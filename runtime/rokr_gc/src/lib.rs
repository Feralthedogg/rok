//! Garbage collector: stop-the-world mark-region (Immix-style blocks
//! and lines, 703 §7.3.1) with opportunistic evacuation: precise in the
//! heap, roots and a few ambiguous words pin what they reach.
//!
//! Small and medium objects (< [`LOS_THRESHOLD`], align <= 8) live in
//! 32 KiB blocks of 128-byte lines carved from one reserved address
//! range. Each thread bump-allocates from its TLAB (702 §7.2.1): a run
//! of free lines in `rok_tls_tlab_cursor..rok_tls_tlab_limit`. Compiled
//! code inlines the bump (809 §8.9.9) and calls [`alloc`] only when the
//! TLAB is exhausted; the refill takes the world lock. A medium object
//! (> one line) that does not fit the TLAB gets its own run of lines.
//! Large objects (LOS, 702 §7.2.9) are one `malloc` each, linked through
//! a hidden [`Prefix`] in front of the header.
//!
//! Every object's `gc_word` (801 §8.1.4) holds its size (8-rounded; its
//! new address while an evacuation runs) and block objects have a nonzero
//! `type_id`, so a block is parsable: memory that is not an object is
//! all zero. The refill zeroes the lines it hands out (outside the
//! world lock; dead objects are not zeroed by the sweep), so the TLAB
//! fast path hands out zeroed memory without a memset.
//!
//! A collection (heap over `max(4 MiB, 2 x live)`, or `rok_gc_collect`)
//! stops every mutator ([`world`]), empties all TLABs, marks from all
//! shadow stacks, then sweeps: live objects mark their lines, dead ones
//! lose their start bit, unmarked lines are free for the next cycle's
//! TLABs. Object lookup uses per-block object-start bitmaps, kept
//! across collections; the lines handed out since the last collection
//! are parsed into them only in blocks a lookup lands in, so a block of
//! young objects that nothing reaches is freed without being read.
//!
//! Generations (sticky mark bits, 703 §7.3.2, on unless
//! `ROK_GC_GEN=0`): a survivor of any collection is old (`STICKY`). A
//! minor collection marks from the roots and the remembered set only,
//! never enters an old object, and sweeps only the lines handed out
//! since the last collection (all young objects live there). An old
//! object also carries `UNLOGGED`; compiled code's write barrier tests
//! that bit before storing a reference into a GC object, and the slow
//! path ([`write_barrier_slow`]) clears it and records the object. A
//! full collection (old bytes over `max(4 MiB, 2 x live after the last
//! full one)`, or `rok_gc_collect`) marks everything and resets the
//! remembered set.
//!
//! An old LOS object is `CARDED` instead: the barrier dirties the
//! 512-byte card of the slot (card table behind the object, pointer in
//! the word before its header) and a minor collection scans only the
//! dirty cards, so a store into a big old buffer costs one card.
//!
//! Evacuation (defragmentation, full collections only): after the
//! sweep, if a quarter of the used blocks' lines are free, every block
//! at most half occupied is a candidate ([`select_candidates`]); its
//! survivors are copied into the holes of the other blocks (then free,
//! then fresh blocks) and leave their new address behind (`FORWARDED`,
//! `gc_word`); one pass over the live heap rewrites every precise
//! reference ([`fix_references`]). An object stays where it is if a
//! root or an ambiguous word reaches it (the mark records those), if it
//! is pinned, or if its address was taken (`NOMOVE`, parking keys).
//! Roots pin because a root word may be an inline `any` payload and
//! because compiled code and runtime calls derive pointers from rooted
//! values (`str` bytes passed to C or a blocking call, element
//! addresses): an object a frame reaches directly never moves. After a
//! full collection the pages of free blocks beyond the next cycle's
//! allocation budget go back to the OS.
//!
//! ponytail: no concurrent marking (705, see TODOS); block objects
//! (< 8 KiB) are remembered whole.
//!
//! Env (read once): `ROK_GC_GEN=0|1`, `ROK_GC_STRESS=N` (every object
//! allocation through the runtime; a collection every `N` of them,
//! every 8th one full), `ROK_GC_EVAC=always|off` (evacuate every block
//! each full collection / never; default: when fragmented),
//! `ROK_GC_STATS=1` (counts, pause times, blocks and bytes moved to
//! stderr at exit).
//!
//! Roots (704 §7.4.1): compiled code links a frame
//! `{ prev, count, slots[count] }` into `rok_tls_shadow_stack_top` on
//! entry and unlinks it on every return; each slot is the *address* of a
//! word that holds a GC reference (0 = none).
//!
//! Children (802): `type_id → ScanTable` registered by
//! [`register_type`] ([`for_each_ref`]): `STRONG_REF` / `INTERIOR_REF`
//! words (a reference, a `str` pointer into an object, or a non-heap
//! address), `ANY_SLOT` (the payload is a reference iff the tag has
//! [`ANY_BOXED`]; else it is the value), and the implementation kind
//! `AMBIGUOUS` (enum union payload words, which may hold anything). A
//! table with the `TABLE_ARRAY` version bit describes one element of a
//! buffer, repeated over its payload. Type id 2 (runtime word buffers)
//! is all ambiguous words. An object whose type was never registered
//! has no traced children. Any reference word (root, interior, or an
//! integer that happens to equal an address) is looked up among the
//! objects; a word outside every object is ignored and an ambiguous one
//! only retains (and pins) the object it hits.

#![cfg_attr(not(test), no_std)]

use core::cell::UnsafeCell;
use core::fmt::Write as _;
use core::mem::size_of;
use core::ptr;
use core::sync::atomic::Ordering;

use rokr_common::fatal;
use rokr_common::object_header::{
    FLAG_CARDED, FLAG_FORWARDED, FLAG_LARGE, FLAG_MARK, FLAG_NOEVAC, FLAG_NOMOVE, FLAG_PINNED,
    FLAG_STICKY, FLAG_UNLOGGED, HEADER_ALIGN, HEADER_SIZE, ObjectHeader,
};

pub mod world;

use rokr_common::gc_abi::{AMBIGUOUS, ANY_SLOT, INTERIOR_REF, STRONG_REF, USER_TYPE_BASE};
pub use rokr_common::gc_abi::{ANY_BOXED, SCAN_WORDS_TYPE_ID};

/// Heap size below which no collection runs.
const MIN_HEAP: usize = 4 << 20;
const TABLE_ARRAY: u16 = rokr_common::gc_abi::TABLE_ARRAY as u16;

/// Immix block / line geometry (703 §7.3.1).
pub const BLOCK_SIZE: usize = 32 << 10;
pub const LINE_SIZE: usize = 128;
const LINES: usize = BLOCK_SIZE / LINE_SIZE;
const GRANULES: usize = BLOCK_SIZE / 8;
/// Objects this large (header included) go to the LOS (702 §7.2.3).
pub const LOS_THRESHOLD: usize = rokr_common::gc_abi::LOS_THRESHOLD as usize;
/// Card size of an old LOS object (`FLAG_CARDED`): a reference store
/// dirties the card(s) of its slot and a minor collection scans only
/// dirty cards, not the whole object.
pub const CARD_SIZE: usize = 1 << rokr_common::gc_abi::CARD_SHIFT;
/// Address space reserved for blocks (committed one block at a time).
// ponytail: a fixed reservation caps the block heap at 64 GiB; chain
// several reservations if a program ever needs more.
const RESERVE: usize = 64 << 30;

/// Line states.
const FREE: u8 = 0;
/// Holds (part of) an object that survived the last collection.
const LIVE: u8 = 1;
/// Handed out (TLAB or medium object) since the last collection.
const TAKEN: u8 = 2;

/// Granules (start bits) per line.
const LINE_GRANULES: usize = LINE_SIZE / 8;

/// Side metadata of one block.
#[allow(clippy::struct_excessive_bools)] // independent per-block states
struct BlockMeta {
    lines: [u8; LINES],
    /// Object starts (one bit per 8-byte granule): `TAKEN` lines are
    /// parsed in by every collection, dead objects cleared by its sweep.
    starts: [u64; GRANULES / 64],
    /// Holds objects or was handed out since the last sweep (else it
    /// is all zero and all `FREE`).
    used: bool,
    /// This collection parsed the `TAKEN` lines (on the first lookup
    /// that landed in one): a block nobody looked into this time holds
    /// no survivor there, so its `TAKEN` lines just become free.
    parsed: bool,
    /// An evacuation candidate of the running full collection.
    evac: bool,
    /// Free, and its pages were given back to the OS (they fault in
    /// zeroed when the block is used again).
    released: bool,
}

/// Hidden bookkeeping right before each LOS object header.
#[repr(C)]
struct Prefix {
    /// Header of the next LOS object.
    next: *mut u8,
    /// Total object size, header included.
    size: usize,
    /// Bytes from the `malloc` base to the header.
    offset: usize,
    /// Card table (one byte per [`CARD_SIZE`] of the object, after its
    /// end in the same `malloc` block). Last field: compiled code's
    /// barrier loads it from the word before the header.
    cards: *mut u8,
}

struct Heap {
    /// Bytes of objects alive after the last collection plus everything
    /// handed out since (TLABs count in full).
    live_bytes: usize,
    next_gc: usize,
    collections: u64,
    /// Bytes alive after the last collection (all old when generational).
    old_bytes: usize,
    /// Generational: the next automatic collection is full once
    /// `old_bytes` reaches this.
    full_at: usize,
    minors: u64,
    /// Total / longest pause (`ROK_GC_STATS`).
    gc_ns: u64,
    max_ns: u64,
    /// Collector-thread CPU time in pauses (robust on a loaded machine).
    gc_cpu_ns: u64,
    /// `ROK_GC_*` read (first slow-path allocation or collection).
    configured: bool,
    generational: bool,
    /// `ROK_GC_STRESS`: collect every `stress` runtime allocations (0 =
    /// off); `allocs` counts them.
    stress: u64,
    allocs: u64,
    /// `scan_tables[type_id - USER_TYPE_BASE]`, null = unregistered.
    scan_tables: *mut *const u8,
    scan_len: usize,
    /// Mark stack (grown with `realloc`).
    stack: *mut *mut u8,
    stack_cap: usize,
    /// Block `i` is at `base + i * BLOCK_SIZE`; 0 until the first one.
    base: usize,
    nblocks: usize,
    meta: *mut BlockMeta,
    meta_cap: usize,
    /// Next line (global index `block * LINES + line`) the small / medium
    /// refill looks at; both restart at 0 after every sweep.
    small_cursor: usize,
    medium_cursor: usize,
    /// LOS objects, linked through their prefixes.
    los: *mut u8,
    los_count: usize,
    /// Sorted LOS addresses, rebuilt by every collection.
    index: *mut usize,
    index_cap: usize,
    /// `ROK_GC_EVAC`: [`EVAC_OFF`], [`EVAC_AUTO`] or [`EVAC_ALWAYS`].
    evac_mode: u8,
    /// This (full) collection may evacuate: the mark records `pinned`.
    evacuating: bool,
    /// Block objects a root or an ambiguous word reaches (repeats
    /// allowed): an evacuation leaves them in place.
    pinned: *mut usize,
    pinned_len: usize,
    pinned_cap: usize,
    /// Copy allocator of an evacuation: bump `copy_cursor..copy_limit`
    /// (free lines of a non-candidate block); `copy_line` is the next
    /// global line index it looks at.
    copy_cursor: usize,
    copy_limit: usize,
    copy_line: usize,
    /// 0: holes of used blocks, 1: free blocks, 2: fresh blocks.
    copy_phase: u8,
    /// Fresh blocks the copy allocator may still commit (unbounded for
    /// `ROK_GC_EVAC=always`).
    fresh_blocks: usize,
    /// `ROK_GC_STATS`: evacuating collections, bytes moved.
    evacuations: u64,
    moved_bytes: u64,
}

/// `ROK_GC_EVAC` modes.
const EVAC_OFF: u8 = 0;
const EVAC_AUTO: u8 = 1;
/// Every full collection evacuates every block it may (tests).
const EVAC_ALWAYS: u8 = 2;

struct Global(UnsafeCell<Heap>);
// SAFETY: only touched with the world lock held (see module docs).
unsafe impl Sync for Global {}

static HEAP: Global = Global(UnsafeCell::new(Heap {
    live_bytes: 0,
    next_gc: MIN_HEAP,
    collections: 0,
    old_bytes: 0,
    full_at: MIN_HEAP,
    minors: 0,
    gc_ns: 0,
    max_ns: 0,
    gc_cpu_ns: 0,
    configured: false,
    generational: true,
    stress: 0,
    allocs: 0,
    scan_tables: ptr::null_mut(),
    scan_len: 0,
    stack: ptr::null_mut(),
    stack_cap: 0,
    base: 0,
    nblocks: 0,
    meta: ptr::null_mut(),
    meta_cap: 0,
    small_cursor: 0,
    medium_cursor: 0,
    los: ptr::null_mut(),
    los_count: 0,
    index: ptr::null_mut(),
    index_cap: 0,
    evac_mode: EVAC_AUTO,
    evacuating: false,
    pinned: ptr::null_mut(),
    pinned_len: 0,
    pinned_cap: 0,
    copy_cursor: 0,
    copy_limit: 0,
    copy_line: 0,
    copy_phase: 0,
    fresh_blocks: 0,
    evacuations: 0,
    moved_bytes: 0,
}));

fn heap() -> &'static mut Heap {
    // SAFETY: callers hold the world lock; no caller keeps the reference
    // across another `heap()` call.
    unsafe { &mut *HEAP.0.get() }
}

const fn prefix(obj: *mut u8) -> *mut Prefix {
    obj.wrapping_sub(size_of::<Prefix>()).cast()
}

const fn header(obj: *mut u8) -> *mut ObjectHeader {
    obj.cast()
}

/// Size of the object at `obj` (its `gc_word`; not of an evacuated
/// one, see [`moved_size`]).
fn obj_size(obj: *mut u8) -> usize {
    // SAFETY: callers pass object headers (or zeroed block memory, which
    // reads as 0).
    unsafe { (*header(obj)).gc_word as usize }
}

/// [`obj_size`] that also reads an evacuated object's (its copy's).
fn moved_size(obj: *mut u8) -> usize {
    // SAFETY: an object header; a forwarded one's `gc_word` is its copy.
    unsafe {
        let h = &*header(obj);
        if h.gc_flags.load(Ordering::Relaxed) & FLAG_FORWARDED != 0 {
            return obj_size(h.gc_word as *mut u8);
        }
        h.gc_word as usize
    }
}

/// Write a fresh header with `size` in `gc_word` into zeroed memory.
fn init_header(obj: *mut u8, type_id: u32, size: usize, flags: u32) {
    // SAFETY: `obj` is 8-aligned memory of at least `size` bytes we own.
    unsafe {
        ObjectHeader::init(obj, type_id);
        (*header(obj)).gc_word = size as u64;
        (*header(obj)).gc_flags.store(flags, Ordering::Relaxed);
    }
}

/// Allocate a zeroed GC object of `size` bytes (header included) and
/// initialize its header (`rok_gc_alloc_slow`). May collect first.
/// Never null.
pub fn alloc(size: usize, align: usize, type_id: u32) -> *mut u8 {
    if size < HEADER_SIZE {
        fatal(b"rok_gc_alloc_slow: size smaller than the object header");
    }
    if !align.is_power_of_two() {
        fatal(b"rok runtime: allocation align is not a power of two");
    }
    let Some(size8) = size.checked_next_multiple_of(8) else {
        fatal(b"rok runtime: allocation size overflow");
    };
    // Type id 0 (invalid, 801 §8.1.2) would read as free memory in a
    // block.
    if size8 >= LOS_THRESHOLD || align > HEADER_ALIGN || type_id == 0 {
        return alloc_large(size, align, type_id);
    }
    let [cursor, limit] = rokr_common::tls::tlab();
    // SAFETY: this thread's own TLAB slots; `cursor..limit` is zeroed
    // block memory nobody else allocates from.
    unsafe {
        let c = cursor.read();
        if c != 0 && size8 <= limit.read() - c {
            cursor.write(c + size8);
            let obj = c as *mut u8;
            init_header(obj, type_id, size8, 0);
            return obj;
        }
    }
    world::lock();
    before_alloc(if size8 > LINE_SIZE { size8 } else { LINE_SIZE });
    // `obj..lines_end`: the lines just taken, zeroed below (free lines
    // keep their dead objects' bytes until reused).
    let (obj, lines_end) = if size8 > LINE_SIZE {
        // A medium object that does not fit the TLAB: its own lines, so
        // the TLAB's tail stays usable.
        let lines = size8.div_ceil(LINE_SIZE);
        let obj = take_run(lines, true);
        heap().live_bytes += size8;
        (obj, obj as usize + lines * LINE_SIZE)
    } else {
        let start = take_run(1, false);
        let line_end = (start as usize + 1).next_multiple_of(LINE_SIZE);
        let (end, lines_end) = if heap().stress == 0 {
            let end = end_of_run(start as usize, line_end);
            (end, end)
        } else {
            // Stress: a TLAB of exactly this object, so the next
            // allocation comes back here too.
            (start as usize + size8, line_end)
        };
        heap().live_bytes += end - start as usize;
        // SAFETY: this thread's own TLAB slots.
        unsafe {
            cursor.write(start as usize + size8);
            limit.write(end);
        }
        (start, lines_end)
    };
    world::unlock();
    // SAFETY: the lines are `TAKEN` for us; outside the lock, which no
    // collection can need before this thread's next safepoint.
    unsafe { ptr::write_bytes(obj, 0, lines_end - obj as usize) };
    init_header(obj, type_id, size8, 0);
    obj
}

/// With the lock held, before handing out `want` more bytes: collect
/// if the heap outgrew its budget or `ROK_GC_STRESS` says so.
fn before_alloc(want: usize) {
    let h = heap();
    configure(h);
    h.allocs += 1;
    let stressed = h.stress != 0 && h.allocs % h.stress == 0;
    if stressed || h.live_bytes.saturating_add(want) > h.next_gc {
        let full = !h.generational
            || h.old_bytes >= h.full_at
            || (stressed && (h.allocs / h.stress) % 8 == 0);
        collect_locked(full);
    }
}

/// Read `ROK_GC_GEN` / `ROK_GC_STRESS` / `ROK_GC_STATS` once (before
/// the first collection, so no object is old yet).
fn configure(h: &mut Heap) {
    if h.configured {
        return;
    }
    h.configured = true;
    h.generational = env_num(c"ROK_GC_GEN").is_none_or(|v| v != 0);
    h.stress = env_num(c"ROK_GC_STRESS").unwrap_or(0);
    // SAFETY: `getenv` result is null or NUL-terminated.
    h.evac_mode = match unsafe { libc::getenv(c"ROK_GC_EVAC".as_ptr()) } {
        p if p.is_null() => EVAC_AUTO,
        // SAFETY: as above.
        p => match unsafe { core::ffi::CStr::from_ptr(p) }.to_bytes() {
            b"always" => EVAC_ALWAYS,
            b"off" | b"0" => EVAC_OFF,
            _ => EVAC_AUTO,
        },
    };
    if env_num(c"ROK_GC_STATS").is_some_and(|v| v != 0) {
        // SAFETY: registering a plain `extern "C" fn()`.
        unsafe { libc::atexit(print_stats) };
    }
}

/// Decimal value of env var `name` (`Some(0)` if set but not a number).
fn env_num(name: &core::ffi::CStr) -> Option<u64> {
    // SAFETY: `name` is NUL-terminated; getenv's result is NUL-terminated.
    unsafe {
        let mut p = libc::getenv(name.as_ptr()).cast::<u8>().cast_const();
        if p.is_null() {
            return None;
        }
        let mut n = 0u64;
        while (*p).is_ascii_digit() {
            n = n.saturating_mul(10).saturating_add(u64::from(*p - b'0'));
            p = p.add(1);
        }
        Some(n)
    }
}

extern "C" fn print_stats() {
    struct Stderr;
    impl core::fmt::Write for Stderr {
        fn write_str(&mut self, s: &str) -> core::fmt::Result {
            // SAFETY: `s` is valid for its own length.
            unsafe { rokr_common::write_stderr(s.as_ptr(), s.len()) };
            Ok(())
        }
    }
    world::lock();
    let h = heap();
    let _ = writeln!(
        Stderr,
        "rok gc: {} collections ({} minor), {}.{:03} ms total pause, max {}.{:03} ms, {}.{:03} ms cpu, {} KiB live",
        h.collections,
        h.minors,
        h.gc_ns / 1_000_000,
        h.gc_ns / 1000 % 1000,
        h.max_ns / 1_000_000,
        h.max_ns / 1000 % 1000,
        h.gc_cpu_ns / 1_000_000,
        h.gc_cpu_ns / 1000 % 1000,
        h.old_bytes >> 10
    );
    // SAFETY: `nblocks` initialized metas.
    let metas = unsafe { core::slice::from_raw_parts(h.meta, h.nblocks) };
    let released = metas.iter().filter(|m| m.released).count();
    let _ = writeln!(
        Stderr,
        "rok gc: {} blocks ({} KiB resident), {} evacuations moved {} KiB",
        h.nblocks,
        ((h.nblocks - released) * BLOCK_SIZE) >> 10,
        h.evacuations,
        h.moved_bytes >> 10
    );
    world::unlock();
}

fn now_ns() -> u64 {
    clock_ns(libc::CLOCK_MONOTONIC)
}

fn clock_ns(clock: libc::clockid_t) -> u64 {
    let mut ts = libc::timespec {
        tv_sec: 0,
        tv_nsec: 0,
    };
    // SAFETY: valid out-pointer.
    unsafe { libc::clock_gettime(clock, &mut ts) };
    ts.tv_sec as u64 * 1_000_000_000 + ts.tv_nsec as u64
}

/// With the lock held: `lines` free lines (exactly, if `exact`; else
/// the first line of a free run, whose remaining free lines
/// [`end_of_run`] claims) in one block, marked `TAKEN`. Commits a new
/// block when no used one has room.
fn take_run(lines: usize, exact: bool) -> *mut u8 {
    let h = heap();
    let cursor = if exact {
        h.medium_cursor
    } else {
        h.small_cursor
    };
    let mut at = cursor;
    while at < h.nblocks * LINES {
        let (blk, line) = (at / LINES, at % LINES);
        // SAFETY: `blk < nblocks`.
        let meta = unsafe { &mut *h.meta.add(blk) };
        if meta.lines[line] != FREE {
            at += 1;
            continue;
        }
        let mut run = 1;
        while line + run < LINES && run < lines && meta.lines[line + run] == FREE {
            run += 1;
        }
        if run < lines {
            at += run;
            continue;
        }
        meta.lines[line..line + run].fill(TAKEN);
        meta.used = true;
        meta.released = false;
        if exact {
            h.medium_cursor = at + run;
        } else {
            h.small_cursor = at + run;
        }
        return (h.base + at * LINE_SIZE) as *mut u8;
    }
    let b = new_block();
    let h = heap();
    // SAFETY: `b` was just committed.
    let m = unsafe { &mut *h.meta.add(b) };
    m.lines[..lines].fill(TAKEN);
    m.used = true;
    m.released = false;
    if exact {
        h.medium_cursor = b * LINES + lines;
    }
    (h.base + b * BLOCK_SIZE) as *mut u8
}

/// With the lock held: extend a small run that starts at `start` (its
/// first line already `TAKEN`, ending at `end`) over the following free
/// lines of its block; the run's end address.
fn end_of_run(start: usize, mut end: usize) -> usize {
    let h = heap();
    let b = (start - h.base) / BLOCK_SIZE;
    // SAFETY: `start` is in block `b < nblocks`.
    let m = unsafe { &mut *h.meta.add(b) };
    let mut l = (end - h.base) / LINE_SIZE - b * LINES;
    while l < LINES && m.lines[l] == FREE {
        m.lines[l] = TAKEN;
        l += 1;
        end += LINE_SIZE;
    }
    h.small_cursor = h.small_cursor.max(b * LINES + l);
    end
}

/// With the lock held: commit one more (zeroed) block; its index.
fn new_block() -> usize {
    let h = heap();
    if h.base == 0 {
        // SAFETY: an anonymous PROT_NONE reservation; nothing is touched
        // until `mprotect` commits it.
        let p = unsafe {
            libc::mmap(
                ptr::null_mut(),
                RESERVE + BLOCK_SIZE,
                libc::PROT_NONE,
                libc::MAP_PRIVATE | libc::MAP_ANON,
                -1,
                0,
            )
        };
        if p == libc::MAP_FAILED {
            rokr_common::oom();
        }
        h.base = (p as usize).next_multiple_of(BLOCK_SIZE);
    }
    if h.nblocks == RESERVE / BLOCK_SIZE {
        rokr_common::oom();
    }
    let b = h.nblocks;
    // SAFETY: block `b` lies inside our reservation.
    let rc = unsafe {
        libc::mprotect(
            (h.base + b * BLOCK_SIZE) as *mut libc::c_void,
            BLOCK_SIZE,
            libc::PROT_READ | libc::PROT_WRITE,
        )
    };
    if rc != 0 {
        rokr_common::oom();
    }
    if b == h.meta_cap {
        let cap = (h.meta_cap * 2).max(64);
        // SAFETY: realloc of our own table (or null).
        let p = unsafe { libc::realloc(h.meta.cast(), cap * size_of::<BlockMeta>()) };
        if p.is_null() {
            rokr_common::oom();
        }
        h.meta = p.cast();
        h.meta_cap = cap;
    }
    // SAFETY: `b < meta_cap`.
    unsafe {
        h.meta.add(b).write(BlockMeta {
            lines: [FREE; LINES],
            starts: [0; GRANULES / 64],
            used: false,
            parsed: false,
            evac: false,
            released: false,
        });
    }
    h.nblocks += 1;
    b
}

/// A large (or over-aligned) object: its own zeroed `malloc` block.
fn alloc_large(size: usize, align: usize, type_id: u32) -> *mut u8 {
    let align = align.max(HEADER_ALIGN);
    let offset = size_of::<Prefix>().next_multiple_of(align);
    let Some(total) = size
        .checked_add(offset)
        .and_then(|t| t.checked_add(size.div_ceil(CARD_SIZE)))
    else {
        fatal(b"rok runtime: allocation size overflow");
    };
    // SAFETY: plain allocation calls; `align` is a power of two >= 8.
    let base = unsafe {
        if align <= 16 {
            libc::calloc(1, total)
        } else {
            let mut p: *mut libc::c_void = ptr::null_mut();
            if libc::posix_memalign(&mut p, align, total) != 0 {
                p = ptr::null_mut();
            } else {
                ptr::write_bytes(p.cast::<u8>(), 0, total);
            }
            p
        }
    };
    if base.is_null() {
        rokr_common::oom();
    }
    world::lock();
    // The new block is not on the list yet, so a collection here cannot
    // free it.
    before_alloc(size);
    let h = heap();
    // SAFETY: `base..base+total` is ours; `obj` is `align`-aligned and the
    // prefix fits in the `offset` bytes before it.
    let obj = unsafe {
        let obj = base.cast::<u8>().add(offset);
        prefix(obj).write(Prefix {
            next: h.los,
            size,
            offset,
            cards: obj.add(size),
        });
        init_header(obj, type_id, size, FLAG_LARGE);
        h.los = obj;
        h.los_count += 1;
        h.live_bytes += size;
        obj
    };
    world::unlock();
    obj
}

/// Register the 802 `ScanTable` for `type_id`. Ids below the user range
/// are not used by the compiler yet and are ignored.
pub fn register_type(type_id: u32, table: *const u8) {
    let Some(i) = type_id.checked_sub(USER_TYPE_BASE) else {
        return;
    };
    let i = i as usize;
    world::lock();
    let h = heap();
    if i >= h.scan_len {
        let len = (i + 1).next_power_of_two().max(64);
        // SAFETY: realloc of our own table (or null); new tail zeroed.
        unsafe {
            let p = libc::realloc(h.scan_tables.cast(), len * size_of::<*const u8>())
                .cast::<*const u8>();
            if p.is_null() {
                rokr_common::oom();
            }
            ptr::write_bytes(p.add(h.scan_len), 0, len - h.scan_len);
            h.scan_tables = p;
            h.scan_len = len;
        }
    }
    // SAFETY: `i < scan_len`.
    unsafe { *h.scan_tables.add(i) = table };
    world::unlock();
}

fn scan_table(type_id: u32) -> *const u8 {
    let h = heap();
    match type_id.checked_sub(USER_TYPE_BASE) {
        // SAFETY: bounds-checked index into our table.
        Some(i) if (i as usize) < h.scan_len => unsafe { *h.scan_tables.add(i as usize) },
        _ => ptr::null(),
    }
}

/// Set the start bits of every object in the `TAKEN` lines of the block
/// at `block` by parsing them: an object has a nonzero `type_id` (0 is
/// reserved, 801 §8.1.2) and its size in `gc_word`; everything else is
/// zero. A run of `TAKEN` lines was all free when handed out, so no
/// object crosses its ends.
fn parse_taken(block: usize, m: &mut BlockMeta) {
    let mut l = 0;
    while l < LINES {
        if m.lines[l] != TAKEN {
            l += 1;
            continue;
        }
        let mut end = l + 1;
        while end < LINES && m.lines[end] == TAKEN {
            end += 1;
        }
        let mut off = l * LINE_SIZE;
        while off < end * LINE_SIZE {
            let obj = (block + off) as *mut u8;
            // SAFETY: `off` is inside the run: an object header or zeroes.
            if unsafe { (*header(obj)).type_id } == 0 {
                off += 8;
            } else {
                m.starts[off / 8 / 64] |= 1 << (off / 8 % 64);
                off += obj_size(obj);
            }
        }
        l = end;
    }
}

/// `f(offset)` for every object start in the lines of `lines` that are
/// `TAKEN` (all lines if `all`), from the start bitmap `starts`.
fn for_each_start(
    lines: &[u8; LINES],
    starts: &[u64; GRANULES / 64],
    all: bool,
    mut f: impl FnMut(usize),
) {
    const PER_WORD: usize = 64 / LINE_GRANULES;
    for (w, &word) in starts.iter().enumerate() {
        let mut bits = word;
        if !all {
            for k in 0..PER_WORD {
                if lines[w * PER_WORD + k] != TAKEN {
                    bits &= !(((1u64 << LINE_GRANULES) - 1) << (k * LINE_GRANULES));
                }
            }
        }
        while bits != 0 {
            f((w * 64 + bits.trailing_zeros() as usize) * 8);
            bits &= bits - 1;
        }
    }
}

/// Before marking: the sorted LOS index. (Block start bits of the lines
/// handed out since the last collection are parsed lazily, by
/// [`object_containing`].)
fn build_index() {
    let h = heap();
    if h.los_count == 0 {
        return;
    }
    if h.index_cap < h.los_count {
        let cap = h.los_count.next_power_of_two();
        // SAFETY: realloc of our own buffer (or null).
        let p = unsafe { libc::realloc(h.index.cast(), cap * size_of::<usize>()) };
        if p.is_null() {
            rokr_common::oom();
        }
        h.index = p.cast();
        h.index_cap = cap;
    }
    // SAFETY: the list holds exactly `los_count` objects; `index` has
    // room.
    unsafe {
        let mut o = h.los;
        for i in 0..h.los_count {
            *h.index.add(i) = o as usize;
            o = (*prefix(o)).next;
        }
        core::slice::from_raw_parts_mut(h.index, h.los_count).sort_unstable();
    }
}

/// Pinned objects (`rok_gc_pin`, `FLAG_PINNED`): roots until unpinned.
/// A list, so a collection does not visit every header looking for the
/// flag.
// ponytail: spin lock + linear unpin; pins are few (deque setup, the
// running executor, the parking registry).
struct Pins {
    lock: core::sync::atomic::AtomicBool,
    list: UnsafeCell<(*mut *mut u8, usize, usize)>,
}

// SAFETY: `list` is only touched under `lock` (or with the world
// stopped, when no thread is inside `pin` / `unpin`).
unsafe impl Sync for Pins {}

static PINS: Pins = Pins {
    lock: core::sync::atomic::AtomicBool::new(false),
    list: UnsafeCell::new((ptr::null_mut(), 0, 0)),
};

fn with_pins<R>(f: impl FnOnce(&mut (*mut *mut u8, usize, usize)) -> R) -> R {
    while PINS
        .lock
        .compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed)
        .is_err()
    {
        core::hint::spin_loop();
    }
    // SAFETY: we hold the lock.
    let r = f(unsafe { &mut *PINS.list.get() });
    PINS.lock.store(false, Ordering::Release);
    r
}

/// Keep `obj` (and what it references) alive until [`unpin`]. Not a
/// safepoint.
///
/// # Safety
/// `obj` must be a live GC object.
pub unsafe fn pin(obj: *mut u8) {
    // SAFETY: caller contract.
    let flags = unsafe { &(*header(obj)).gc_flags };
    if flags.fetch_or(FLAG_PINNED, Ordering::Relaxed) & FLAG_PINNED != 0 {
        return;
    }
    with_pins(|(objs, len, cap)| {
        if *len == *cap {
            *cap = (*cap * 2).max(16);
            // SAFETY: realloc of our own list (or null).
            *objs = unsafe { libc::realloc(objs.cast(), *cap * size_of::<*mut u8>()) }.cast();
            if objs.is_null() {
                rokr_common::oom();
            }
        }
        // SAFETY: `len < cap`.
        unsafe { *objs.add(*len) = obj };
        *len += 1;
    });
}

/// Undo [`pin`].
///
/// # Safety
/// `obj` must be a live GC object.
pub unsafe fn unpin(obj: *mut u8) {
    // SAFETY: caller contract.
    let flags = unsafe { &(*header(obj)).gc_flags };
    if flags.fetch_and(!FLAG_PINNED, Ordering::Relaxed) & FLAG_PINNED == 0 {
        return;
    }
    with_pins(|(objs, len, _)| {
        // SAFETY: the first `len` entries are initialized.
        let list = unsafe { core::slice::from_raw_parts_mut(*objs, *len) };
        if let Some(i) = list.iter().position(|&o| o == obj) {
            list.swap(i, *len - 1);
            *len -= 1;
        }
    });
}

/// Never move `obj` again (its address became a number: a parking key).
/// It still dies when unreachable.
///
/// # Safety
/// `obj` must be a live GC object.
pub unsafe fn no_move(obj: *mut u8) {
    // SAFETY: caller contract.
    unsafe {
        (*header(obj))
            .gc_flags
            .fetch_or(FLAG_NOMOVE, Ordering::Relaxed)
    };
}

/// The object whose header address is `word` or whose memory contains
/// it (a `str` points at its payload bytes, or into them after slicing).
/// `young`: block objects outside `TAKEN` lines (old ones) are `None`,
/// decided from the line table without touching the object.
fn object_containing(word: usize, young: bool) -> Option<*mut u8> {
    object_in::<false>(word, young)
}

/// [`object_containing`]; `MOVED`: objects may be evacuated already.
fn object_in<const MOVED: bool>(word: usize, young: bool) -> Option<*mut u8> {
    let size_of = |o: *mut u8| if MOVED { moved_size(o) } else { obj_size(o) };
    let h = heap();
    if word >= h.base && word < h.base + h.nblocks * BLOCK_SIZE {
        let blk = (word - h.base) / BLOCK_SIZE;
        // SAFETY: `blk < nblocks`.
        let meta = unsafe { &mut *h.meta.add(blk) };
        let block = h.base + blk * BLOCK_SIZE;
        let line = meta.lines[(word - block) / LINE_SIZE];
        if !meta.used || (young && line != TAKEN) {
            return None;
        }
        if line == TAKEN && !meta.parsed {
            parse_taken(block, meta);
            meta.parsed = true;
        }
        let granule = (word - block) / 8;
        // The nearest object start at or before `granule`: objects are
        // smaller than `LOS_THRESHOLD`, so only that many granules back.
        let lowest = granule.saturating_sub(LOS_THRESHOLD / 8);
        let mut i = granule / 64;
        let mut bits = meta.starts[i] & (u64::MAX >> (63 - granule % 64));
        loop {
            if bits != 0 {
                let start = block + (i * 64 + 63 - bits.leading_zeros() as usize) * 8;
                let size = size_of(start as *mut u8);
                return (word < start + size).then_some(start as *mut u8);
            }
            if i == 0 || (i - 1) * 64 + 63 < lowest {
                return None;
            }
            i -= 1;
            bits = meta.starts[i];
        }
    }
    if h.los_count == 0 {
        return None;
    }
    // SAFETY: `build_index` filled `los_count` entries.
    let index = unsafe { core::slice::from_raw_parts(h.index, h.los_count) };
    let i = match index.binary_search(&word) {
        Ok(i) => i,
        Err(0) => return None,
        Err(i) => i - 1,
    };
    let start = index[i];
    (word < start + size_of(start as *mut u8)).then_some(start as *mut u8)
}

/// Queue the object `word` points into, if any (and young, unless
/// `full`), for marking. `pin`: `word` is a root or ambiguous, so the
/// object must not move.
fn push(word: usize, full: bool, len: &mut usize, pin: bool) {
    let Some(obj) = object_containing(word, !full) else {
        return;
    };
    let h = heap();
    if pin && h.evacuating && (obj as usize) < h.base + h.nblocks * BLOCK_SIZE {
        if h.pinned_len == h.pinned_cap {
            let cap = (h.pinned_cap * 2).max(1024);
            // SAFETY: realloc of our own buffer (or null).
            let p = unsafe { libc::realloc(h.pinned.cast(), cap * size_of::<usize>()) };
            if p.is_null() {
                rokr_common::oom();
            }
            h.pinned = p.cast();
            h.pinned_cap = cap;
        }
        // SAFETY: `pinned_len < pinned_cap`.
        unsafe { *h.pinned.add(h.pinned_len) = obj as usize };
        h.pinned_len += 1;
    }
    push_obj(obj, len);
}

/// `addr` lies in an evacuation candidate block.
fn in_candidate(addr: usize) -> bool {
    let h = heap();
    // SAFETY: bounds-checked block index.
    addr >= h.base
        && addr < h.base + h.nblocks * BLOCK_SIZE
        && unsafe { (*h.meta.add((addr - h.base) / BLOCK_SIZE)).evac }
}

fn push_obj(obj: *mut u8, len: &mut usize) {
    let h = heap();
    if *len == h.stack_cap {
        let cap = (h.stack_cap * 2).max(1024);
        // SAFETY: realloc of our own stack (or null).
        let p = unsafe { libc::realloc(h.stack.cast(), cap * size_of::<*mut u8>()) };
        if p.is_null() {
            rokr_common::oom();
        }
        h.stack = p.cast();
        h.stack_cap = cap;
    }
    // SAFETY: `*len < stack_cap`.
    unsafe { *h.stack.add(*len) = obj };
    *len += 1;
}

/// Queue the referents of `o`'s reference words.
// The mark loop's hot path: a plain (non-array) table read inline, the
// general `for_each_ref` otherwise.
#[allow(clippy::cast_ptr_alignment)] // tables are 4-aligned, payloads 8
fn scan_children(o: *mut u8, full: bool, len: &mut usize) {
    // SAFETY: `o` is a live GC object; its ScanTable (802) describes it.
    unsafe {
        let type_id = (*header(o)).type_id;
        let t = if type_id == SCAN_WORDS_TYPE_ID {
            ptr::null()
        } else {
            scan_table(type_id)
        };
        if t.is_null() || t.add(4).cast::<u16>().read_unaligned() & TABLE_ARRAY != 0 {
            scan_range(o, 0, usize::MAX, full, len);
            return;
        }
        let n = t.add(6).cast::<u16>().read_unaligned() as usize;
        for e in 0..n {
            let entry = t.add(8 + 8 * e).cast::<u32>();
            let mut off = entry.read_unaligned() as usize;
            let precise = match entry.add(1).read_unaligned() {
                STRONG_REF | INTERIOR_REF => true,
                ANY_SLOT => {
                    if o.add(off).cast::<u32>().read() & ANY_BOXED == 0 {
                        continue;
                    }
                    off += size_of::<usize>();
                    true
                }
                AMBIGUOUS => false,
                _ => continue,
            };
            push(
                o.add(off).cast::<usize>().read_unaligned(),
                full,
                len,
                !precise,
            );
        }
    }
}

/// Queue the referents of `o`'s reference words at byte offsets
/// `lo..hi` (from the header).
fn scan_range(o: *mut u8, lo: usize, hi: usize, full: bool, len: &mut usize) {
    for_each_ref(o, lo, hi, |off, precise| {
        // SAFETY: `off` is a word inside the live object `o`.
        let word = unsafe { o.add(off).cast::<usize>().read_unaligned() };
        push(word, full, len, !precise);
    });
}

/// `f(offset, precise)` for every word of the live object `o` at byte
/// offsets `lo..hi` (from the header) that may hold a reference, per
/// its `ScanTable` (802). A `precise` word holds a reference or an
/// address outside the heap; an ambiguous one may hold anything. An
/// `ANY_SLOT` yields its payload word only when the tag says it is a
/// box. An object whose type was never registered has none.
#[allow(clippy::cast_ptr_alignment)] // tables are 4-aligned, payloads 8
fn for_each_ref(o: *mut u8, lo: usize, hi: usize, mut f: impl FnMut(usize, bool)) {
    // SAFETY: `o` is a live GC object; its ScanTable (802) describes it.
    unsafe {
        let hd = &*header(o);
        if hd.type_id == SCAN_WORDS_TYPE_ID {
            let hi = hi.min(obj_size(o)) & !7;
            let mut off = lo.max(HEADER_SIZE).next_multiple_of(8);
            while off < hi {
                f(off, false);
                off += 8;
            }
            return;
        }
        let t = scan_table(hd.type_id);
        if t.is_null() {
            return;
        }
        let version = t.add(4).cast::<u16>().read_unaligned();
        let n = t.add(6).cast::<u16>().read_unaligned() as usize;
        if n == 0 {
            return;
        }
        let entries = core::slice::from_raw_parts(t.add(8).cast::<[u32; 2]>(), n);
        if version & TABLE_ARRAY == 0 {
            if lo == 0 && hi == usize::MAX {
                visit_entries(o, entries, 0, &mut f);
            } else {
                visit_entries(o, entries, 0, &mut |off, p| {
                    if (lo..hi).contains(&off) {
                        f(off, p);
                    }
                });
            }
            return;
        }
        // An array table repeats its entries every `stride` bytes after
        // the header: visit the elements that overlap `lo..hi` (an `any`
        // counts by its payload word).
        let stride = t.cast::<u32>().read_unaligned() as usize;
        let count = (obj_size(o) - HEADER_SIZE) / stride;
        let first = lo.saturating_sub(HEADER_SIZE + size_of::<usize>()) / stride;
        let last = hi.saturating_sub(HEADER_SIZE).div_ceil(stride).min(count);
        for i in first..last {
            visit_entries(o, entries, HEADER_SIZE + i * stride, &mut |off, p| {
                if (lo..hi).contains(&off) {
                    f(off, p);
                }
            });
        }
    }
}

/// [`for_each_ref`] over the `entries` of one table at byte offset `at`.
#[inline]
#[allow(clippy::cast_ptr_alignment)] // the tag is 4-aligned
fn visit_entries(o: *mut u8, entries: &[[u32; 2]], at: usize, f: &mut impl FnMut(usize, bool)) {
    for &[eo, kind] in entries {
        let off = at + eo as usize;
        match kind {
            STRONG_REF | INTERIOR_REF => f(off, true),
            // SAFETY: the tag word of an `any` inside the live `o`.
            ANY_SLOT if unsafe { o.add(off).cast::<u32>().read() } & ANY_BOXED != 0 => {
                f(off + size_of::<usize>(), true);
            }
            AMBIGUOUS => f(off, false),
            _ => {}
        }
    }
}

/// Full stop-the-world collection (`rok_gc_collect`).
pub fn collect() {
    world::lock();
    configure(heap());
    collect_locked(true);
    world::unlock();
}

/// A minor collection if generational, else a full one
/// (`rok_gc_collect_young`, tests).
pub fn collect_young() {
    world::lock();
    let h = heap();
    configure(h);
    collect_locked(!h.generational);
    world::unlock();
}

/// With the world lock held: stop every other mutator, mark from all
/// registered threads' shadow stacks, pinned / immortal objects and
/// (minor) the remembered set, sweep, resume.
fn collect_locked(full: bool) {
    let t0 = now_ns();
    let c0 = clock_ns(libc::CLOCK_THREAD_CPUTIME_ID);
    world::stop();
    world::reset_tlabs();
    let mut len = 0;
    build_index();
    let h = heap();
    h.evacuating = full && h.evac_mode != EVAC_OFF;
    // SAFETY: the world is stopped: nobody is inside `pin` / `unpin`.
    let (pins, npins, _) = unsafe { *PINS.list.get() };
    for i in 0..npins {
        // Through the lookup, so a young one's block gets parsed.
        // SAFETY: `i < npins`.
        push(unsafe { *pins.add(i) } as usize, full, &mut len, true);
    }
    // Roots pin their referents: a root word may be an inline `any`
    // payload, and compiled code / runtime calls derive pointers from
    // rooted values (`str` bytes handed to C, element addresses), so an
    // object a frame reaches directly never moves.
    world::for_each_root(|word| push(word as usize, full, &mut len, true));
    // Nobody logs while the world is stopped (the barrier has no
    // safepoint): every thread's chunk joins the retired ones.
    world::for_each_wb_log(retire_log);
    let log = LOG_FULL.swap(ptr::null_mut(), Ordering::Acquire);
    if !full {
        for_each_logged(log, |o| scan_children(o, false, &mut len));
        scan_dirty_cards(&mut len);
    }
    while len > 0 {
        len -= 1;
        // SAFETY: `push` only queues addresses of live GC objects.
        let o = unsafe { *heap().stack.add(len) };
        // SAFETY: as above.
        let flags = unsafe { &(*header(o)).gc_flags };
        // A minor collection never enters an old object: whatever young
        // object it references is in the remembered set's reach.
        if (!full && flags.load(Ordering::Relaxed) & FLAG_STICKY != 0)
            || flags.fetch_or(FLAG_MARK, Ordering::Relaxed) & FLAG_MARK != 0
        {
            continue;
        }
        scan_children(o, full, &mut len);
    }
    if !full {
        // The logged (old) objects all survive: unlogged again.
        for_each_logged(log, |o| {
            // SAFETY: logged objects are live.
            unsafe {
                (*header(o))
                    .gc_flags
                    .fetch_or(FLAG_UNLOGGED, Ordering::Relaxed)
            };
        });
    }
    free_logs(log);
    let survived = sweep_blocks(full) + sweep_los(full);
    if heap().evacuating {
        if select_candidates() {
            evacuate();
        }
        let h = heap();
        h.evacuating = false;
        h.pinned_len = 0;
    }
    let h = heap();
    let live = if full {
        survived
    } else {
        h.old_bytes + survived
    };
    h.live_bytes = live;
    h.old_bytes = live;
    h.next_gc = (live * 2).max(MIN_HEAP);
    if full {
        h.full_at = h.next_gc;
    } else {
        h.minors += 1;
    }
    h.small_cursor = 0;
    h.medium_cursor = 0;
    h.collections += 1;
    if full {
        release_free_blocks();
    }
    let h = heap();
    let dt = now_ns() - t0;
    h.gc_cpu_ns += clock_ns(libc::CLOCK_THREAD_CPUTIME_ID) - c0;
    h.gc_ns += dt;
    h.max_ns = h.max_ns.max(dt);
    world::resume();
}

/// Minor collection: queue the referents in the dirty cards of every
/// carded (old LOS) object, cleaning the cards (every survivor of this
/// collection is old, so no old -> young reference outlives it).
fn scan_dirty_cards(len: &mut usize) {
    // SAFETY: walks the LOS list; each prefix's card table covers its
    // object.
    unsafe {
        let mut o = heap().los;
        while !o.is_null() {
            let p = prefix(o);
            if (*header(o)).gc_flags.load(Ordering::Relaxed) & FLAG_CARDED != 0 {
                let n = (*p).size.div_ceil(CARD_SIZE);
                let cards = core::slice::from_raw_parts_mut((*p).cards, n);
                for (c, dirty) in cards.iter_mut().enumerate() {
                    if *dirty != 0 {
                        *dirty = 0;
                        scan_range(o, c * CARD_SIZE, (c + 1) * CARD_SIZE, false, len);
                    }
                }
            }
            o = (*p).next;
        }
    }
}

/// After marking: whether `obj` lives on (it was marked); a survivor's
/// mark is cleared and it becomes old (`STICKY | UNLOGGED`, or
/// `STICKY | CARDED` for a LOS object) when generational.
fn survives(obj: *mut u8, generational: bool) -> bool {
    // SAFETY: `obj` is an object header; the world is stopped.
    let flags = unsafe { &(*header(obj)).gc_flags };
    let f = flags.load(Ordering::Relaxed);
    if f & FLAG_MARK == 0 {
        return false;
    }
    let f = f & !(FLAG_MARK | FLAG_STICKY | FLAG_UNLOGGED | FLAG_CARDED);
    let old = if !generational {
        0
    } else if f & FLAG_LARGE != 0 {
        FLAG_STICKY | FLAG_CARDED
    } else {
        FLAG_STICKY | FLAG_UNLOGGED
    };
    flags.store(f | old, Ordering::Relaxed);
    true
}

/// Sweep the blocks (minor: only the `TAKEN` lines, where all young
/// objects are): survivors keep their lines, dead objects lose their
/// start bit. Bytes of the swept survivors.
fn sweep_blocks(full: bool) -> usize {
    let generational = heap().generational;
    let mut live = 0;
    for b in 0..heap().nblocks {
        let h = heap();
        // SAFETY: `b < nblocks`.
        let m = unsafe { &mut *h.meta.add(b) };
        if !m.used || (!full && !m.lines.contains(&TAKEN)) {
            continue;
        }
        let block = h.base + b * BLOCK_SIZE;
        let mut lines = m.lines;
        for l in &mut lines {
            if full || *l == TAKEN {
                *l = FREE;
            }
        }
        if !full && !m.parsed {
            // No young survivor here, and no start bits to clear.
            m.used = lines.contains(&LIVE);
            m.lines = lines;
            continue;
        }
        m.parsed = false;
        let (old_lines, starts) = (m.lines, m.starts);
        for_each_start(&old_lines, &starts, full, |off| {
            let obj = (block + off) as *mut u8;
            let size = obj_size(obj);
            if survives(obj, generational) {
                live += size;
                lines[off / LINE_SIZE..(off + size).div_ceil(LINE_SIZE)].fill(LIVE);
            } else {
                // Its bytes stay until the line is handed out again.
                m.starts[off / 8 / 64] &= !(1 << (off / 8 % 64));
            }
        });
        m.used = lines.contains(&LIVE);
        m.lines = lines;
    }
    live
}

/// Sweep the LOS list: free dead objects (minor: old ones stay
/// unexamined). Bytes of the swept survivors.
fn sweep_los(full: bool) -> usize {
    let h = heap();
    let generational = h.generational;
    let mut live = 0;
    let mut link: *mut *mut u8 = &mut h.los;
    // SAFETY: walks the LOS list; freed objects are unlinked before their
    // memory is released.
    unsafe {
        while !(*link).is_null() {
            let o = *link;
            let p = prefix(o);
            let old = (*header(o)).gc_flags.load(Ordering::Relaxed) & FLAG_STICKY != 0;
            if !full && old {
                link = &mut (*p).next;
            } else if survives(o, generational) {
                live += (*p).size;
                // Clean: everything it references is old now.
                ptr::write_bytes((*p).cards, 0, (*p).size.div_ceil(CARD_SIZE));
                link = &mut (*p).next;
            } else {
                *link = (*p).next;
                h.los_count -= 1;
                libc::free(o.sub((*p).offset).cast());
            }
        }
    }
    live
}

/// After a full collection's sweep: choose the evacuation candidates
/// (703 §7.3.1 opportunistic defragmentation) from the exact line
/// states the sweep left: when free lines are at least a quarter of the
/// used blocks' lines, every block at most half occupied — if together
/// they hold an eighth of the used lines free. `ROK_GC_EVAC=always`:
/// every used block. Whether there is any.
// ponytail: occupancy counts lines, not live bytes; an object-level
// histogram (Immix's "holes") is the upgrade if this picks poorly.
#[allow(clippy::naive_bytecount)] // 256 bytes per block
fn select_candidates() -> bool {
    let h = heap();
    if h.nblocks == 0 {
        return false;
    }
    // SAFETY: `nblocks` initialized metas.
    let metas = unsafe { core::slice::from_raw_parts_mut(h.meta, h.nblocks) };
    if h.evac_mode == EVAC_ALWAYS {
        let mut any = false;
        for m in metas {
            m.evac = m.used;
            any |= m.used;
        }
        h.fresh_blocks = usize::MAX;
        return any;
    }
    let occupied = |m: &BlockMeta| m.lines.iter().filter(|&&l| l == LIVE).count();
    let (mut used_lines, mut free_lines, mut gain, mut moved) = (0, 0, 0, 0);
    for m in metas.iter().filter(|m| m.used) {
        let occ = occupied(m);
        used_lines += LINES;
        free_lines += LINES - occ;
        if occ <= LINES / 2 {
            gain += LINES - occ;
            moved += occ;
        }
    }
    if used_lines == 0 || free_lines * 4 < used_lines || gain * 8 < used_lines {
        return false;
    }
    for m in metas {
        m.evac = m.used && occupied(m) <= LINES / 2;
    }
    // At most half full each, the candidates fit in half as many blocks:
    // fresh ones may be taken when the holes and free blocks run out.
    h.fresh_blocks = moved.div_ceil(LINES) + 1;
    true
}

/// Copy every movable survivor out of the candidate blocks (leaving its
/// new address in the old header's `gc_word`, `FORWARDED`), rewrite
/// every precise reference to a moved object, then recompute the
/// candidates' lines. A survivor stays put if it is pinned, address-
/// taken (`NOMOVE`), reached through a root or an ambiguous word, or no
/// free line is left for it.
fn evacuate() {
    let h = heap();
    h.evacuations += 1;
    h.copy_cursor = 0;
    h.copy_limit = 0;
    h.copy_line = 0;
    h.copy_phase = 0;
    for i in 0..h.pinned_len {
        // SAFETY: `pinned_len` recorded live block objects.
        let o = unsafe { *h.pinned.add(i) };
        if in_candidate(o) {
            // SAFETY: as above.
            unsafe {
                (*header(o as *mut u8))
                    .gc_flags
                    .fetch_or(FLAG_NOEVAC, Ordering::Relaxed)
            };
        }
    }
    let (base, nblocks) = (h.base, h.nblocks);
    let mut moved = 0;
    for b in 0..nblocks {
        // SAFETY: `b < nblocks`; copied out, as `copy_alloc` may grow
        // (move) the meta table.
        let (evac, lines, starts) = unsafe {
            let m = &*heap().meta.add(b);
            (m.evac, m.lines, m.starts)
        };
        if !evac {
            continue;
        }
        let block = base + b * BLOCK_SIZE;
        for_each_start(&lines, &starts, true, |off| {
            let obj = (block + off) as *mut u8;
            // SAFETY: a survivor's header.
            let flags = unsafe { &(*header(obj)).gc_flags };
            let f = flags.fetch_and(!FLAG_NOEVAC, Ordering::Relaxed);
            if f & (FLAG_NOEVAC | FLAG_NOMOVE | FLAG_PINNED) != 0 {
                return;
            }
            let size = obj_size(obj);
            let Some(to) = copy_alloc(size) else {
                return;
            };
            // SAFETY: `to` is `size` free bytes outside every candidate.
            unsafe {
                ptr::copy_nonoverlapping(obj, to, size);
                (*header(obj)).gc_word = to as u64;
            }
            flags.fetch_or(FLAG_FORWARDED, Ordering::Relaxed);
            moved += size;
        });
    }
    if moved > 0 {
        fix_references();
    }
    for b in 0..nblocks {
        // SAFETY: `b < nblocks`; nothing else touches the table here.
        let m = unsafe { &mut *heap().meta.add(b) };
        if !m.evac {
            continue;
        }
        m.evac = false;
        let block = base + b * BLOCK_SIZE;
        let (lines, starts) = (m.lines, m.starts);
        m.lines = [FREE; LINES];
        for_each_start(&lines, &starts, true, |off| {
            let obj = (block + off) as *mut u8;
            // SAFETY: an object header (moved or not).
            let f = unsafe { (*header(obj)).gc_flags.load(Ordering::Relaxed) };
            if f & FLAG_FORWARDED != 0 {
                m.starts[off / 8 / 64] &= !(1 << (off / 8 % 64));
            } else {
                let end = (off + obj_size(obj)).div_ceil(LINE_SIZE);
                m.lines[off / LINE_SIZE..end].fill(LIVE);
            }
        });
        m.used = m.lines.contains(&LIVE);
    }
    heap().moved_bytes += moved as u64;
}

/// After the copies: rewrite every precise reference word of every
/// survivor (copies included, old copies not) that points into a moved
/// object. Roots and ambiguous words only reach objects that stayed.
// ponytail: a second pass over the live heap; recording the slots that
// point into candidates during the mark needs the candidates before
// the mark, from stale line states (young objects refill the holes and
// look live, so sparse blocks are rarely seen).
#[allow(clippy::cast_ptr_alignment)] // reference words are 8-aligned
fn fix_references() {
    let fix = |o: *mut u8| {
        for_each_ref(o, 0, usize::MAX, |off, precise| {
            if !precise {
                return;
            }
            // SAFETY: `off` is a reference word inside the live `o`.
            unsafe {
                let slot = o.add(off).cast::<usize>();
                let w = slot.read_unaligned();
                if !in_candidate(w) {
                    return;
                }
                if let Some(old) = object_in::<true>(w, false) {
                    slot.write_unaligned(forwarded(old as usize) + (w - old as usize));
                }
            }
        });
    };
    let h = heap();
    let (base, nblocks) = (h.base, h.nblocks);
    for b in 0..nblocks {
        // SAFETY: `b < nblocks`; `fix` only reads the table.
        let (used, lines, starts) = unsafe {
            let m = &*heap().meta.add(b);
            (m.used, m.lines, m.starts)
        };
        if !used {
            continue;
        }
        let block = base + b * BLOCK_SIZE;
        for_each_start(&lines, &starts, true, |off| {
            let obj = (block + off) as *mut u8;
            // SAFETY: a survivor's (or an old copy's) header.
            if unsafe { (*header(obj)).gc_flags.load(Ordering::Relaxed) } & FLAG_FORWARDED == 0 {
                fix(obj);
            }
        });
    }
    // SAFETY: walks the LOS list.
    unsafe {
        let mut o = heap().los;
        while !o.is_null() {
            fix(o);
            o = (*prefix(o)).next;
        }
    }
}

/// The new address of the object at `o` if it was evacuated, else `o`.
fn forwarded(o: usize) -> usize {
    // SAFETY: `o` is an object header.
    unsafe {
        let h = &*header(o as *mut u8);
        if h.gc_flags.load(Ordering::Relaxed) & FLAG_FORWARDED != 0 {
            h.gc_word as usize
        } else {
            o
        }
    }
}

/// Evacuation's bump allocator: `size` bytes in the free lines of a
/// block that is not a candidate (holes of used blocks first, then
/// free blocks, then fresh blocks within the budget). Its lines
/// become `LIVE` and its start bit is set. `None`: no room.
fn copy_alloc(size: usize) -> Option<*mut u8> {
    let h = heap();
    if size > h.copy_limit - h.copy_cursor && !next_copy_run(size.div_ceil(LINE_SIZE)) {
        return None;
    }
    let h = heap();
    let to = h.copy_cursor;
    h.copy_cursor += size;
    let b = (to - h.base) / BLOCK_SIZE;
    let off = to - h.base - b * BLOCK_SIZE;
    // SAFETY: `b < nblocks`.
    let m = unsafe { &mut *h.meta.add(b) };
    m.lines[off / LINE_SIZE..(off + size).div_ceil(LINE_SIZE)].fill(LIVE);
    m.starts[off / 8 / 64] |= 1 << (off / 8 % 64);
    m.used = true;
    m.released = false;
    Some(to as *mut u8)
}

/// Point the copy allocator at the next run of at least `lines` free
/// lines; false when there is none (and no fresh block may be taken).
fn next_copy_run(lines: usize) -> bool {
    let h = heap();
    while h.copy_phase < 2 {
        let total = h.nblocks * LINES;
        while h.copy_line < total {
            let (b, l) = (h.copy_line / LINES, h.copy_line % LINES);
            // SAFETY: `b < nblocks`.
            let m = unsafe { &*h.meta.add(b) };
            if m.evac || m.used != (h.copy_phase == 0) {
                h.copy_line = (b + 1) * LINES;
                continue;
            }
            let mut end = l;
            while end < LINES && m.lines[end] == FREE {
                end += 1;
            }
            h.copy_line = b * LINES + end.max(l + 1);
            if end - l >= lines {
                h.copy_cursor = h.base + b * BLOCK_SIZE + l * LINE_SIZE;
                h.copy_limit = h.base + b * BLOCK_SIZE + end * LINE_SIZE;
                return true;
            }
        }
        h.copy_phase += 1;
        h.copy_line = 0;
    }
    if h.fresh_blocks == 0 {
        return false;
    }
    h.fresh_blocks -= 1;
    let b = new_block();
    let h = heap();
    h.copy_cursor = h.base + b * BLOCK_SIZE;
    h.copy_limit = h.copy_cursor + BLOCK_SIZE;
    true
}

/// After a full collection: give the pages of the free blocks beyond
/// the next cycle's allocation budget back to the OS. They stay
/// reserved and writable, and fault back in zeroed when reused.
fn release_free_blocks() {
    let h = heap();
    let mut keep = h.next_gc.saturating_sub(h.live_bytes).div_ceil(BLOCK_SIZE);
    let mut b = 0;
    while b < h.nblocks {
        // SAFETY: `b < nblocks`.
        let m = unsafe { &*h.meta.add(b) };
        if m.used || m.released || keep > 0 {
            keep -= usize::from(!m.used && !m.released);
            b += 1;
            continue;
        }
        let first = b;
        while b < h.nblocks {
            // SAFETY: `b < nblocks`.
            let m = unsafe { &mut *h.meta.add(b) };
            if m.used || m.released {
                break;
            }
            m.released = true;
            b += 1;
        }
        // SAFETY: remaps whole blocks of our reservation that hold no
        // object (fresh zero pages, same protection).
        let p = unsafe {
            libc::mmap(
                (h.base + first * BLOCK_SIZE) as *mut libc::c_void,
                (b - first) * BLOCK_SIZE,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE | libc::MAP_ANON | libc::MAP_FIXED,
                -1,
                0,
            )
        };
        if p == libc::MAP_FAILED {
            rokr_common::oom();
        }
    }
}

/// The remembered set (generational): old objects that had a reference
/// stored into them since the last collection, each logged once (its
/// `UNLOGGED` bit cleared by the barrier). Each thread appends to its
/// own chunk through `rok_tls_wb_log_cursor` / `_limit` (803) without
/// a lock; a full chunk (and every thread's chunk at a collection or
/// thread exit) is retired onto the lock-free [`LOG_FULL`] stack.
#[repr(C)]
struct LogChunk {
    next: *mut LogChunk,
    /// End of the logged objects (`*mut u8` each, from `self + 1`).
    end: usize,
}

/// Words per log chunk (header included).
const LOG_CHUNK_WORDS: usize = 512;

/// Retired chunks: pushed by any thread, taken with the world stopped.
static LOG_FULL: core::sync::atomic::AtomicPtr<LogChunk> =
    core::sync::atomic::AtomicPtr::new(ptr::null_mut());

/// Retire the chunk behind the wb log slots `[cursor, limit]` (none if
/// null) and clear them.
fn retire_log([cursor, limit]: [*mut usize; 2]) {
    // SAFETY: the slots are the owner's (or a stopped / exiting
    // thread's); a non-null limit ends a chunk from `refill_log`.
    unsafe {
        let end = limit.read();
        if end == 0 {
            return;
        }
        let c = (end - LOG_CHUNK_WORDS * size_of::<usize>()) as *mut LogChunk;
        (*c).end = cursor.read();
        let mut head = LOG_FULL.load(Ordering::Relaxed);
        loop {
            (*c).next = head;
            match LOG_FULL.compare_exchange_weak(head, c, Ordering::Release, Ordering::Relaxed) {
                Ok(_) => break,
                Err(h) => head = h,
            }
        }
        cursor.write(0);
        limit.write(0);
    }
}

/// The calling thread's wb log is full (or absent): retire it and start
/// a fresh chunk.
fn refill_log(slots: [*mut usize; 2]) {
    retire_log(slots);
    // SAFETY: plain allocation; the slots are ours.
    unsafe {
        let c = libc::malloc(LOG_CHUNK_WORDS * size_of::<usize>()).cast::<LogChunk>();
        if c.is_null() {
            rokr_common::oom();
        }
        slots[0].write(c.add(1) as usize);
        slots[1].write(c as usize + LOG_CHUNK_WORDS * size_of::<usize>());
    }
}

/// `f` on every object logged in the chunk list `log`.
fn for_each_logged(mut log: *mut LogChunk, mut f: impl FnMut(*mut u8)) {
    // SAFETY: retired chunks hold objects up to their `end`.
    unsafe {
        while !log.is_null() {
            let mut e = log.add(1).cast::<*mut u8>();
            while (e as usize) < (*log).end {
                f(*e);
                e = e.add(1);
            }
            log = (*log).next;
        }
    }
}

fn free_logs(mut log: *mut LogChunk) {
    while !log.is_null() {
        // SAFETY: chunks come from `refill_log`'s malloc.
        unsafe {
            let next = (*log).next;
            libc::free(log.cast());
            log = next;
        }
    }
}

/// Before the calling thread leaves the registry: retire its wb log so
/// the next collection still sees what it logged.
pub fn retire_own_log() {
    retire_log(rokr_common::tls::wb_log());
}

/// Write barrier for runtime code: call before storing a GC reference
/// into the word at `slot` of the GC object `obj` (what compiled code
/// inlines).
///
/// # Safety
/// `obj` must be a live GC object and `slot` a word inside it.
pub unsafe fn write_barrier(obj: *mut u8, slot: *const u8) {
    // SAFETY: caller contract.
    let flags = unsafe { (*header(obj)).gc_flags.load(Ordering::Relaxed) };
    if flags & FLAG_CARDED != 0 {
        // SAFETY: a carded object is a LOS object with a card table.
        unsafe {
            let cards = (*prefix(obj)).cards;
            *cards.add((slot as usize - obj as usize) / CARD_SIZE) = 1;
        }
    } else if flags & FLAG_UNLOGGED != 0 {
        // SAFETY: caller contract.
        unsafe { write_barrier_slow(obj) };
    }
}

/// `rok_gc_wb_slow`: remember `obj` for the next minor collection.
///
/// `obj` (old, `UNLOGGED`) is about to hold a reference that may be
/// young. Not a safepoint: no collection runs between the
/// barrier and the store that follows it.
///
/// # Safety
/// `obj` must be a live GC object.
pub unsafe fn write_barrier_slow(obj: *mut u8) {
    // SAFETY: caller contract.
    let flags = unsafe { &(*header(obj)).gc_flags };
    // Racing stores: exactly one thread logs it.
    if flags.fetch_and(!FLAG_UNLOGGED, Ordering::Relaxed) & FLAG_UNLOGGED == 0 {
        return;
    }
    let slots = rokr_common::tls::wb_log();
    // SAFETY: this thread's own slots: `cursor < limit` inside its chunk.
    unsafe {
        if slots[0].read() == slots[1].read() {
            refill_log(slots);
        }
        let c = slots[0].read();
        (c as *mut *mut u8).write(obj);
        slots[0].write(c + size_of::<usize>());
    }
}

/// Bytes held by GC objects (headers included) as of the last
/// collection, plus everything handed out since (whole TLABs).
pub fn live_bytes() -> usize {
    world::lock();
    let n = heap().live_bytes;
    world::unlock();
    n
}

pub fn collections() -> u64 {
    world::lock();
    let n = heap().collections;
    world::unlock();
    n
}

/// Bytes evacuation has copied so far.
pub fn moved_bytes() -> u64 {
    world::lock();
    let n = heap().moved_bytes;
    world::unlock();
    n
}

#[cfg(test)]
#[allow(
    clippy::missing_const_for_fn,
    clippy::cast_ptr_alignment,
    clippy::items_after_statements
)]
mod tests {
    use super::*;

    #[repr(C)]
    struct Frame {
        prev: *mut Frame,
        count: usize,
    }

    #[test]
    #[allow(clippy::cast_ptr_alignment)] // GC objects are 8-aligned
    fn collect_frees_unreachable_and_keeps_traced_children() {
        // 802 table: total 32, version 1, one STRONG_REF at offset 16.
        static TABLE: [u32; 4] = [32, 1 | (1 << 16), 16, STRONG_REF];
        rokr_common::tls::thread_init();
        world::attach_current();
        register_type(USER_TYPE_BASE, TABLE.as_ptr().cast());
        collect();
        let base = live_bytes();
        let a = alloc(32, 8, USER_TYPE_BASE);
        let b = alloc(24, 8, USER_TYPE_BASE + 1); // unregistered: leaf
        let garbage = alloc(24, 8, USER_TYPE_BASE + 1);
        // SAFETY: `a` has a 16-byte payload; frame layout matches
        // `Frame` + one slot; the frame is unlinked before it dies.
        unsafe {
            *garbage.add(16) = 7;
            *a.add(16).cast::<*mut u8>() = b;
            let mut junk = 0x1234usize; // inline `any` bits: ignored
            let mut root = a as usize;
            let mut frame: (Frame, *mut usize, *mut usize) = (
                Frame {
                    prev: ptr::null_mut(),
                    count: 2,
                },
                &mut root,
                &mut junk,
            );
            let top = rokr_common::tls::shadow_stack_top();
            *top = (&raw mut frame).cast();
            collect();
            assert_eq!(live_bytes(), base + 32 + 24);
            assert_eq!((*header(b)).type_id, USER_TYPE_BASE + 1);
            assert_eq!(object_containing(garbage as usize + 16, false), None);
            *frame.1 = 0;
            collect();
            assert_eq!(live_bytes(), base);
            *top = ptr::null_mut();
        }
        scan_words_buffers_and_interior_pointers();
        medium_and_large_objects();
        free_lines_are_reused();
        minor_collection_keeps_logged_children();
        minor_collection_scans_dirty_cards();
        evacuation_moves_objects_and_fixes_references();
        evacuation_defragments_sparse_blocks();
    }

    fn word(o: *mut u8, off: usize) -> usize {
        // SAFETY: tests read words inside their own objects.
        unsafe { o.add(off).cast::<usize>().read_unaligned() }
    }

    fn set(o: *mut u8, off: usize, v: usize) {
        // SAFETY: tests write words inside their own objects.
        unsafe { o.add(off).cast::<usize>().write_unaligned(v) };
    }

    /// `ROK_GC_EVAC=always`: a full collection moves what it may and
    /// fixes every precise reference (header, interior `str`, boxed
    /// `any` payload, array-table buffer element); roots, ambiguous
    /// words, `NOMOVE` objects and inline `any` payloads behave.
    #[allow(clippy::many_single_char_names)]
    fn evacuation_moves_objects_and_fixes_references() {
        // A: {ref @16, str ptr @24, any tag @32 + payload @40}.
        static A: [u32; 8] = [
            48,
            1 | (3 << 16),
            16,
            STRONG_REF,
            24,
            INTERIOR_REF,
            32,
            ANY_SLOT,
        ];
        // R: a buffer of references (array table, 8-byte elements).
        static R: [u32; 4] = [8, 1 | TABLE_ARRAY as u32 | (1 << 16), 0, STRONG_REF];
        let (ta, tr, leaf) = (USER_TYPE_BASE + 10, USER_TYPE_BASE + 11, USER_TYPE_BASE + 1);
        register_type(ta, A.as_ptr().cast());
        register_type(tr, R.as_ptr().cast());
        heap().evac_mode = EVAC_ALWAYS;
        let base = live_bytes();
        let a = alloc(48, 8, ta);
        let a2 = alloc(48, 8, ta);
        let (b, c, d, e, f, g) = (
            alloc(24, 8, leaf),
            alloc(32, 8, leaf),
            alloc(24, 8, leaf),
            alloc(24, 8, leaf),
            alloc(24, 8, leaf),
            alloc(24, 8, leaf),
        );
        let r = alloc(16 + 16, 8, tr);
        let w = alloc(16 + 8, 8, SCAN_WORDS_TYPE_ID);
        for (o, v) in [(b, 0xB), (c, 0xC), (d, 0xD), (e, 0xE), (f, 0xF)] {
            set(o, 16, v);
        }
        set(a, 16, b as usize);
        set(a, 24, c as usize + 20);
        // SAFETY: tests write their own objects' headers / words.
        unsafe {
            a.add(32).cast::<u32>().write(0x1234 | ANY_BOXED);
            a2.add(32).cast::<u32>().write(0x1234); // inline: payload is bits
            no_move(f);
        }
        set(a, 40, r as usize);
        set(a2, 40, g as usize);
        set(r, 16, e as usize);
        set(r, 24, f as usize);
        set(w, 16, d as usize);
        // SAFETY: frame layout matches `Frame` + three slots, unlinked
        // before it dies.
        unsafe {
            let (mut ra, mut ra2, mut rw) = (a as usize, a2 as usize, w as usize);
            let mut frame: (Frame, *mut usize, *mut usize, *mut usize) = (
                Frame {
                    prev: ptr::null_mut(),
                    count: 3,
                },
                &mut ra,
                &mut ra2,
                &mut rw,
            );
            let top = rokr_common::tls::shadow_stack_top();
            *top = (&raw mut frame).cast();
            let moved = heap().moved_bytes;
            collect();
            assert!(heap().moved_bytes > moved);
            // Rooted objects stay; what they reach precisely moves.
            assert_eq!((ra, ra2, rw), (a as usize, a2 as usize, w as usize));
            let b2 = word(a, 16) as *mut u8;
            assert_ne!(b2, b);
            assert_eq!(word(b2, 16), 0xB);
            let c2 = (word(a, 24) - 20) as *mut u8;
            assert_ne!(c2, c);
            assert_eq!(word(c2, 16), 0xC);
            let r2 = word(a, 40) as *mut u8;
            assert_ne!(r2, r);
            assert_eq!((*header(r2)).type_id, tr);
            let e2 = word(r2, 16) as *mut u8;
            assert_ne!(e2, e);
            assert_eq!(word(e2, 16), 0xE);
            // Address-taken, ambiguous: in place.
            assert_eq!(word(r2, 24), f as usize);
            assert_eq!(word(f, 16), 0xF);
            assert_eq!(word(w, 16), d as usize);
            assert_eq!(word(d, 16), 0xD);
            // `g` was only behind an inline `any` payload: dead.
            assert_eq!(object_containing(g as usize, false), None);
            assert_eq!(object_containing(b as usize, false), None);
            assert_eq!(live_bytes(), base + 48 * 2 + 24 * 4 + 32 + 32 + 24);
            // A second round moves the copies again.
            collect();
            let b3 = word(a, 16) as *mut u8;
            assert_eq!(word(b3, 16), 0xB);
            assert_eq!(word(word(word(a, 40) as *mut u8, 16) as *mut u8, 16), 0xE);
            *frame.1 = 0;
            *frame.2 = 0;
            *frame.3 = 0;
            collect();
            assert_eq!(live_bytes(), base);
            *top = ptr::null_mut();
        }
        heap().evac_mode = EVAC_AUTO;
    }

    /// Default mode: after most of a block-filling population dies, the
    /// sparse blocks are emptied into one and the rest freed.
    fn evacuation_defragments_sparse_blocks() {
        static R: [u32; 4] = [8, 1 | TABLE_ARRAY as u32 | (1 << 16), 0, STRONG_REF];
        let (tr, leaf) = (USER_TYPE_BASE + 12, USER_TYPE_BASE + 1);
        register_type(tr, R.as_ptr().cast());
        assert_eq!(heap().evac_mode, EVAC_AUTO);
        collect();
        let base = live_bytes();
        const N: usize = 4096;
        let r = alloc(16 + 8 * N, 8, tr);
        let used = || {
            // SAFETY: `nblocks` initialized metas.
            unsafe { core::slice::from_raw_parts(heap().meta, heap().nblocks) }
                .iter()
                .filter(|m| m.used)
                .count()
        };
        // SAFETY: as above.
        unsafe {
            let mut root = r as usize;
            let mut frame: (Frame, *mut usize) = (
                Frame {
                    prev: ptr::null_mut(),
                    count: 1,
                },
                &mut root,
            );
            let top = rokr_common::tls::shadow_stack_top();
            *top = (&raw mut frame).cast();
            let before = used();
            for i in 0..N {
                let o = alloc(64, 8, leaf);
                set(o, 16, i);
                set(r, 16 + 8 * i, o as usize);
            }
            collect();
            let full = used();
            assert!(full >= before + N * 64 / BLOCK_SIZE, "{before} -> {full}");
            for i in (0..N).filter(|i| i % 16 != 0) {
                set(r, 16 + 8 * i, 0);
            }
            let moved = heap().moved_bytes;
            collect(); // sweeps the dead: blocks 1/16 live
            collect(); // evacuates them
            assert!(heap().moved_bytes - moved >= (N / 16 * 64) as u64);
            assert!(used() <= before + 2, "{before} -> {full} -> {}", used());
            for i in (0..N).step_by(16) {
                assert_eq!(word(word(r, 16 + 8 * i) as *mut u8, 16), i);
            }
            assert_eq!(live_bytes(), base + 16 + 8 * N + N / 16 * 64);
            *frame.1 = 0;
            collect();
            *top = ptr::null_mut();
        }
    }

    /// Generational: a young object reachable only through an old one
    /// (stored behind the write barrier) survives minor collections;
    /// unreachable young objects do not.
    #[allow(clippy::cast_ptr_alignment)] // GC objects are 8-aligned
    fn minor_collection_keeps_logged_children() {
        assert!(heap().generational);
        let base = live_bytes();
        let old = alloc(32, 8, USER_TYPE_BASE);
        // SAFETY: as above.
        unsafe {
            let mut root = old as usize;
            let mut frame: (Frame, *mut usize) = (
                Frame {
                    prev: ptr::null_mut(),
                    count: 1,
                },
                &mut root,
            );
            let top = rokr_common::tls::shadow_stack_top();
            *top = (&raw mut frame).cast();
            collect();
            let flags = (*header(old)).gc_flags.load(Ordering::Relaxed);
            assert_eq!(
                flags & (FLAG_STICKY | FLAG_UNLOGGED),
                FLAG_STICKY | FLAG_UNLOGGED
            );
            let young = alloc(24, 8, USER_TYPE_BASE + 1);
            let garbage = alloc(24, 8, USER_TYPE_BASE + 1);
            write_barrier(old, old.add(16));
            *old.add(16).cast::<*mut u8>() = young;
            let minors = heap().minors;
            collect_young();
            collect_young();
            assert_eq!(heap().minors, minors + 2);
            assert_eq!((*header(young)).type_id, USER_TYPE_BASE + 1);
            assert_eq!(object_containing(garbage as usize, false), None);
            assert_eq!(live_bytes(), base + 32 + 24);
            *old.add(16).cast::<*mut u8>() = ptr::null_mut();
            *frame.1 = 0;
            collect();
            assert_eq!(live_bytes(), base);
            *top = ptr::null_mut();
        }
    }

    /// Generational: an old LOS buffer is carded; a young object stored
    /// into it (behind the barrier) survives minors through its card
    /// alone; once overwritten it dies at the next minor.
    #[allow(clippy::cast_ptr_alignment)] // GC objects are 8-aligned
    fn minor_collection_scans_dirty_cards() {
        let base = live_bytes();
        let size = 64 << 10;
        let buf = alloc(size, 8, SCAN_WORDS_TYPE_ID);
        // SAFETY: as above.
        unsafe {
            let mut root = buf as usize;
            let mut frame: (Frame, *mut usize) = (
                Frame {
                    prev: ptr::null_mut(),
                    count: 1,
                },
                &mut root,
            );
            let top = rokr_common::tls::shadow_stack_top();
            *top = (&raw mut frame).cast();
            collect();
            let flags = (*header(buf)).gc_flags.load(Ordering::Relaxed);
            assert_eq!(
                flags & (FLAG_STICKY | FLAG_CARDED),
                FLAG_STICKY | FLAG_CARDED
            );
            let young = alloc(24, 8, USER_TYPE_BASE + 1);
            let slot = buf.add(40_000);
            write_barrier(buf, slot);
            *slot.cast::<*mut u8>() = young;
            assert_eq!(*(*prefix(buf)).cards.add(40_000 / CARD_SIZE), 1);
            collect_young();
            assert_eq!((*header(young)).type_id, USER_TYPE_BASE + 1);
            assert_eq!(live_bytes(), base + size + 24);
            let young2 = alloc(24, 8, USER_TYPE_BASE + 1);
            write_barrier(buf, slot);
            *slot.cast::<*mut u8>() = young2;
            collect_young();
            // `young` is old now (it survived a minor): only a full
            // collection frees it.
            assert_eq!(live_bytes(), base + size + 48);
            collect();
            assert_eq!(live_bytes(), base + size + 24);
            *frame.1 = 0;
            collect();
            assert_eq!(live_bytes(), base);
            *top = ptr::null_mut();
        }
    }

    // Called from the test above: the heap is a single-mutator global,
    // so GC tests must not run on parallel test threads.
    #[allow(clippy::cast_ptr_alignment)] // GC objects are 8-aligned
    fn scan_words_buffers_and_interior_pointers() {
        let base = live_bytes();
        let buf = alloc(16 + 16, 8, SCAN_WORDS_TYPE_ID);
        let s = alloc(24, 8, USER_TYPE_BASE + 7);
        // SAFETY: as above; the buffer holds an interior pointer into `s`
        // and a non-pointer word; only the buffer's payload is rooted.
        unsafe {
            *buf.add(16).cast::<usize>() = 0x99;
            *buf.add(24).cast::<*mut u8>() = s.add(18);
            let mut root = buf as usize + 20; // interior root
            let mut frame: (Frame, *mut usize) = (
                Frame {
                    prev: ptr::null_mut(),
                    count: 1,
                },
                &mut root,
            );
            let top = rokr_common::tls::shadow_stack_top();
            *top = (&raw mut frame).cast();
            collect();
            assert_eq!(live_bytes(), base + 32 + 24);
            *frame.1 = 0;
            collect();
            assert_eq!(live_bytes(), base);
            *top = ptr::null_mut();
        }
    }

    /// Medium objects (several lines) and LOS objects are found through
    /// interior pointers and freed when unreachable.
    fn medium_and_large_objects() {
        let base = live_bytes();
        let medium = alloc(1000, 8, USER_TYPE_BASE + 1);
        let large = alloc(LOS_THRESHOLD + 8, 8, USER_TYPE_BASE + 1);
        // SAFETY: as above.
        unsafe {
            assert_ne!(
                (*header(large)).gc_flags.load(Ordering::Relaxed) & FLAG_LARGE,
                0
            );
            let mut r1 = medium as usize + 900;
            let mut r2 = large as usize + 5000;
            let mut frame: (Frame, *mut usize, *mut usize) = (
                Frame {
                    prev: ptr::null_mut(),
                    count: 2,
                },
                &mut r1,
                &mut r2,
            );
            let top = rokr_common::tls::shadow_stack_top();
            *top = (&raw mut frame).cast();
            collect();
            assert_eq!(live_bytes(), base + 1000 + LOS_THRESHOLD + 8);
            *frame.1 = 0;
            *frame.2 = 0;
            collect();
            assert_eq!(live_bytes(), base);
            *top = ptr::null_mut();
        }
    }

    /// After a collection the dead objects' lines are handed out again
    /// (zeroed) instead of growing the heap.
    fn free_lines_are_reused() {
        collect();
        let blocks = heap().nblocks;
        for _ in 0..3 {
            for _ in 0..(4 * BLOCK_SIZE / 64) {
                let p = alloc(64, 8, USER_TYPE_BASE + 1);
                // SAFETY: a fresh 64-byte object.
                unsafe {
                    assert_eq!(*p.add(40), 0);
                    *p.add(40) = 1;
                }
            }
            collect();
        }
        assert!(heap().nblocks <= blocks + 5, "{} blocks", heap().nblocks);
    }
}
