//! Garbage collector: precise, non-moving, stop-the-world mark-region
//! (Immix-style blocks and lines, 703 §7.3.1, without evacuation).
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
//! Every object's `gc_word` (801 §8.1.4) holds its size (8-rounded;
//! this collector never forwards) and block objects have a nonzero
//! `type_id`, so a block is parsable: memory that is not an object is
//! all zero. Free lines are zero because the sweep
//! zeroes every dead object; the TLAB fast path therefore hands out
//! zeroed memory without a memset.
//!
//! A collection (heap over `max(4 MiB, 2 x live)`, or `rok_gc_collect`)
//! stops every mutator ([`world`]), empties all TLABs, parses the used
//! blocks into per-block object-start bitmaps, marks from all shadow
//! stacks, then sweeps: live objects mark their lines, dead ones are
//! zeroed, unmarked lines are free for the next cycle's TLABs.
//!
//! ponytail: no evacuation / defragmentation, no sticky mark-bit
//! generations (704), no concurrent marking (705); blocks are never
//! returned to the OS (`madvise` of clean blocks is the upgrade).
//!
//! Roots (704 §7.4.1): compiled code links a frame
//! `{ prev, count, slots[count] }` into `rok_tls_shadow_stack_top` on
//! entry and unlinks it on every return; each slot is the *address* of a
//! word that holds a GC reference (0 = none).
//!
//! Children (802): `type_id → ScanTable` registered by
//! [`register_type`]; only `STRONG_REF` entries are traced. An object
//! whose type was never registered has no traced children.
//!
//! A root slot or `STRONG_REF` word may also hold raw bits: the compiler
//! types the whole payload word of an `any` value as a reference, but
//! small primitives live there inline (`ANY_SLOT`, 802 §8.2.7). Instead
//! of decoding tags, every candidate word is looked up among the
//! objects (interior pointers count: a `str` points into its object's
//! payload); a word outside every object is ignored and an integer that
//! happens to equal one only retains that object. Words the compiler
//! never typed as references (`usize`, raw `rok_alloc` memory) are never
//! looked at, so marking stays precise everywhere else.

#![cfg_attr(not(test), no_std)]

use core::cell::UnsafeCell;
use core::mem::size_of;
use core::ptr;
use core::sync::atomic::Ordering;

use rokr_common::fatal;
use rokr_common::object_header::{
    FLAG_IMMORTAL, FLAG_LARGE, FLAG_MARK, FLAG_PINNED, HEADER_ALIGN, HEADER_SIZE, ObjectHeader,
};

pub mod world;

/// Heap size below which no collection runs.
const MIN_HEAP: usize = 4 << 20;
/// First type id of the user range (801 §8.1.2).
const USER_TYPE_BASE: u32 = 0x10000;
const STRONG_REF: u32 = 0;
/// Reserved type id: every pointer-aligned payload word is a candidate
/// reference (library buffers whose element layout the runtime does not
/// know; checked like any candidate word).
pub const SCAN_WORDS_TYPE_ID: u32 = 2;

/// Immix block / line geometry (703 §7.3.1).
pub const BLOCK_SIZE: usize = 32 << 10;
pub const LINE_SIZE: usize = 128;
const LINES: usize = BLOCK_SIZE / LINE_SIZE;
const GRANULES: usize = BLOCK_SIZE / 8;
/// Objects this large (header included) go to the LOS (702 §7.2.3).
pub const LOS_THRESHOLD: usize = 8 << 10;
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

/// Side metadata of one block.
struct BlockMeta {
    lines: [u8; LINES],
    /// Object starts (one bit per 8-byte granule), rebuilt by every
    /// collection before marking.
    starts: [u64; GRANULES / 64],
    /// Holds objects or was handed out since the last sweep (else it
    /// is all zero and all `FREE`).
    used: bool,
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
}

struct Heap {
    /// Bytes of objects alive after the last collection plus everything
    /// handed out since (TLABs count in full).
    live_bytes: usize,
    next_gc: usize,
    collections: u64,
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
}

struct Global(UnsafeCell<Heap>);
// SAFETY: only touched with the world lock held (see module docs).
unsafe impl Sync for Global {}

static HEAP: Global = Global(UnsafeCell::new(Heap {
    live_bytes: 0,
    next_gc: MIN_HEAP,
    collections: 0,
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

/// Size of the object at `obj` (its `gc_word`).
fn obj_size(obj: *mut u8) -> usize {
    // SAFETY: callers pass object headers (or zeroed block memory, which
    // reads as 0).
    unsafe { (*header(obj)).gc_word as usize }
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
    let h = heap();
    let want = if size8 > LINE_SIZE { size8 } else { LINE_SIZE };
    if h.live_bytes.saturating_add(want) > h.next_gc {
        collect_locked();
    }
    let obj = if size8 > LINE_SIZE {
        // A medium object that does not fit the TLAB: its own lines, so
        // the TLAB's tail stays usable.
        let obj = take_run(size8.div_ceil(LINE_SIZE), true);
        heap().live_bytes += size8;
        obj
    } else {
        let start = take_run(1, false);
        let end = (start as usize + 1).next_multiple_of(LINE_SIZE);
        let end = end_of_run(start as usize, end);
        heap().live_bytes += end - start as usize;
        // SAFETY: this thread's own TLAB slots.
        unsafe {
            cursor.write(start as usize + size8);
            limit.write(end);
        }
        start
    };
    world::unlock();
    init_header(obj, type_id, size8, 0);
    obj
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
        });
    }
    h.nblocks += 1;
    b
}

/// A large (or over-aligned) object: its own zeroed `malloc` block.
fn alloc_large(size: usize, align: usize, type_id: u32) -> *mut u8 {
    let align = align.max(HEADER_ALIGN);
    let offset = size_of::<Prefix>().next_multiple_of(align);
    let Some(total) = size.checked_add(offset) else {
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
    let h = heap();
    // The new block is not on the list yet, so a collection here cannot
    // free it.
    if h.live_bytes.saturating_add(size) > h.next_gc {
        collect_locked();
    }
    let h = heap();
    // SAFETY: `base..base+total` is ours; `obj` is `align`-aligned and the
    // prefix fits in the `offset` bytes before it.
    let obj = unsafe {
        let obj = base.cast::<u8>().add(offset);
        prefix(obj).write(Prefix {
            next: h.los,
            size,
            offset,
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

/// Call `f(offset)` for every object of the block at `block` (line
/// states `lines`), by parsing it: an object has a nonzero `type_id`
/// (0 is reserved, 801 §8.1.2) and its size in `gc_word`; everything
/// else is zero. Lines free since the last sweep are skipped whole.
fn parse_block(block: usize, lines: &[u8; LINES], mut f: impl FnMut(usize)) {
    let mut off = 0;
    // An object needs at least a header's room.
    while off + HEADER_SIZE <= BLOCK_SIZE {
        if off % LINE_SIZE == 0 && lines[off / LINE_SIZE] == FREE {
            off += LINE_SIZE;
            continue;
        }
        let obj = (block + off) as *mut u8;
        // SAFETY: `off + 16 <= BLOCK_SIZE`: an object header or zeroes.
        if unsafe { (*header(obj)).type_id } == 0 {
            off += 8;
        } else {
            f(off);
            off += obj_size(obj);
        }
    }
}

/// Before marking: object-start bitmaps of all used blocks, the sorted
/// LOS index, and the pinned / immortal objects queued as roots.
fn build_index(len: &mut usize) {
    for b in 0..heap().nblocks {
        let h = heap();
        // SAFETY: `b < nblocks`.
        let m = unsafe { &mut *h.meta.add(b) };
        let mut starts = [0u64; GRANULES / 64];
        if m.used {
            let block = h.base + b * BLOCK_SIZE;
            parse_block(block, &m.lines, |off| {
                starts[off / 8 / 64] |= 1 << (off / 8 % 64);
                pin_root((block + off) as *mut u8, len);
            });
        }
        m.starts = starts;
    }
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
            pin_root(o, len);
            o = (*prefix(o)).next;
        }
        core::slice::from_raw_parts_mut(h.index, h.los_count).sort_unstable();
    }
}

/// Queue `obj` if it is pinned or immortal.
fn pin_root(obj: *mut u8, len: &mut usize) {
    // SAFETY: `obj` is an object header.
    let flags = unsafe { (*header(obj)).gc_flags.load(Ordering::Relaxed) };
    if flags & (FLAG_PINNED | FLAG_IMMORTAL) != 0 {
        push_obj(obj, len);
    }
}

/// The object whose header address is `word` or whose memory contains
/// it (a `str` points at its payload bytes, or into them after slicing).
fn object_containing(word: usize) -> Option<*mut u8> {
    let h = heap();
    if word >= h.base && word < h.base + h.nblocks * BLOCK_SIZE {
        let blk = (word - h.base) / BLOCK_SIZE;
        // SAFETY: `blk < nblocks`.
        let meta = unsafe { &*h.meta.add(blk) };
        if !meta.used {
            return None;
        }
        let block = h.base + blk * BLOCK_SIZE;
        let granule = (word - block) / 8;
        // The nearest object start at or before `granule`: objects are
        // smaller than `LOS_THRESHOLD`, so only that many granules back.
        let lowest = granule.saturating_sub(LOS_THRESHOLD / 8);
        let mut i = granule / 64;
        let mut bits = meta.starts[i] & (u64::MAX >> (63 - granule % 64));
        loop {
            if bits != 0 {
                let start = block + (i * 64 + 63 - bits.leading_zeros() as usize) * 8;
                let size = obj_size(start as *mut u8);
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
    (word < start + obj_size(start as *mut u8)).then_some(start as *mut u8)
}

/// Queue the object `word` points into, if any, for marking.
fn push(word: *mut u8, len: &mut usize) {
    if let Some(obj) = object_containing(word as usize) {
        push_obj(obj, len);
    }
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

/// Full stop-the-world collection (`rok_gc_collect`).
pub fn collect() {
    world::lock();
    collect_locked();
    world::unlock();
}

/// With the world lock held: stop every other mutator, mark from all
/// registered threads' shadow stacks and from pinned / immortal objects,
/// sweep, resume.
#[allow(clippy::cast_ptr_alignment)] // tables are word-aligned
fn collect_locked() {
    world::stop();
    world::reset_tlabs();
    let mut len = 0;
    build_index(&mut len);
    world::for_each_root(|word| push(word, &mut len));

    while len > 0 {
        len -= 1;
        // SAFETY: `push` only queues addresses of live GC objects.
        unsafe {
            let o = *heap().stack.add(len);
            let hd = &*header(o);
            if hd.gc_flags.fetch_or(FLAG_MARK, Ordering::Relaxed) & FLAG_MARK != 0 {
                continue;
            }
            if hd.type_id == SCAN_WORDS_TYPE_ID {
                let words = (obj_size(o) - HEADER_SIZE) / size_of::<usize>();
                let payload = o.add(HEADER_SIZE).cast::<*mut u8>();
                for w in 0..words {
                    push(payload.add(w).read(), &mut len);
                }
                continue;
            }
            let t = scan_table(hd.type_id);
            if t.is_null() {
                continue;
            }
            let n = t.add(6).cast::<u16>().read_unaligned() as usize;
            for e in 0..n {
                let entry = t.add(8 + 8 * e).cast::<u32>();
                if entry.add(1).read_unaligned() == STRONG_REF {
                    let off = entry.read_unaligned() as usize;
                    push(o.add(off).cast::<*mut u8>().read_unaligned(), &mut len);
                }
            }
        }
    }
    let live = sweep_blocks() + sweep_los();
    let h = heap();
    h.live_bytes = live;
    h.next_gc = (live * 2).max(MIN_HEAP);
    h.small_cursor = 0;
    h.medium_cursor = 0;
    h.collections += 1;
    world::resume();
}

/// Clear the mark of `obj`; whether it was set.
fn unmark(obj: *mut u8) -> bool {
    // SAFETY: `obj` is an object header.
    unsafe {
        (*header(obj))
            .gc_flags
            .fetch_and(!FLAG_MARK, Ordering::Relaxed)
            & FLAG_MARK
            != 0
    }
}

/// Sweep the blocks: marked objects keep their lines, dead ones are
/// zeroed. Bytes of the survivors.
fn sweep_blocks() -> usize {
    let mut live = 0;
    for b in 0..heap().nblocks {
        let h = heap();
        // SAFETY: `b < nblocks`.
        let m = unsafe { &mut *h.meta.add(b) };
        if !m.used {
            continue;
        }
        let block = h.base + b * BLOCK_SIZE;
        let mut lines = [FREE; LINES];
        for (w, &word) in m.starts.iter().enumerate() {
            let mut bits = word;
            while bits != 0 {
                let off = (w * 64 + bits.trailing_zeros() as usize) * 8;
                bits &= bits - 1;
                let obj = (block + off) as *mut u8;
                let size = obj_size(obj);
                if unmark(obj) {
                    live += size;
                    lines[off / LINE_SIZE..(off + size).div_ceil(LINE_SIZE)].fill(LIVE);
                } else {
                    // SAFETY: a dead object's memory, ours to reuse.
                    unsafe { ptr::write_bytes(obj, 0, size) };
                }
            }
        }
        m.used = lines.contains(&LIVE);
        m.lines = lines;
    }
    live
}

/// Sweep the LOS list: free unmarked objects. Bytes of the survivors.
fn sweep_los() -> usize {
    let h = heap();
    let mut live = 0;
    let mut link: *mut *mut u8 = &mut h.los;
    // SAFETY: walks the LOS list; freed objects are unlinked before their
    // memory is released.
    unsafe {
        while !(*link).is_null() {
            let o = *link;
            let p = prefix(o);
            if unmark(o) {
                live += (*p).size;
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

#[cfg(test)]
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
            // The dead object was zeroed for reuse.
            assert_eq!(*garbage.add(16), 0);
            *frame.1 = 0;
            collect();
            assert_eq!(live_bytes(), base);
            *top = ptr::null_mut();
        }
        scan_words_buffers_and_interior_pointers();
        medium_and_large_objects();
        free_lines_are_reused();
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
