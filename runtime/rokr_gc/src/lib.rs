//! Garbage collector: precise, non-moving, stop-the-world mark-sweep.
//!
//! ponytail: stand-in for Immix (703) + sticky mark-bit generations +
//! concurrent mark (705). Every object is its own `malloc` block; the
//! 16-byte header (801) is untouched and a hidden [`Prefix`] in front of
//! it links all objects for the sweep. Single mutator thread: the heap
//! is a plain global and only the calling thread's shadow stack is
//! walked. Upgrade path: TLAB + Immix blocks, a thread registry for
//! roots, write-barrier logs for sticky / concurrent marking.
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
//! of decoding tags, every candidate word is looked up in the sorted set
//! of object addresses (interior pointers count: a `str` points into its
//! object's payload); a word outside every object is ignored and an integer that
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
    FLAG_IMMORTAL, FLAG_MARK, FLAG_PINNED, HEADER_ALIGN, HEADER_SIZE, ObjectHeader,
};

/// Heap size below which no collection runs.
const MIN_HEAP: usize = 4 << 20;
/// First type id of the user range (801 §8.1.2).
const USER_TYPE_BASE: u32 = 0x10000;
const STRONG_REF: u32 = 0;
/// Reserved type id: every pointer-aligned payload word is a candidate
/// reference (library buffers whose element layout the runtime does not
/// know; checked like any candidate word).
pub const SCAN_WORDS_TYPE_ID: u32 = 2;

/// Hidden bookkeeping right before each object header.
#[repr(C)]
struct Prefix {
    /// Header of the next object in the all-objects list.
    next: *mut u8,
    /// Total object size, header included (what `live_bytes` counts).
    size: usize,
    /// Bytes from the `malloc` base to the header.
    offset: usize,
}

#[repr(C)]
struct Frame {
    prev: *mut Frame,
    count: usize,
    // `slots: [*mut usize; count]` follows.
}

struct Heap {
    objects: *mut u8,
    live_bytes: usize,
    next_gc: usize,
    collections: u64,
    /// `scan_tables[type_id - USER_TYPE_BASE]`, null = unregistered.
    scan_tables: *mut *const u8,
    scan_len: usize,
    /// Mark stack (grown with `realloc`).
    stack: *mut *mut u8,
    stack_cap: usize,
    /// Number of objects on the `objects` list.
    count: usize,
    /// Sorted object addresses, rebuilt by every collection.
    index: *mut usize,
    index_cap: usize,
}

struct Global(UnsafeCell<Heap>);
// SAFETY: single mutator thread (see module docs).
unsafe impl Sync for Global {}

static HEAP: Global = Global(UnsafeCell::new(Heap {
    objects: ptr::null_mut(),
    live_bytes: 0,
    next_gc: MIN_HEAP,
    collections: 0,
    scan_tables: ptr::null_mut(),
    scan_len: 0,
    stack: ptr::null_mut(),
    stack_cap: 0,
    count: 0,
    index: ptr::null_mut(),
    index_cap: 0,
}));

fn heap() -> &'static mut Heap {
    // SAFETY: single mutator thread; no caller keeps the reference across
    // another `heap()` call.
    unsafe { &mut *HEAP.0.get() }
}

const fn prefix(obj: *mut u8) -> *mut Prefix {
    obj.wrapping_sub(size_of::<Prefix>()).cast()
}

const fn header(obj: *mut u8) -> *mut ObjectHeader {
    obj.cast()
}

/// Allocate a zeroed GC object of `size` bytes (header included) and
/// initialize its header. May collect first. Never null.
pub fn alloc(size: usize, align: usize, type_id: u32) -> *mut u8 {
    if size < HEADER_SIZE {
        fatal(b"rok_gc_alloc_slow: size smaller than the object header");
    }
    if !align.is_power_of_two() {
        fatal(b"rok runtime: allocation align is not a power of two");
    }
    let align = align.max(HEADER_ALIGN);
    let offset = size_of::<Prefix>().next_multiple_of(align);
    let Some(total) = size.checked_add(offset) else {
        fatal(b"rok runtime: allocation size overflow");
    };
    let h = heap();
    if h.live_bytes.saturating_add(size) > h.next_gc {
        collect();
    }
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
        fatal(b"rok runtime: out of memory");
    }
    let h = heap();
    // SAFETY: `base..base+total` is ours; `obj` is `align`-aligned and the
    // prefix fits in the `offset` bytes before it.
    unsafe {
        let obj = base.cast::<u8>().add(offset);
        prefix(obj).write(Prefix {
            next: h.objects,
            size,
            offset,
        });
        ObjectHeader::init(obj, type_id);
        h.objects = obj;
        h.count += 1;
        h.live_bytes += size;
        obj
    }
}

/// Register the 802 `ScanTable` for `type_id`. Ids below the user range
/// are not used by the compiler yet and are ignored.
pub fn register_type(type_id: u32, table: *const u8) {
    let Some(i) = type_id.checked_sub(USER_TYPE_BASE) else {
        return;
    };
    let i = i as usize;
    let h = heap();
    if i >= h.scan_len {
        let len = (i + 1).next_power_of_two().max(64);
        // SAFETY: realloc of our own table (or null); new tail zeroed.
        unsafe {
            let p = libc::realloc(h.scan_tables.cast(), len * size_of::<*const u8>())
                .cast::<*const u8>();
            if p.is_null() {
                fatal(b"rok runtime: out of memory");
            }
            ptr::write_bytes(p.add(h.scan_len), 0, len - h.scan_len);
            h.scan_tables = p;
            h.scan_len = len;
        }
    }
    // SAFETY: `i < scan_len`.
    unsafe { *h.scan_tables.add(i) = table };
}

fn scan_table(type_id: u32) -> *const u8 {
    let h = heap();
    match type_id.checked_sub(USER_TYPE_BASE) {
        // SAFETY: bounds-checked index into our table.
        Some(i) if (i as usize) < h.scan_len => unsafe { *h.scan_tables.add(i as usize) },
        _ => ptr::null(),
    }
}

/// Sorted addresses of all objects, for [`is_object`].
fn build_index() {
    let h = heap();
    if h.count == 0 {
        return;
    }
    if h.index_cap < h.count {
        let cap = h.count.next_power_of_two();
        // SAFETY: realloc of our own buffer (or null).
        let p = unsafe { libc::realloc(h.index.cast(), cap * size_of::<usize>()) };
        if p.is_null() {
            fatal(b"rok runtime: out of memory (GC object index)");
        }
        h.index = p.cast();
        h.index_cap = cap;
    }
    // SAFETY: the list holds exactly `count` objects; `index` has room.
    unsafe {
        let mut o = h.objects;
        for i in 0..h.count {
            *h.index.add(i) = o as usize;
            o = (*prefix(o)).next;
        }
        core::slice::from_raw_parts_mut(h.index, h.count).sort_unstable();
    }
}

/// The object whose header address is `word` or whose memory contains
/// it (a `str` points at its payload bytes, or into them after slicing).
fn object_containing(word: usize) -> Option<*mut u8> {
    let h = heap();
    if h.count == 0 {
        return None;
    }
    // SAFETY: `build_index` filled `count` entries.
    let index = unsafe { core::slice::from_raw_parts(h.index, h.count) };
    let i = match index.binary_search(&word) {
        Ok(i) => i,
        Err(0) => return None,
        Err(i) => i - 1,
    };
    let start = index[i];
    // SAFETY: `start` is a live object with a prefix.
    let size = unsafe { (*prefix(start as *mut u8)).size };
    (word < start + size).then_some(start as *mut u8)
}

/// Queue the object `word` points into, if any, for marking.
fn push(word: *mut u8, len: &mut usize) {
    let Some(obj) = object_containing(word as usize) else {
        return;
    };
    let h = heap();
    if *len == h.stack_cap {
        let cap = (h.stack_cap * 2).max(1024);
        // SAFETY: realloc of our own stack (or null).
        let p = unsafe { libc::realloc(h.stack.cast(), cap * size_of::<*mut u8>()) };
        if p.is_null() {
            fatal(b"rok runtime: out of memory (GC mark stack)");
        }
        h.stack = p.cast();
        h.stack_cap = cap;
    }
    // SAFETY: `*len < stack_cap`.
    unsafe { *h.stack.add(*len) = obj };
    *len += 1;
}

/// Full stop-the-world collection: mark from this thread's shadow stack
/// and from pinned / immortal objects, then sweep.
#[allow(clippy::cast_ptr_alignment)] // frames, slots and tables are word-aligned
pub fn collect() {
    build_index();
    let mut len = 0;
    // SAFETY: every frame on the chain was linked by compiled code and
    // stays live until its function returns, which is after this call;
    // each slot points at a word inside such a frame's function.
    unsafe {
        let mut f = (*rokr_common::tls::shadow_stack_top()).cast::<Frame>();
        while !f.is_null() {
            let slots = f.add(1).cast::<*const usize>();
            for i in 0..(*f).count {
                push(**slots.add(i) as *mut u8, &mut len);
            }
            f = (*f).prev;
        }
        let mut o = heap().objects;
        while !o.is_null() {
            let flags = (*header(o)).gc_flags.load(Ordering::Relaxed);
            if flags & (FLAG_PINNED | FLAG_IMMORTAL) != 0 {
                push(o, &mut len);
            }
            o = (*prefix(o)).next;
        }
    }
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
                let words = ((*prefix(o)).size - HEADER_SIZE) / size_of::<usize>();
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
    let h = heap();
    let mut link: *mut *mut u8 = &mut h.objects;
    // SAFETY: walks the all-objects list; freed objects are unlinked
    // before their memory is released.
    unsafe {
        while !(*link).is_null() {
            let o = *link;
            let p = prefix(o);
            if (*header(o))
                .gc_flags
                .fetch_and(!FLAG_MARK, Ordering::Relaxed)
                & FLAG_MARK
                != 0
            {
                link = &mut (*p).next;
            } else {
                *link = (*p).next;
                h.count -= 1;
                h.live_bytes -= (*p).size;
                libc::free(o.sub((*p).offset).cast());
            }
        }
    }
    h.next_gc = (h.live_bytes * 2).max(MIN_HEAP);
    h.collections += 1;
}

/// Bytes held by GC objects (headers included) not yet swept.
pub fn live_bytes() -> usize {
    heap().live_bytes
}

pub fn collections() -> u64 {
    heap().collections
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[allow(clippy::cast_ptr_alignment)] // GC objects are 8-aligned
    fn collect_frees_unreachable_and_keeps_traced_children() {
        // 802 table: total 32, version 1, one STRONG_REF at offset 16.
        static TABLE: [u32; 4] = [32, 1 | (1 << 16), 16, STRONG_REF];
        register_type(USER_TYPE_BASE, TABLE.as_ptr().cast());
        let base = live_bytes();
        let a = alloc(32, 8, USER_TYPE_BASE);
        let b = alloc(24, 8, USER_TYPE_BASE + 1); // unregistered: leaf
        let _garbage = alloc(24, 8, USER_TYPE_BASE + 1);
        // SAFETY: `a` has a 16-byte payload; frame layout matches
        // `Frame` + one slot; the frame is unlinked before it dies.
        unsafe {
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
            *frame.1 = 0;
            collect();
            assert_eq!(live_bytes(), base);
            *top = ptr::null_mut();
        }
        scan_words_buffers_and_interior_pointers();
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
}
