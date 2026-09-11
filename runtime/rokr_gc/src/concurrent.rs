//! Concurrent marking of full collections (705): snapshot at the
//! beginning (SATB, Yuasa), one marker thread.
//!
//! - Start (a pause, [`start`]): a minor collection first, so every
//!   survivor is old: block objects `UNLOGGED`, LOS objects `CARDED`
//!   (they get `UNLOGGED` too here) and no line is `TAKEN`. Then the
//!   roots and pins are queued and the marker thread wakes.
//! - Marking: mutators run. Refills hand out `BLACK` lines and new LOS
//!   objects go in front of `los_mark_head`: what is allocated now is
//!   younger than the mark, which never reads or sweeps it (allocate
//!   black). The first store into an old object goes through
//!   `rok_gc_wb_slow` (it is `UNLOGGED`), which here also logs every
//!   reference the object holds into the thread's SATB chunk
//!   ([`snapshot`]) before clearing `UNLOGGED`, so nothing reachable at
//!   the start is lost; later stores only overwrite values stored during
//!   the mark, which were reachable at the start or are new. The object
//!   also joins the remembered set (block objects) or dirties its card
//!   (LOS), as references to the new, young objects must survive the
//!   next minor collection. An object the marker already scanned
//!   (`SCANNED`) logs nothing.
//! - Finish (a pause, [`finish`]): when the marker runs out of work, or
//!   when the allocation budget runs out first (no minor collection
//!   runs during a mark), the world stops: every thread's SATB chunk is
//!   drained, the roots are queued again, the mark completes, the
//!   snapshot is swept (`BLACK` lines become `TAKEN`: young) and the
//!   remembered set of the mark (its surviving objects) carries over to
//!   the next minor collection. No evacuation: if the heap is
//!   fragmented, the next full collection stops the world for it.
//!
//! The mark state ([`super::Mark`]) belongs to whoever holds the mark
//! lock: the marker thread while it marks, a pause otherwise (it asks
//! the marker to let go through [`FINISH`]). The marker never holds the
//! mark lock while it waits for the world lock.

use core::cell::UnsafeCell;
use core::sync::atomic::{AtomicBool, AtomicPtr, AtomicU64, Ordering};
use core::{ptr, ptr::null_mut};

use super::{
    FLAG_LARGE, FLAG_SATB, FLAG_SCANNED, FLAG_UNLOGGED, LOG_FULL, LogChunk, MARKER_CPU_NS,
    MIN_HEAP, Pause, build_index, clock_ns, drain, for_each_logged, for_each_ref, free_logs,
    header, heap, load_word, log_word, mark, mark_roots, prefix, push, push_chunks,
    release_free_blocks, retire_log, retire_to, select_candidates, sweep_blocks, sweep_los, world,
};
use rokr_common::object_header::{FLAG_CARDED, FLAG_MARK};

/// A concurrent mark runs: the barrier slow path snapshots.
pub static MARKING: AtomicBool = AtomicBool::new(false);
/// Retired SATB chunks (reference words to mark).
static SATB_FULL: AtomicPtr<LogChunk> = AtomicPtr::new(null_mut());
/// A pause waits for the mark lock: the marker lets go.
static FINISH: AtomicBool = AtomicBool::new(false);
/// The marker has a mark to work on (under the mark lock).
static ACTIVE: AtomicBool = AtomicBool::new(false);
/// The running mark (`Heap::cycles`), so the marker finishes only its own.
static CYCLE: AtomicU64 = AtomicU64::new(0);
static SPAWNED: AtomicBool = AtomicBool::new(false);

struct Lock {
    mutex: UnsafeCell<libc::pthread_mutex_t>,
    cond: UnsafeCell<libc::pthread_cond_t>,
}

// SAFETY: pthread objects are designed for shared use.
unsafe impl Sync for Lock {}

/// The mark lock (guards [`super::Mark`]) and its condvar (the marker
/// waits on it for a mark).
static MARK_LOCK: Lock = Lock {
    mutex: UnsafeCell::new(libc::PTHREAD_MUTEX_INITIALIZER),
    cond: UnsafeCell::new(libc::PTHREAD_COND_INITIALIZER),
};

fn raw_lock() {
    // SAFETY: statically initialized mutex.
    unsafe { libc::pthread_mutex_lock(MARK_LOCK.mutex.get()) };
}

/// Release the mark lock.
pub fn unlock_mark() {
    // SAFETY: the caller holds it.
    unsafe { libc::pthread_mutex_unlock(MARK_LOCK.mutex.get()) };
}

/// Take the mark lock from the marker (a pause).
pub fn lock_mark() {
    FINISH.store(true, Ordering::Relaxed);
    raw_lock();
    FINISH.store(false, Ordering::Relaxed);
}

fn wait() {
    // SAFETY: the caller holds the mutex.
    unsafe { libc::pthread_cond_wait(MARK_LOCK.cond.get(), MARK_LOCK.mutex.get()) };
}

fn broadcast() {
    // SAFETY: statically initialized condvar.
    unsafe { libc::pthread_cond_broadcast(MARK_LOCK.cond.get()) };
}

/// Retire a thread's SATB chunk.
pub fn retire_satb(slots: [*mut usize; 2]) {
    retire_to(slots, &SATB_FULL);
}

/// Queue every word of the retired SATB chunks; whether there was any.
fn take_satb() -> bool {
    let log = SATB_FULL.swap(null_mut(), Ordering::Acquire);
    for_each_logged(log, |w| push(w as usize, false));
    free_logs(log);
    !log.is_null()
}

/// In the pause after a minor collection (world stopped, mark lock
/// held): start a concurrent mark of everything that survived it.
pub fn start() {
    let h = heap();
    h.marking = true;
    h.los_mark_head = h.los;
    h.mark_start_live = h.live_bytes;
    h.cycles += 1;
    CYCLE.store(h.cycles, Ordering::Relaxed);
    // Old LOS objects: the first store into one snapshots it too (then
    // marks its card as always).
    // SAFETY: walks the LOS list.
    unsafe {
        let mut o = h.los;
        while !o.is_null() {
            let flags = &(*header(o)).gc_flags;
            if flags.load(Ordering::Relaxed) & FLAG_CARDED != 0 {
                flags.fetch_or(FLAG_UNLOGGED, Ordering::Relaxed);
            }
            o = (*prefix(o)).next;
        }
    }
    build_index();
    let m = mark();
    (m.full, m.concurrent, m.evacuating, m.len) = (true, true, false, 0);
    mark_roots(false);
    MARKING.store(true, Ordering::Relaxed);
    ACTIVE.store(true, Ordering::Relaxed);
    if !SPAWNED.swap(true, Ordering::Relaxed) {
        spawn_marker();
    }
    broadcast();
}

fn spawn_marker() {
    // SAFETY: plain pthread calls; the thread runs for the rest of the
    // process.
    unsafe {
        let mut t: libc::pthread_t = core::mem::zeroed();
        if libc::pthread_create(&mut t, ptr::null(), marker, null_mut()) != 0 {
            rokr_common::fatal(b"rok runtime: cannot start the GC marker thread");
        }
        libc::pthread_detach(t);
    }
}

/// The marker thread: drains the mark stack and the retired SATB chunks
/// while mutators run, then stops the world to finish.
extern "C" fn marker(_: *mut libc::c_void) -> *mut libc::c_void {
    raw_lock();
    loop {
        while !ACTIVE.load(Ordering::Relaxed) {
            wait();
        }
        let cycle = CYCLE.load(Ordering::Relaxed);
        let c0 = clock_ns(libc::CLOCK_THREAD_CPUTIME_ID);
        let done = loop {
            drain(256);
            if FINISH.load(Ordering::Relaxed) {
                break false;
            }
            if mark().len == 0 && !take_satb() {
                break true;
            }
        };
        MARKER_CPU_NS.fetch_add(
            clock_ns(libc::CLOCK_THREAD_CPUTIME_ID) - c0,
            Ordering::Relaxed,
        );
        if done {
            unlock_mark();
            world::lock();
            let h = heap();
            if h.marking && h.cycles == cycle {
                finish(false);
            }
            world::unlock();
            raw_lock();
        } else {
            // A pause takes the lock; wait it out.
            wait();
        }
    }
}

/// With the world lock held, during a concurrent mark: stop the world
/// and finish it. `forced`: the allocation budget ran out first.
pub fn finish(forced: bool) {
    let p = Pause::begin();
    world::for_each_satb(retire_satb);
    // Roots stored since the start need no marking (they were reachable
    // then or are new); queueing them again is cheap and robust.
    mark_roots(false);
    loop {
        drain(usize::MAX);
        if !take_satb() {
            break;
        }
    }
    // The objects stored into during the mark stay remembered (they may
    // reference new, young objects): the survivors among them.
    world::for_each_wb_log(retire_log);
    let log = LOG_FULL.swap(null_mut(), Ordering::Acquire);
    let last = keep_marked(log);
    MARKING.store(false, Ordering::Relaxed);
    ACTIVE.store(false, Ordering::Relaxed);
    mark().concurrent = false;
    let h = heap();
    h.marking = false;
    let survived = sweep_blocks(true) + sweep_los(true, true);
    for_each_logged(log, |o| {
        // SAFETY: a survivor (its sweep set `UNLOGGED` again).
        unsafe {
            (*header(o))
                .gc_flags
                .fetch_and(!FLAG_UNLOGGED, Ordering::Relaxed)
        };
    });
    if !log.is_null() {
        push_chunks(&LOG_FULL, log, last);
    }
    let h = heap();
    if select_candidates() {
        // Fragmented: the next full collection stops the world and
        // evacuates (fixing references needs every slot stable).
        // SAFETY: `nblocks` initialized metas.
        for m in unsafe { core::slice::from_raw_parts_mut(h.meta, h.nblocks) } {
            m.evac = false;
        }
        h.stw_next = true;
    }
    let allocated = h.live_bytes - h.mark_start_live;
    h.old_bytes = survived;
    h.live_bytes = survived + allocated;
    h.next_gc = (survived * 2).max(MIN_HEAP);
    h.full_at = h.next_gc;
    h.small_cursor = 0;
    h.medium_cursor = 0;
    h.collections += 1;
    h.forced += u64::from(forced);
    release_free_blocks();
    p.end(true);
}

/// Drop the unmarked (dead) objects from the chunk list `log`, in place;
/// its last chunk (null if empty).
fn keep_marked(mut log: *mut LogChunk) -> *mut LogChunk {
    let mut last = null_mut();
    // SAFETY: retired chunks hold objects up to their `end`.
    unsafe {
        while !log.is_null() {
            let first = log.add(1).cast::<*mut u8>();
            let (mut r, mut w) = (first, first);
            while (r as usize) < (*log).end {
                if (*header(*r)).gc_flags.load(Ordering::Relaxed) & FLAG_MARK != 0 {
                    *w = *r;
                    w = w.add(1);
                }
                r = r.add(1);
            }
            (*log).end = w as usize;
            last = log;
            log = (*log).next;
        }
    }
    last
}

/// The barrier slow path while a concurrent mark runs: the first store
/// into the old object `obj` logs every reference it holds (unless the
/// marker scanned it already) and remembers `obj`; a racing store waits
/// until that is done, so no value is overwritten before it is logged.
///
/// # Safety
/// `obj` must be a live GC object about to be stored into.
pub unsafe fn snapshot(obj: *mut u8) {
    // SAFETY: caller contract.
    let flags = unsafe { &(*header(obj)).gc_flags };
    let f = flags.fetch_or(FLAG_SATB, Ordering::Acquire);
    if f & FLAG_SATB != 0 {
        while flags.load(Ordering::Acquire) & FLAG_UNLOGGED != 0 {
            core::hint::spin_loop();
        }
        return;
    }
    if f & FLAG_UNLOGGED == 0 {
        return;
    }
    if f & FLAG_SCANNED == 0 {
        let slots = rokr_common::tls::satb_log();
        for_each_ref(obj, 0, usize::MAX, |off, _| {
            // SAFETY: a reference word inside `obj`.
            let w = load_word(unsafe { obj.add(off) });
            if w != 0 {
                log_word(slots, &SATB_FULL, w);
            }
        });
    }
    if f & FLAG_LARGE == 0 {
        log_word(rokr_common::tls::wb_log(), &LOG_FULL, obj as usize);
    }
    flags.fetch_and(!FLAG_UNLOGGED, Ordering::Release);
}
