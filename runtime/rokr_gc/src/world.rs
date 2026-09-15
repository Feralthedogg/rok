//! Thread registry and stop-the-world (008-abi/804).
//!
//! One process-wide "world lock" guards the heap, the registry and the
//! stop protocol. A collector holds it, sets `STOP`, raises every other
//! mutator's `rok_tls_yield_flag` and waits on the world condvar until
//! each one is out of `RUNNING`:
//!
//! - `GC_COOPERATING`: parked in [`safepoint`] (compiled code polls the
//!   flag at function entry and loop back-edges), or blocked on the world
//!   lock itself (taking it means cooperating first, see [`lock`]);
//! - `PARKED`: inside a blocking runtime call bracketed by
//!   [`enter_native`] / [`leave_native`] (804 §8.4.10). Leaving waits
//!   out a running stop, so a parked thread never touches the heap
//!   mid-collection;
//! - not attached yet (spawned, not started): its state slot is unknown.
//!
//! Then every registered thread's shadow-stack chain is a root set.
//!
//! TLABs (702) keep allocation off the lock: it guards block refills,
//! the registry and the stop protocol.

use core::cell::UnsafeCell;
use core::mem::size_of;
use core::ptr;
use core::sync::atomic::{AtomicBool, AtomicU8, Ordering};

use rokr_common::sys;
use rokr_common::tls::{self, MUTATOR_GC_COOPERATING, MUTATOR_PARKED, MUTATOR_RUNNING};

/// One registered mutator thread.
pub struct Mutator {
    next: *mut Mutator,
    /// The owner's TLS slots, published by [`attach`] (null before).
    yield_flag: *const AtomicU8,
    state: *const AtomicU8,
    stack_top: *const *mut u8,
    /// `rok_tls_tlab_cursor` / `rok_tls_tlab_limit`: a collection empties
    /// every thread's TLAB (its unused tail is reclaimed by the sweep).
    tlab: [*mut usize; 2],
    /// `rok_tls_wb_log_cursor` / `_limit`: a collection retires every
    /// thread's remembered-set chunk.
    wb_log: [*mut usize; 2],
    /// `rok_tls_satb_cursor` / `_limit`: the final pause of a concurrent
    /// mark retires every thread's SATB chunk.
    satb: [*mut usize; 2],
    /// Extra root, alive while the record is registered: a spawned
    /// thread's closure environment (its only reference before the
    /// thread's own frames hold it).
    root: *mut u8,
    /// `rok_tls_worker_id` the spawner chose, written by [`attach`]
    /// (`u64::MAX`: keep the one `thread_init` allocated, then record it).
    worker_id: u64,
}

struct World {
    lock: sys::Lock,
    cond: sys::Cond,
    threads: UnsafeCell<*mut Mutator>,
}

// SAFETY: `threads` is only touched with `lock` held.
unsafe impl Sync for World {}

static WORLD: World = World {
    lock: sys::Lock::new(),
    cond: sys::Cond::new(),
    threads: UnsafeCell::new(ptr::null_mut()),
};

/// A stop-the-world pause is requested or running.
static STOP: AtomicBool = AtomicBool::new(false);

/// The process is exiting ([`halt`]): no thread runs rok code again.
static HALT: AtomicBool = AtomicBool::new(false);

/// `rok_runtime_shutdown` (805 §8.5.2): no other thread runs rok code
/// again.
///
/// The worker pool and threads still running stop for good at their
/// next safepoint or world-lock acquisition; one inside runtime or C
/// code finishes that first, so it releases the locks the exit path
/// needs. The caller is done with rok code and counts as stopped.
pub fn halt() {
    raw_lock();
    HALT.store(true, Ordering::SeqCst);
    // SAFETY: registry guarded by the lock.
    unsafe {
        let mut m = *WORLD.threads.get();
        while !m.is_null() {
            if !(*m).yield_flag.is_null() {
                (*(*m).yield_flag).fetch_or(tls::YIELD_STOP, Ordering::SeqCst);
            }
            m = (*m).next;
        }
    }
    tls::mutator_state().store(MUTATOR_PARKED, Ordering::SeqCst);
    unlock();
}

fn raw_lock() {
    WORLD.lock.lock();
}

/// Release the world lock.
pub fn unlock() {
    WORLD.lock.unlock();
}

fn wait() {
    WORLD.cond.wait(&WORLD.lock);
}

fn broadcast() {
    WORLD.cond.broadcast();
}

/// With the lock held: if another thread is stopping the world, park
/// here (state `GC_COOPERATING`, our frames are its roots) until it is
/// done.
fn cooperate() {
    if !STOP.load(Ordering::Relaxed) {
        return;
    }
    let state = tls::mutator_state();
    let prev = state.load(Ordering::Relaxed);
    state.store(MUTATOR_GC_COOPERATING, Ordering::Release);
    broadcast();
    while STOP.load(Ordering::Relaxed) {
        wait();
    }
    state.store(prev, Ordering::Release);
}

/// [`lock`] for an `atexit` handler: after [`halt`] it takes the lock
/// instead of parking for good.
pub fn lock_at_exit() {
    if HALT.load(Ordering::SeqCst) {
        raw_lock();
    } else {
        lock();
    }
}

/// Take the world lock as a running mutator (heap access, registry
/// changes). Cooperates with a pending stop first.
pub fn lock() {
    raw_lock();
    if HALT.load(Ordering::Relaxed) {
        unlock();
        sys::park_forever();
    }
    cooperate();
}

/// `rok_runtime_yield` (804 §8.4.3): the slow path of a safepoint poll.
pub fn safepoint() {
    if HALT.load(Ordering::Relaxed) {
        sys::park_forever();
    }
    lock();
    // Under the lock, as a stopper raises the flag: cleared outside it,
    // a request raised just after this thread's pause would be lost and
    // its next `enter_native` would not wake that stopper.
    tls::yield_flag().fetch_and(!tls::YIELD_STOP, Ordering::Relaxed);
    unlock();
}

/// Before a call that may block: this thread counts as stopped until
/// [`leave_native`].
///
/// Join, sleep, lock wait, any `extern "C"` call. It must not touch GC
/// objects in between except reading words its own frames keep alive.
///
/// Lock-free unless a stop is pending: [`stop`] raises the yield flag
/// before reading the state, we write the state before reading the
/// flag (both `SeqCst`), so either it sees `PARKED` or we see the flag
/// and wake it.
pub fn enter_native() {
    tls::mutator_state().store(MUTATOR_PARKED, Ordering::SeqCst);
    if tls::yield_flag().load(Ordering::SeqCst) != 0 {
        raw_lock();
        broadcast();
        unlock();
    }
}

/// Back from a blocking call: wait out a running stop, then run again.
///
/// Lock-free unless a stop is pending (the same handshake as
/// [`enter_native`]: a stopper that read `RUNNING` raised our flag
/// first, one that read `PARKED` too).
pub fn leave_native() {
    let state = tls::mutator_state();
    state.store(MUTATOR_RUNNING, Ordering::SeqCst);
    if tls::yield_flag().load(Ordering::SeqCst) == 0 {
        return;
    }
    state.store(MUTATOR_PARKED, Ordering::SeqCst);
    raw_lock();
    broadcast();
    while STOP.load(Ordering::Relaxed) {
        wait();
    }
    state.store(MUTATOR_RUNNING, Ordering::Release);
    // Halted: the next safepoint stops this thread.
    if !HALT.load(Ordering::Relaxed) {
        tls::yield_flag().fetch_and(!tls::YIELD_STOP, Ordering::Relaxed);
    }
    unlock();
}

/// Register a thread that is about to be spawned, keeping `root` alive
/// until it detaches. It counts as stopped until it [`attach`]es.
pub fn register(root: *mut u8, worker_id: u64) -> *mut Mutator {
    // SAFETY: plain allocation.
    let m = unsafe { libc::malloc(size_of::<Mutator>()) }.cast::<Mutator>();
    if m.is_null() {
        rokr_common::oom();
    }
    lock();
    // SAFETY: `m` is fresh; the registry is guarded by the lock.
    unsafe {
        m.write(Mutator {
            next: *WORLD.threads.get(),
            yield_flag: ptr::null(),
            state: ptr::null(),
            stack_top: ptr::null(),
            tlab: [ptr::null_mut(); 2],
            wb_log: [ptr::null_mut(); 2],
            satb: [ptr::null_mut(); 2],
            root,
            worker_id,
        });
        *WORLD.threads.get() = m;
    }
    unlock();
    m
}

/// On the registered thread itself (TLS already initialized): publish
/// its TLS slots and start running as a mutator.
///
/// # Safety
/// `m` must come from [`register`] and not be attached or unregistered.
pub unsafe fn attach(m: *mut Mutator) {
    raw_lock();
    while STOP.load(Ordering::Relaxed) {
        wait();
    }
    tls::mutator_state().store(MUTATOR_RUNNING, Ordering::Release);
    // SAFETY: `m` is registered and only its owner writes these fields,
    // under the lock the collector reads them with.
    unsafe {
        (*m).yield_flag = tls::yield_flag();
        (*m).state = tls::mutator_state();
        (*m).stack_top = tls::shadow_stack_top();
        (*m).tlab = tls::tlab();
        (*m).wb_log = tls::wb_log();
        (*m).satb = tls::satb_log();
        if (*m).worker_id == u64::MAX {
            (*m).worker_id = tls::worker_id().read();
        } else {
            tls::worker_id().write((*m).worker_id);
        }
    }
    unlock();
}

/// Register and attach the calling thread (the main thread, or a thread
/// that calls `rok_thread_init` itself). No-op if already registered.
pub fn attach_current() {
    raw_lock();
    let registered = !find_current().is_null();
    unlock();
    if !registered {
        // SAFETY: a fresh record.
        unsafe { attach(register(ptr::null_mut(), u64::MAX)) };
    }
}

/// With the lock held: this thread's record, or null.
fn find_current() -> *mut Mutator {
    let me = tls::shadow_stack_top().cast_const();
    // SAFETY: the registry is guarded by the caller's lock.
    unsafe {
        let mut m = *WORLD.threads.get();
        while !m.is_null() && (*m).stack_top != me {
            m = (*m).next;
        }
        m
    }
}

/// Remove the calling thread from the registry (`rok_thread_shutdown`).
/// It must not touch GC objects afterwards.
pub fn detach() {
    lock();
    crate::retire_own_logs();
    let me = find_current();
    // SAFETY: registry guarded by the lock; `me` came from `register`.
    unsafe {
        let mut link: *mut *mut Mutator = WORLD.threads.get();
        while !(*link).is_null() {
            if *link == me {
                *link = (*me).next;
                libc::free(me.cast());
                break;
            }
            link = &raw mut (**link).next;
        }
    }
    unlock();
}

/// Unregister a record whose thread never started (spawn failed).
///
/// # Safety
/// `m` must come from [`register`] and its thread never have started.
pub unsafe fn unregister(m: *mut Mutator) {
    lock();
    // SAFETY: as in `detach`.
    unsafe {
        let mut link: *mut *mut Mutator = WORLD.threads.get();
        while !(*link).is_null() {
            if *link == m {
                *link = (*m).next;
                libc::free(m.cast());
                break;
            }
            link = &raw mut (**link).next;
        }
    }
    unlock();
}

/// With the lock held (taken by [`lock`]): stop every other registered
/// mutator. Returns once all of them are out of `RUNNING`.
pub fn stop() {
    STOP.store(true, Ordering::Release);
    let me = tls::mutator_state().as_ptr().cast_const();
    loop {
        let mut running = false;
        // SAFETY: registry guarded by the lock; published TLS slots stay
        // valid while their thread is registered.
        unsafe {
            let mut m = *WORLD.threads.get();
            while !m.is_null() {
                let s = (*m).state;
                if !s.is_null() && s.cast::<u8>() != me {
                    // `SeqCst`: the handshake of `enter_native`.
                    (*(*m).yield_flag).fetch_or(tls::YIELD_STOP, Ordering::SeqCst);
                    if (*s).load(Ordering::SeqCst) == MUTATOR_RUNNING {
                        running = true;
                    }
                }
                m = (*m).next;
            }
        }
        if !running {
            return;
        }
        wait();
    }
}

/// With the world stopped: empty every registered thread's TLAB (and
/// the caller's, registered or not), so the sweep may hand its unused
/// lines to anyone.
pub fn reset_tlabs() {
    // SAFETY: as in `stop`; the slots are only written by their owner,
    // which is stopped, and by us.
    unsafe {
        let mut m = *WORLD.threads.get();
        while !m.is_null() {
            for p in (*m).tlab {
                if !p.is_null() {
                    p.write(0);
                }
            }
            m = (*m).next;
        }
        for p in tls::tlab() {
            p.write(0);
        }
    }
}

/// With the world stopped: `f` on the wb log slots of every registered
/// thread and the caller's (registered or not).
pub fn for_each_wb_log(mut f: impl FnMut([*mut usize; 2])) {
    // SAFETY: as in `reset_tlabs`.
    unsafe {
        let mut m = *WORLD.threads.get();
        while !m.is_null() {
            if !(*m).wb_log[0].is_null() {
                f((*m).wb_log);
            }
            m = (*m).next;
        }
    }
    f(tls::wb_log());
}

/// With the world stopped: `f` on the SATB log slots of every registered
/// thread and the caller's.
pub fn for_each_satb(mut f: impl FnMut([*mut usize; 2])) {
    // SAFETY: as in `reset_tlabs`.
    unsafe {
        let mut m = *WORLD.threads.get();
        while !m.is_null() {
            if !(*m).satb[0].is_null() {
                f((*m).satb);
            }
            m = (*m).next;
        }
    }
    f(tls::satb_log());
}

/// With the lock held: end the pause and wake every parked mutator.
pub fn resume() {
    STOP.store(false, Ordering::Release);
    // SAFETY: as in `stop`.
    unsafe {
        let mut m = *WORLD.threads.get();
        while !m.is_null() {
            if !(*m).yield_flag.is_null() {
                (*(*m).yield_flag).fetch_and(!tls::YIELD_STOP, Ordering::Relaxed);
            }
            m = (*m).next;
        }
    }
    broadcast();
}

/// With the world stopped: call `f` with the address of every root word
/// of every registered thread (shadow-stack slots, spawn roots).
#[allow(clippy::cast_ptr_alignment)] // frames and slots are word-aligned
pub fn for_each_root(mut f: impl FnMut(*mut u8)) {
    #[repr(C)]
    struct Frame {
        prev: *mut Frame,
        count: usize,
        // `slots: [*mut usize; count]` follows.
    }
    // SAFETY: every frame on a stopped thread's chain was linked by
    // compiled code and stays live until its function returns, which
    // cannot happen while the thread is stopped; each slot points at a
    // word inside such a function's frame.
    unsafe {
        let mut m = *WORLD.threads.get();
        while !m.is_null() {
            if !(*m).root.is_null() {
                f((*m).root);
            }
            if !(*m).stack_top.is_null() {
                let mut fr = (*(*m).stack_top).cast::<Frame>();
                while !fr.is_null() {
                    let slots = fr.add(1).cast::<*const usize>();
                    for i in 0..(*fr).count {
                        f(**slots.add(i) as *mut u8);
                    }
                    fr = (*fr).prev;
                }
            }
            m = (*m).next;
        }
        let g = &*GLOBAL_ROOTS.0.get();
        for i in 0..g.len {
            f(*(*g.words.add(i)) as *mut u8);
        }
    }
}

/// Addresses of words outside any stack that hold GC references
/// (statics), scanned by every collection.
struct GlobalRoots {
    words: *mut *const usize,
    len: usize,
    cap: usize,
}

struct GlobalRootsCell(UnsafeCell<GlobalRoots>);
// SAFETY: only touched with the world lock held.
unsafe impl Sync for GlobalRootsCell {}

static GLOBAL_ROOTS: GlobalRootsCell = GlobalRootsCell(UnsafeCell::new(GlobalRoots {
    words: ptr::null_mut(),
    len: 0,
    cap: 0,
}));

/// Make the word at `word` a root for the rest of the process.
pub fn add_root(word: *const usize) {
    lock();
    // SAFETY: guarded by the lock; realloc of our own buffer.
    unsafe {
        let g = &mut *GLOBAL_ROOTS.0.get();
        if g.len == g.cap {
            let cap = (g.cap * 2).max(16);
            let p = libc::realloc(g.words.cast(), cap * size_of::<*const usize>());
            if p.is_null() {
                rokr_common::oom();
            }
            g.words = p.cast();
            g.cap = cap;
        }
        *g.words.add(g.len) = word;
        g.len += 1;
    }
    unlock();
}
