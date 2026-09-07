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
//! ponytail: one global lock for heap + registry; a thread allocating
//! takes it on every object. TLABs (702) make the common path lock-free;
//! the lock then only guards block refills and the stop protocol.

use core::cell::UnsafeCell;
use core::mem::size_of;
use core::ptr;
use core::sync::atomic::{AtomicBool, AtomicU8, Ordering};

use rokr_common::tls::{self, MUTATOR_GC_COOPERATING, MUTATOR_PARKED, MUTATOR_RUNNING};

/// One registered mutator thread.
pub struct Mutator {
    next: *mut Mutator,
    /// The owner's TLS slots, published by [`attach`] (null before).
    yield_flag: *const AtomicU8,
    state: *const AtomicU8,
    stack_top: *const *mut u8,
    /// Extra root, alive while the record is registered: a spawned
    /// thread's closure environment (its only reference before the
    /// thread's own frames hold it).
    root: *mut u8,
    /// `rok_tls_worker_id` the spawner chose, written by [`attach`]
    /// (`u64::MAX`: keep the one `thread_init` allocated).
    worker_id: u64,
}

struct World {
    lock: UnsafeCell<libc::pthread_mutex_t>,
    cond: UnsafeCell<libc::pthread_cond_t>,
    threads: UnsafeCell<*mut Mutator>,
}

// SAFETY: `threads` is only touched with `lock` held; the pthread
// objects are designed for shared use.
unsafe impl Sync for World {}

static WORLD: World = World {
    lock: UnsafeCell::new(libc::PTHREAD_MUTEX_INITIALIZER),
    cond: UnsafeCell::new(libc::PTHREAD_COND_INITIALIZER),
    threads: UnsafeCell::new(ptr::null_mut()),
};

/// A stop-the-world pause is requested or running.
static STOP: AtomicBool = AtomicBool::new(false);

fn raw_lock() {
    // SAFETY: statically initialized mutex.
    unsafe { libc::pthread_mutex_lock(WORLD.lock.get()) };
}

/// Release the world lock.
pub fn unlock() {
    // SAFETY: the caller holds the lock.
    unsafe { libc::pthread_mutex_unlock(WORLD.lock.get()) };
}

fn wait() {
    // SAFETY: the caller holds the lock.
    unsafe { libc::pthread_cond_wait(WORLD.cond.get(), WORLD.lock.get()) };
}

fn broadcast() {
    // SAFETY: statically initialized condvar.
    unsafe { libc::pthread_cond_broadcast(WORLD.cond.get()) };
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

/// Take the world lock as a running mutator (heap access, registry
/// changes). Cooperates with a pending stop first.
pub fn lock() {
    raw_lock();
    cooperate();
}

/// `rok_runtime_yield` (804 §8.4.3): the slow path of a safepoint poll.
pub fn safepoint() {
    if STOP.load(Ordering::Acquire) {
        lock();
        unlock();
    }
    tls::yield_flag().store(0, Ordering::Relaxed);
}

/// Before a call that may block (join, sleep, lock wait): this thread
/// counts as stopped until [`leave_native`]. It must not touch GC
/// objects in between except reading words its own frames keep alive.
pub fn enter_native() {
    raw_lock();
    tls::mutator_state().store(MUTATOR_PARKED, Ordering::Release);
    broadcast();
    unlock();
}

/// Back from a blocking call: wait out a running stop, then run again.
pub fn leave_native() {
    raw_lock();
    while STOP.load(Ordering::Relaxed) {
        wait();
    }
    tls::mutator_state().store(MUTATOR_RUNNING, Ordering::Release);
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
        if (*m).worker_id != u64::MAX {
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
                    (*(*m).yield_flag).store(1, Ordering::Release);
                    if (*s).load(Ordering::Acquire) == MUTATOR_RUNNING {
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

/// With the lock held: end the pause and wake every parked mutator.
pub fn resume() {
    STOP.store(false, Ordering::Release);
    // SAFETY: as in `stop`.
    unsafe {
        let mut m = *WORLD.threads.get();
        while !m.is_null() {
            if !(*m).yield_flag.is_null() {
                (*(*m).yield_flag).store(0, Ordering::Relaxed);
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
    }
}
