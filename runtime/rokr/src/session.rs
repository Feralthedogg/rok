//! For the REPL's session host (`rokc_tools/src/repl_host.c`): stop the
//! world at a quiet moment to save the session before a cell, and put
//! the runtime back together after a failed cell restored it with some
//! threads gone (POSIX: a forked copy keeps only the main thread;
//! Windows: threads the host ended).
//!
//! Quiet: no executor thread is inside a poll, a blocking job or its own
//! bookkeeping (each passes a `rok_session_*` gate between them), and no
//! thread is stopped inside a critical section. A gone thread was
//! therefore between steps whose state is all in memory, so executor
//! threads restart where they were and its locks are released.

use core::sync::atomic::{AtomicBool, AtomicI32, AtomicPtr, AtomicUsize, Ordering};

use rokr_common::object_header::HEADER_SIZE;
use rokr_common::{sys, tls};
use rokr_gc::world;

/// A hold is requested: executor threads wait at their gates.
static HOLD: AtomicBool = AtomicBool::new(false);
/// Executor threads between their gates.
static BUSY: AtomicUsize = AtomicUsize::new(0);
/// Lock notes are kept: a session host saves sessions.
static NOTES: AtomicBool = AtomicBool::new(false);

/// Whether locks are to be noted (`rok_lock_note`): 1 in a session host
/// (it is, from before its first cell). `rok::core::sync` reads it once
/// per process (a lazy static), so other programs pay a load per lock.
#[unsafe(no_mangle)]
pub extern "C" fn rok_lock_notes() -> i32 {
    i32::from(NOTES.load(Ordering::SeqCst))
}

struct Gate {
    lock: sys::Lock,
    cond: sys::Cond,
}

// SAFETY: the OS primitives are thread-safe.
unsafe impl Sync for Gate {}

static GATE: Gate = Gate {
    lock: sys::Lock::new(),
    cond: sys::Cond::new(),
};

fn gate_broadcast() {
    GATE.lock.lock();
    GATE.cond.broadcast();
    GATE.lock.unlock();
}

/// Wait out a hold, parked for the collector.
fn gate_wait() {
    world::enter_native();
    GATE.lock.lock();
    while HOLD.load(Ordering::SeqCst) {
        GATE.cond.wait(&GATE.lock);
    }
    GATE.lock.unlock();
    world::leave_native();
}

/// An executor thread starts work (a loop of polls, jobs, scans): it
/// counts as busy until [`rok_session_leave`]; waits out a hold first.
#[unsafe(no_mangle)]
pub extern "C" fn rok_session_enter() {
    loop {
        BUSY.fetch_add(1, Ordering::SeqCst);
        if !HOLD.load(Ordering::SeqCst) {
            return;
        }
        rok_session_leave();
        gate_wait();
    }
}

/// An executor thread stops working (it sleeps, blocks for its next
/// work, or ends).
#[unsafe(no_mangle)]
pub extern "C" fn rok_session_leave() {
    if BUSY.fetch_sub(1, Ordering::SeqCst) == 1 && HOLD.load(Ordering::SeqCst) {
        gate_broadcast();
    }
}

/// A busy executor thread between two steps (it holds no lock and runs
/// no poll or job): wait here while a hold is requested.
#[unsafe(no_mangle)]
pub extern "C" fn rok_session_pass() {
    if HOLD.load(Ordering::SeqCst) {
        rok_session_leave();
        rok_session_enter();
    }
}

/// Bring the session to a quiet moment and stop every other mutator
/// there: 1 once stopped (end it with [`rok_session_resume`]); 0 if that
/// took longer than `timeout_ns` (the hold stays requested: call again,
/// or give up with [`rok_session_unhold`]).
#[unsafe(no_mangle)]
pub extern "C" fn rok_session_hold(timeout_ns: i64) -> i32 {
    NOTES.store(true, Ordering::SeqCst);
    HOLD.store(true, Ordering::SeqCst);
    let deadline = sys::monotonic_ns().saturating_add(timeout_ns);
    loop {
        if BUSY.load(Ordering::SeqCst) == 0 {
            world::lock();
            world::stop();
            if world::quiet() {
                return 1;
            }
            world::resume();
            world::unlock();
        }
        let left = deadline - sys::monotonic_ns();
        if left <= 0 {
            return 0;
        }
        // Woken when the last busy thread passes its gate; a lock holder
        // is looked at again each millisecond.
        world::enter_native();
        GATE.lock.lock();
        GATE.cond
            .wait_timeout(&GATE.lock, left.min(1_000_000) as u64);
        GATE.lock.unlock();
        world::leave_native();
    }
}

/// End a hold: the session was saved (or [`rok_session_hold`] gave up).
#[unsafe(no_mangle)]
pub extern "C" fn rok_session_unhold() {
    HOLD.store(false, Ordering::SeqCst);
    gate_broadcast();
}

/// End [`rok_session_hold`]'s stop and the hold.
#[unsafe(no_mangle)]
pub extern "C" fn rok_session_resume() {
    world::resume();
    world::unlock();
    rok_session_unhold();
}

/// Lock kinds of [`rok_lock_note`].
const MUTEX: usize = 0;
const READ: usize = 1;
const WRITE: usize = 2;
const ONCE: usize = 3;

/// The calling thread took the lock whose state word is element 0 of
/// the `GcBuf<i32>` `buf` (`kind`: 0 `Mutex`, 1 `RwLock` read, 2 write,
/// 3 a running `Once`). Noted (1) only in a session host and outside
/// the task executor (a task outlives its threads); the guard passes
/// the 1 to [`rok_lock_drop`].
///
/// # Safety
/// `buf` must be a live `GcBuf<i32>`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_lock_note(buf: *mut u8, kind: i32) -> i32 {
    // SAFETY: this thread's own slot.
    if !NOTES.load(Ordering::Relaxed) || unsafe { tls::task_worker().read() } != 0 {
        return 0;
    }
    // Released by address after a failed cell: it must stay put.
    // SAFETY: caller contract.
    unsafe { rokr_gc::no_move(buf) };
    world::note_lock(buf as usize, kind as usize);
    1
}

/// The lock [`rok_lock_note`] noted is released.
#[unsafe(no_mangle)]
pub extern "C" fn rok_lock_drop(buf: *mut u8) {
    world::drop_lock(buf as usize);
}

/// Release a lock a gone thread held, as its guard's drop would.
#[allow(clippy::cast_ptr_alignment)] // i32 buffer elements are 4-aligned
fn release((buf, kind): (usize, usize)) {
    // SAFETY: the lock's buffer is alive (the gone thread's frames were
    // roots until now) and was kept in place (`rok_lock_note`).
    let w = unsafe { &*(buf as *mut u8).add(HEADER_SIZE).cast::<AtomicI32>() };
    match kind {
        MUTEX | WRITE => w.store(0, Ordering::SeqCst),
        READ => {
            w.fetch_sub(1, Ordering::SeqCst);
        }
        ONCE => {
            let _ = w.compare_exchange(1, 0, Ordering::SeqCst, Ordering::SeqCst);
        }
        _ => {}
    }
}

/// With the world stopped: the OS ids of the other mutator threads into
/// `out` (up to `cap`); how many there are.
///
/// # Safety
/// `out` must be writable for `cap` ids.
#[cfg(windows)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_world_threads(out: *mut u64, cap: usize) -> usize {
    // SAFETY: caller contract.
    world::other_thread_ids(unsafe { core::slice::from_raw_parts_mut(out, cap) })
}

/// Worker ids of threads [`rok_session_restored`] found gone (a
/// `malloc`'d array, replaced as it grows), and their count.
static LOST: AtomicPtr<u64> = AtomicPtr::new(core::ptr::null_mut());
static NLOST: AtomicUsize = AtomicUsize::new(0);

fn note_lost(id: u64) {
    let n = NLOST.load(Ordering::Relaxed);
    let old = LOST.load(Ordering::Relaxed);
    if n.is_power_of_two() || n == 0 {
        // SAFETY: plain reallocation of our own array.
        let new =
            unsafe { libc::realloc(old.cast(), (n.max(1) * 2) * size_of::<u64>()) }.cast::<u64>();
        if new.is_null() {
            rokr_common::oom();
        }
        LOST.store(new, Ordering::Relaxed);
    }
    // SAFETY: room for `n + 1` ids.
    unsafe { LOST.load(Ordering::Relaxed).add(n).write(id) };
    NLOST.store(n + 1, Ordering::Release);
}

/// The session was put back as it was before a failed cell, the world
/// resumed: forget the threads that are gone (`n == usize::MAX`: every
/// other one; else the OS ids at `lost`) and release the locks they
/// held, drop the I/O poller's state and let the task executor restart
/// its threads.
///
/// # Safety
/// `lost` must be readable for `n` ids unless `n` is `usize::MAX`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_session_restored(lost: *const u64, n: usize) {
    let lost = (n != usize::MAX)
        // SAFETY: caller contract.
        .then(|| unsafe { core::slice::from_raw_parts(lost, n) });
    world::forget(lost, |id, held| {
        note_lost(id);
        held.iter().copied().for_each(release);
    });
    crate::thread::forget_waiters(|id| rok_thread_lost(id) != 0);
    // Threads waiting on a lock released above (and any other: a wait
    // may end spuriously) look again; tasks are unparked by the
    // executor's restart.
    crate::thread::wake_all_waiters();
    crate::net::reset_poller();
    crate::restart_executor();
}

/// Whether the thread with worker id `id` (`rok_thread_new_id`) was
/// found gone after a failed REPL cell: 1 if so.
#[unsafe(no_mangle)]
pub extern "C" fn rok_thread_lost(id: u64) -> i32 {
    let n = NLOST.load(Ordering::Acquire);
    let ids = LOST.load(Ordering::Relaxed);
    // SAFETY: `n` ids were written before `NLOST` published them.
    i32::from((0..n).any(|i| unsafe { *ids.add(i) } == id))
}

/// Windows, with every other thread suspended and before the memory is
/// put back: cancel the I/O poller's requests in flight, whose
/// completions would land in memory the session no longer owns.
#[cfg(windows)]
#[unsafe(no_mangle)]
pub extern "C" fn rok_io_quiesce() {
    crate::net::quiesce();
}
