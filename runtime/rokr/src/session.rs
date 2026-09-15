//! For the REPL's session host (`rokc_tools/src/repl_host.c`): the world
//! stopped while it saves the session before a cell, and the runtime put
//! back together after a failed cell when the session is as it was
//! before it but some threads are gone (POSIX: a forked copy has only
//! the host's main thread; Windows: threads the host ended because they
//! no longer match the restored memory).

use core::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};

use rokr_gc::world;

/// Stop every other mutator (at a safepoint or parked in a blocking
/// call): none holds a runtime lock while the session is saved.
#[unsafe(no_mangle)]
pub extern "C" fn rok_world_stop() {
    world::lock();
    world::stop();
}

/// End [`rok_world_stop`]'s pause.
#[unsafe(no_mangle)]
pub extern "C" fn rok_world_resume() {
    world::resume();
    world::unlock();
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
/// other one; else the OS ids at `lost`), drop the I/O poller's state
/// and let the task executor restart what ran on them.
///
/// # Safety
/// `lost` must be readable for `n` ids unless `n` is `usize::MAX`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_session_restored(lost: *const u64, n: usize) {
    let lost = (n != usize::MAX)
        // SAFETY: caller contract.
        .then(|| unsafe { core::slice::from_raw_parts(lost, n) });
    world::forget(lost, note_lost);
    crate::thread::forget_waiters(|id| rok_thread_lost(id) != 0);
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
