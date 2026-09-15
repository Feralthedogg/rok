//! Stack overflow on wasm32: exhausting the engine's call stack, or the
//! linear-memory stack (the main one placed first, so it runs off
//! address 0), traps, and code inside the module cannot catch a trap;
//! the host reports it. The guard range stays unknown (`[0, 0)`).

use core::sync::atomic::{AtomicU64, Ordering};

use rokr_common::tls;

/// `rok_tls_worker_id` of the main thread, named `main` in reports.
static MAIN: AtomicU64 = AtomicU64::new(u64::MAX);

pub fn thread_start(main: bool) {
    if main {
        // SAFETY: this thread's own slot, written by `tls::thread_init`.
        MAIN.store(unsafe { tls::worker_id().read() }, Ordering::Relaxed);
    }
}

pub const fn thread_exit() {}

/// The calling thread's name in a report: `main`, else `<unnamed>`
/// (rok thread names live in the library).
pub fn thread_name(_buf: &mut [u8; 64]) -> &[u8] {
    // SAFETY: this thread's own slot.
    if unsafe { tls::worker_id().read() } == MAIN.load(Ordering::Relaxed) {
        b"main"
    } else {
        b"<unnamed>"
    }
}
