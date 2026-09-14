//! Stack overflow report on Windows. The first touch of a thread's
//! guard page raises `EXCEPTION_STACK_OVERFLOW`; a vectored handler
//! (installed once) flushes stdout, prints `thread '<name>' has
//! overflowed its stack` and aborts. Every rok thread reserves stack
//! for the handler to run on (`SetThreadStackGuarantee`); any other
//! exception goes on to the next handler.

use core::sync::atomic::{AtomicBool, AtomicU32, Ordering};

use rokr_common::win;
use rokr_common::write_stderr;

/// `GetCurrentThreadId()` of the main thread, named `main` in reports.
static MAIN: AtomicU32 = AtomicU32::new(0);
static INSTALLED: AtomicBool = AtomicBool::new(false);
/// Stack kept back for the handler once the guard page is hit.
const GUARANTEE: u32 = 32 << 10;

/// Set up the calling thread: its handler stack and (once per process)
/// the vectored handler.
pub fn thread_start(main: bool) {
    // SAFETY: plain calls on this thread's own state.
    unsafe {
        if main {
            MAIN.store(win::GetCurrentThreadId(), Ordering::Relaxed);
        }
        let mut size = GUARANTEE;
        win::SetThreadStackGuarantee(&mut size);
        if !INSTALLED.swap(true, Ordering::AcqRel) {
            win::AddVectoredExceptionHandler(0, handler);
        }
    }
}

/// Nothing to undo: the guarantee ends with the thread.
pub const fn thread_exit() {}

/// The calling thread's name in a report: `main`, else `<unnamed>`
/// (rok thread names live in the library, not the OS).
pub fn thread_name(_buf: &mut [u8; 64]) -> &[u8] {
    // SAFETY: no preconditions.
    if unsafe { win::GetCurrentThreadId() } == MAIN.load(Ordering::Relaxed) {
        b"main"
    } else {
        b"<unnamed>"
    }
}

unsafe extern "system" fn handler(info: *mut win::EXCEPTION_POINTERS) -> i32 {
    // SAFETY: the system passes valid exception pointers.
    let code = unsafe { (*(*info).ExceptionRecord).ExceptionCode };
    if code != win::EXCEPTION_STACK_OVERFLOW {
        return win::EXCEPTION_CONTINUE_SEARCH;
    }
    crate::stdio::flush_in_signal();
    let mut buf = [0u8; 64];
    let name = thread_name(&mut buf);
    for part in [
        b"\nthread '".as_slice(),
        name,
        b"' has overflowed its stack\nfatal runtime error: stack overflow, aborting\n",
    ] {
        // SAFETY: each part is valid for its length.
        unsafe { write_stderr(part.as_ptr(), part.len()) };
    }
    // SAFETY: never returns.
    unsafe { libc::abort() }
}
