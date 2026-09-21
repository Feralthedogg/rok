//! Stack overflow report on Windows. The first touch of a thread's
//! guard page raises `EXCEPTION_STACK_OVERFLOW`; a vectored handler
//! (installed once) flushes stdout, prints `thread '<name>' has
//! overflowed its stack` and aborts. Every rok thread reserves stack
//! for the handler to run on (`SetThreadStackGuarantee`); any other
//! exception goes on to the next handler.

use core::sync::atomic::{AtomicBool, Ordering};

use rokr_common::win;
use rokr_common::write_stderr;

static INSTALLED: AtomicBool = AtomicBool::new(false);
/// Stack kept back for the handler once the guard page is hit.
const GUARANTEE: u32 = 32 << 10;

/// Set up the calling thread: its handler stack and (once per process)
/// the vectored handler.
pub fn thread_start() {
    // SAFETY: plain calls on this thread's own state.
    unsafe {
        let mut size = GUARANTEE;
        win::SetThreadStackGuarantee(&mut size);
        if !INSTALLED.swap(true, Ordering::AcqRel) {
            win::AddVectoredExceptionHandler(0, handler);
        }
    }
}

/// Nothing to undo: the guarantee ends with the thread.
pub const fn thread_exit() {}

unsafe extern "system" fn handler(info: *mut win::EXCEPTION_POINTERS) -> i32 {
    // SAFETY: the system passes valid exception pointers.
    let code = unsafe { (*(*info).ExceptionRecord).ExceptionCode };
    if code != win::EXCEPTION_STACK_OVERFLOW {
        return win::EXCEPTION_CONTINUE_SEARCH;
    }
    crate::stdio::flush_in_signal();
    let name = crate::thread::name();
    for part in [
        b"\nthread '".as_slice(),
        name,
        b"' has overflowed its stack\nfatal runtime error: stack overflow, aborting\n",
    ] {
        // SAFETY: each part is valid for its length.
        unsafe { write_stderr(part.as_ptr(), part.len()) };
    }
    // The status `abort` ends with.
    crate::ending(3);
    // SAFETY: never returns.
    unsafe { libc::abort() }
}
