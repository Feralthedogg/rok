//! Shared runtime primitives: object header layout, mutator TLS block,
//! the OS layer (`sys`), the raw fd writer and the fatal-error path.

#![no_std]

pub mod gc_abi;
pub mod object_header;
pub mod tls;
pub mod tls_abi;
#[cfg(windows)]
pub mod win;
pub mod wtf8;

#[cfg_attr(any(unix, target_os = "wasi"), path = "sys_unix.rs")]
#[cfg_attr(windows, path = "sys_windows.rs")]
pub mod sys;

pub use sys::{errno, write_all};

/// `len` bytes at `msg` to stderr. Diagnostics: a failure is dropped.
///
/// # Safety
/// `msg` must be valid for reads of `len` bytes (or `len` must be 0).
pub unsafe fn write_stderr(msg: *const u8, len: usize) {
    if len > 0 {
        // SAFETY: caller contract.
        write_all(2, &[unsafe { core::slice::from_raw_parts(msg, len) }]);
    }
}

/// Out of memory (stdlib 2.14.5 `oom_fn`; Fatal, exit 101): the one
/// path every allocation failure and `rok::core::panic::oom()` take.
pub fn oom() -> ! {
    fatal(b"fatal error: out of memory")
}

/// Fatal runtime error: `msg` + `\n` to stderr, then `exit(101)`;
/// `exit` runs the runtime's stdout flush.
pub fn fatal(msg: &[u8]) -> ! {
    write_all(2, &[msg, b"\n"]);
    // SAFETY: plain libc call.
    unsafe { libc::exit(101) }
}
