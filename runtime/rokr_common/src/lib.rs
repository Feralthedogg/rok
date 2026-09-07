//! Shared runtime primitives: object header layout, mutator TLS block,
//! safepoint poll, fatal-error path.

#![no_std]

pub mod object_header;
pub mod tls;

/// Write `len` bytes at `msg` to stderr (fd 2), ignoring errors.
///
/// # Safety
/// `msg` must be valid for reads of `len` bytes (or `len` must be 0).
pub unsafe fn write_stderr(mut msg: *const u8, mut len: usize) {
    while len > 0 {
        // SAFETY: caller guarantees `msg..msg+len` is readable.
        let n = unsafe { libc::write(2, msg.cast(), len) };
        if n <= 0 {
            break; // ponytail: no EINTR retry; stderr diagnostics are best-effort.
        }
        let n = n as usize;
        // SAFETY: `n <= len`, so the result stays inside the caller's buffer.
        msg = unsafe { msg.add(n) };
        len -= n;
    }
}

/// Out of memory (stdlib 2.14.5 `oom_fn`; Fatal, exit 101): the one
/// path every allocation failure and `rok::core::panic::oom()` take.
pub fn oom() -> ! {
    fatal(b"fatal error: out of memory")
}

/// Fatal runtime error: `msg` + `\n` to stderr, then `exit(101)`.
/// `exit` (not `_exit`) so buffered stdout from `rok_print_*` is flushed.
pub fn fatal(msg: &[u8]) -> ! {
    // SAFETY: slices are valid for their own length.
    unsafe {
        write_stderr(msg.as_ptr(), msg.len());
        write_stderr(b"\n".as_ptr(), 1);
        libc::exit(101)
    }
}
