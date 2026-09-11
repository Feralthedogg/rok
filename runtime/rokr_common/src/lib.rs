//! Shared runtime primitives: object header layout, mutator TLS block,
//! safepoint poll, the raw fd writer and the fatal-error path.

#![no_std]

pub mod gc_abi;
pub mod object_header;
pub mod tls;

/// The calling thread's `errno`.
pub fn errno() -> i32 {
    // SAFETY: the libc errno accessor has no preconditions.
    #[cfg(target_vendor = "apple")]
    unsafe {
        *libc::__error()
    }
    // SAFETY: as above.
    #[cfg(not(target_vendor = "apple"))]
    unsafe {
        *libc::__errno_location()
    }
}

/// Write `parts` to `fd` back to back with `writev`, finishing short
/// writes and retrying `EINTR`: 0 or `-errno`. At most eight parts.
pub fn write_all(fd: i32, parts: &[&[u8]]) -> i32 {
    let mut iov = [libc::iovec {
        iov_base: core::ptr::null_mut(),
        iov_len: 0,
    }; 8];
    let mut n = 0;
    for p in parts.iter().filter(|p| !p.is_empty()) {
        iov[n] = libc::iovec {
            iov_base: p.as_ptr().cast_mut().cast(),
            iov_len: p.len(),
        };
        n += 1;
    }
    let mut first = 0;
    while first < n {
        // SAFETY: `iov[first..n]` describe live caller buffers.
        let r = unsafe { libc::writev(fd, iov[first..].as_ptr(), (n - first) as libc::c_int) };
        if r < 0 {
            let e = errno();
            if e == libc::EINTR {
                continue;
            }
            return -e;
        }
        let mut done = r as usize;
        while first < n && done >= iov[first].iov_len {
            done -= iov[first].iov_len;
            first += 1;
        }
        if first < n {
            // SAFETY: `done < iov_len`, inside the part.
            iov[first].iov_base = unsafe { iov[first].iov_base.cast::<u8>().add(done) }.cast();
            iov[first].iov_len -= done;
        }
    }
    0
}

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
