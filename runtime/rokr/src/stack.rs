//! Stack overflow report. Every rok thread records the addresses just
//! below its stack (the guard page, and a little more for frames
//! without stack probes, e.g. C's) and gets an
//! alternate signal stack. A SIGSEGV / SIGBUS there flushes stdout,
//! prints `thread '<name>' has overflowed its stack` and aborts; any
//! other fault falls back to the default action.
//!
//! Covers the main thread (`rok_runtime_init`), `rok_thread_spawn`
//! threads (including executor workers, so deep `await` chains too) and
//! C threads that call `rok_thread_init`.

use core::ptr;
use core::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use rokr_common::{tls, write_stderr};

/// `pthread_self()` of the main thread, named `main` in the report.
static MAIN: AtomicUsize = AtomicUsize::new(0);
static INSTALLED: AtomicBool = AtomicBool::new(false);
/// Alternate signal stack size (plus a guard page below it).
const ALT_SIZE: usize = 64 << 10;
/// How far below the stack a fault still counts as an overflow. rok
/// and Rust frames probe each page, so theirs land in the guard page;
/// this covers unprobed frames up to this size.
const SLOP: usize = 1 << 20;

/// `[lowest usable stack address, guard bytes at / above it)` of the
/// calling thread, or `None` when the OS will not say.
#[cfg(target_vendor = "apple")]
fn stack_bounds() -> Option<(usize, usize)> {
    // SAFETY: queries about the calling thread.
    unsafe {
        let me = libc::pthread_self();
        let top = libc::pthread_get_stackaddr_np(me) as usize;
        let size = libc::pthread_get_stacksize_np(me);
        // The guard page sits below `top - size`.
        Some((top.checked_sub(size)?, 0))
    }
}

#[cfg(target_os = "linux")]
fn stack_bounds() -> Option<(usize, usize)> {
    // SAFETY: `attr` is initialized by `pthread_getattr_np` before use
    // and destroyed after; out-pointers are valid.
    unsafe {
        let mut attr: libc::pthread_attr_t = core::mem::zeroed();
        if libc::pthread_getattr_np(libc::pthread_self(), &mut attr) != 0 {
            return None;
        }
        let mut addr: *mut libc::c_void = ptr::null_mut();
        let mut size = 0usize;
        let mut guard = 0usize;
        let ok = libc::pthread_attr_getstack(&attr, &mut addr, &mut size) == 0
            && libc::pthread_attr_getguardsize(&attr, &mut guard) == 0;
        libc::pthread_attr_destroy(&mut attr);
        // glibc before 2.27 counts the guard inside the reported stack,
        // later ones put it below: take both sides of `addr`.
        ok.then_some((addr as usize, guard))
    }
}

/// Set up the calling thread: its guard range and alternate signal
/// stack, and (once per process) the signal handlers.
pub fn thread_start(main: bool) {
    // SAFETY: plain libc calls on this thread's own state.
    unsafe {
        if main {
            MAIN.store(libc::pthread_self() as usize, Ordering::Relaxed);
        }
        let range =
            stack_bounds().map_or([0, 0], |(lo, guard)| [lo.saturating_sub(SLOP), lo + guard]);
        tls::stack_guard().write(range);
        let page = usize::try_from(libc::sysconf(libc::_SC_PAGESIZE)).unwrap_or(4096);
        let mem = libc::mmap(
            ptr::null_mut(),
            ALT_SIZE + page,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_PRIVATE | libc::MAP_ANON,
            -1,
            0,
        );
        if mem == libc::MAP_FAILED {
            return; // no report on this thread, nothing else changes
        }
        libc::mprotect(mem, page, libc::PROT_NONE);
        let ss = libc::stack_t {
            ss_sp: mem.cast::<u8>().add(page).cast(),
            ss_flags: 0,
            ss_size: ALT_SIZE,
        };
        libc::sigaltstack(&ss, ptr::null_mut());
        if !INSTALLED.swap(true, Ordering::AcqRel) {
            install(handler as libc::sighandler_t);
        }
    }
}

/// Undo `thread_start`'s alternate stack before the thread ends.
pub fn thread_exit() {
    // SAFETY: disables, then unmaps, the stack `thread_start` mapped.
    unsafe {
        let mut old: libc::stack_t = core::mem::zeroed();
        let off = libc::stack_t {
            ss_sp: ptr::null_mut(),
            ss_flags: libc::SS_DISABLE,
            ss_size: 0,
        };
        if libc::sigaltstack(&off, &mut old) != 0 || old.ss_sp.is_null() {
            return;
        }
        if old.ss_flags & libc::SS_DISABLE == 0 && old.ss_size == ALT_SIZE {
            let page = usize::try_from(libc::sysconf(libc::_SC_PAGESIZE)).unwrap_or(4096);
            libc::munmap(old.ss_sp.cast::<u8>().sub(page).cast(), ALT_SIZE + page);
        }
    }
}

unsafe fn install(action: libc::sighandler_t) {
    for sig in [libc::SIGSEGV, libc::SIGBUS] {
        // SAFETY: a zeroed `sigaction` with the fields set below is a
        // valid argument.
        unsafe {
            let mut sa: libc::sigaction = core::mem::zeroed();
            sa.sa_sigaction = action;
            sa.sa_flags = if action == libc::SIG_DFL {
                0
            } else {
                libc::SA_SIGINFO | libc::SA_ONSTACK
            };
            libc::sigemptyset(&mut sa.sa_mask);
            libc::sigaction(sig, &sa, ptr::null_mut());
        }
    }
}

/// The calling thread's name in a report: `main`, its OS name (set by
/// `thread::Builder::name`), else `<unnamed>`. Async-signal-tolerant.
pub fn thread_name(buf: &mut [u8; 64]) -> &[u8] {
    // SAFETY: queries about the calling thread into a local buffer.
    unsafe {
        let me = libc::pthread_self();
        if me as usize == MAIN.load(Ordering::Relaxed) {
            b"main"
        } else if libc::pthread_getname_np(me, buf.as_mut_ptr().cast(), buf.len()) == 0
            && buf[0] != 0
        {
            let n = buf.iter().position(|b| *b == 0).unwrap_or(buf.len());
            &buf[..n]
        } else {
            b"<unnamed>"
        }
    }
}

extern "C" fn handler(_sig: libc::c_int, info: *mut libc::siginfo_t, _ctx: *mut libc::c_void) {
    // SAFETY: the kernel passes a valid `siginfo_t`; the TLS slot was
    // written by `thread_start` (or is zero).
    let (addr, [lo, hi]) = unsafe { ((*info).si_addr() as usize, *tls::stack_guard()) };
    if !(lo <= addr && addr < hi) {
        // Not ours: the default action happens when the faulting
        // instruction runs again.
        // SAFETY: restoring the default disposition.
        unsafe { install(libc::SIG_DFL) };
        return;
    }
    crate::stdio::flush_in_signal();
    let mut buf = [0u8; 64];
    let name = thread_name(&mut buf);
    // SAFETY: only async-signal-tolerant calls.
    unsafe {
        for part in [
            b"\nthread '".as_slice(),
            name,
            b"' has overflowed its stack\nfatal runtime error: stack overflow, aborting\n",
        ] {
            write_stderr(part.as_ptr(), part.len());
        }
        libc::abort();
    }
}
