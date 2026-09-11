//! The standard streams. Everything rok writes to fd 1 goes through one
//! runtime buffer behind one lock, flushed when full, at a newline on a
//! terminal, by `rok_stdio_flush`, at `exit` and before a stack-overflow
//! abort. Stderr is unbuffered: one `writev` per call, so a line never
//! interleaves with another thread's. Stdin is one shared read buffer.
//!
//! A thread that has to wait (for a lock or a syscall) does so parked
//! (`os::native`), so a collection never waits on it; the lock holder
//! only blocks parked. Results are 0 / a count, or `-errno`.

use core::cell::UnsafeCell;
use core::ptr;
use core::sync::atomic::{AtomicI32, Ordering};

use rokr_common::object_header::HEADER_SIZE;
use rokr_common::write_all;

use crate::os::native;
use crate::str::RokStr;

const CAP: usize = 8192;

struct Buf {
    lock: UnsafeCell<libc::pthread_mutex_t>,
    data: UnsafeCell<[u8; CAP]>,
    /// stdout: bytes held; stdin: `[pos, end)` of unread bytes.
    pos: UnsafeCell<usize>,
    end: UnsafeCell<usize>,
}

// SAFETY: every field but `lock` is touched only with `lock` held.
unsafe impl Sync for Buf {}

impl Buf {
    const fn new() -> Self {
        Self {
            lock: UnsafeCell::new(libc::PTHREAD_MUTEX_INITIALIZER),
            data: UnsafeCell::new([0; CAP]),
            pos: UnsafeCell::new(0),
            end: UnsafeCell::new(0),
        }
    }

    /// Take the lock, parked if it is contended.
    fn lock(&self) -> Guard<'_> {
        // SAFETY: a statically initialized mutex.
        if unsafe { libc::pthread_mutex_trylock(self.lock.get()) } != 0 {
            // SAFETY: as above.
            native(|| unsafe { libc::pthread_mutex_lock(self.lock.get()) });
        }
        Guard(self)
    }

    /// Take the lock without parking (no mutator needed).
    fn lock_raw(&self) -> Guard<'_> {
        // SAFETY: a statically initialized mutex.
        unsafe { libc::pthread_mutex_lock(self.lock.get()) };
        Guard(self)
    }
}

struct Guard<'a>(&'a Buf);

impl Drop for Guard<'_> {
    fn drop(&mut self) {
        // SAFETY: held by this guard.
        unsafe { libc::pthread_mutex_unlock(self.0.lock.get()) };
    }
}

impl Guard<'_> {
    #[allow(clippy::mut_from_ref)] // exclusive while the lock is held
    fn parts(&self) -> (&mut [u8; CAP], &mut usize, &mut usize) {
        // SAFETY: the lock is held, so nobody else touches these.
        unsafe {
            (
                &mut *self.0.data.get(),
                &mut *self.0.pos.get(),
                &mut *self.0.end.get(),
            )
        }
    }
}

static OUT: Buf = Buf::new();
static IN: Buf = Buf::new();
/// `flush_at_exit` is registered before any byte is buffered, by the
/// first writer (with a `swap` flag a second writer could buffer, and
/// the process exit, before the first had registered it).
struct Once(UnsafeCell<libc::pthread_once_t>);
// SAFETY: only `pthread_once` touches it.
unsafe impl Sync for Once {}
static AT_EXIT: Once = Once(UnsafeCell::new(libc::PTHREAD_ONCE_INIT));

extern "C" fn register_flush() {
    // SAFETY: registers a plain `extern "C"` function.
    unsafe { libc::atexit(flush_at_exit) };
}
/// `isatty(1)`: -1 unknown, then 0 / 1.
static TTY: AtomicI32 = AtomicI32::new(-1);

fn tty() -> bool {
    let t = TTY.load(Ordering::Relaxed);
    if t >= 0 {
        return t != 0;
    }
    // SAFETY: plain libc call.
    let t = unsafe { libc::isatty(1) };
    TTY.store(t, Ordering::Relaxed);
    t != 0
}

/// Write out the held bytes (lock held). They are dropped on failure,
/// so one bad write does not repeat.
fn drain(held: &[u8], len: &mut usize, parked: bool) -> i32 {
    if *len == 0 {
        return 0;
    }
    let r = if parked {
        native(|| write_all(1, &[&held[..*len]])).0
    } else {
        write_all(1, &[&held[..*len]])
    };
    *len = 0;
    r
}

extern "C" fn flush_at_exit() {
    let g = OUT.lock_raw();
    let (data, len, _) = g.parts();
    drain(data, len, false);
}

/// `parts` to stdout through the buffer.
fn out(parts: &[&[u8]]) -> i32 {
    // SAFETY: a statically initialized once-control.
    unsafe { libc::pthread_once(AT_EXIT.0.get(), Some(register_flush)) };
    let g = OUT.lock();
    let (data, len, _) = g.parts();
    let mut r = 0;
    let mut newline = false;
    for p in parts {
        if p.len() > CAP - *len {
            r = r.min(drain(data, len, true));
        }
        if p.len() >= CAP {
            r = r.min(native(|| write_all(1, &[p])).0);
        } else {
            data[*len..*len + p.len()].copy_from_slice(p);
            *len += p.len();
            newline |= p.contains(&b'\n');
        }
    }
    if newline && tty() {
        r = r.min(drain(data, len, true));
    }
    r
}

/// `parts` to fd 1 or 2.
pub fn write(fd: i32, parts: &[&[u8]]) -> i32 {
    match fd {
        1 => out(parts),
        2 => native(|| write_all(2, parts)).0,
        _ => -libc::EBADF,
    }
}

/// Flush stdout from the stack-overflow handler: only when no thread
/// holds the lock (waiting could deadlock), never parked.
pub fn flush_in_signal() {
    // SAFETY: a statically initialized mutex; left locked, as the
    // process is about to abort.
    if unsafe { libc::pthread_mutex_trylock(OUT.lock.get()) } == 0 {
        // SAFETY: the lock is held.
        let (data, len) = unsafe { (&*OUT.data.get(), *OUT.pos.get()) };
        write_all(1, &[&data[..len]]);
    }
}

/// `s` (then `\n` if `newline != 0`) to fd 1 or 2: 0 or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_stdio_write(fd: i32, s: RokStr, newline: i32) -> i32 {
    let nl: &[u8] = if newline != 0 { b"\n" } else { b"" };
    write(fd, &[s.bytes(), nl])
}

/// `len` bytes of the `GcBuf<u8>` `buf` from `off` to fd 1 or 2.
///
/// # Safety
/// `buf` must be a live `GcBuf<u8>` with at least `off + len` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_stdio_write_buf(fd: i32, buf: *mut u8, off: usize, len: usize) -> i32 {
    // SAFETY: caller contract; the caller roots `buf`, so it stays put.
    write(
        fd,
        &[unsafe { core::slice::from_raw_parts(buf.add(HEADER_SIZE + off), len) }],
    )
}

/// Write out the stdout buffer: 0 or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_stdio_flush() -> i32 {
    let g = OUT.lock();
    let (data, len, _) = g.parts();
    drain(data, len, true)
}

/// One `read(0)`, parked.
fn read0(dst: *mut u8, len: usize) -> isize {
    native(|| {
        loop {
            // SAFETY: caller passes a writable region of `len` bytes.
            let n = unsafe { libc::read(0, dst.cast(), len) };
            if n >= 0 || rokr_common::errno() != libc::EINTR {
                break crate::os::ret(n);
            }
        }
    })
    .0
}

/// Up to `len` bytes of stdin into the `GcBuf<u8>` `buf` at `off`,
/// stopping after the first `delim` byte (`delim < 0`: no stop). The
/// count (0 at the end of input) or `-errno`.
///
/// # Safety
/// `buf` must be a live `GcBuf<u8>` with at least `off + len` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_stdin_read(buf: *mut u8, off: usize, len: usize, delim: i32) -> isize {
    // SAFETY: caller contract.
    let dst = unsafe { buf.add(HEADER_SIZE + off) };
    if len == 0 {
        return 0;
    }
    let g = IN.lock();
    let (data, pos, end) = g.parts();
    if *pos == *end {
        if delim < 0 && len >= CAP {
            return read0(dst, len);
        }
        let n = read0(data.as_mut_ptr(), CAP);
        if n <= 0 {
            return n;
        }
        (*pos, *end) = (0, n as usize);
    }
    let avail = &data[*pos..*end];
    let mut n = avail.len().min(len);
    if let Some(i) = avail[..n].iter().position(|&b| i32::from(b) == delim) {
        n = i + 1;
    }
    // SAFETY: `dst` has room for `len >= n` bytes; distinct objects.
    unsafe { ptr::copy_nonoverlapping(avail.as_ptr(), dst, n) };
    *pos += n;
    n as isize
}
