//! POSIX helpers behind `rok::std` (stdlib 300: fs, io, env, process).
//! No ABI stability (805 §8.5.12 appendix).
//!
//! Conventions:
//! - `str` arguments are rok strings; libc gets them through [`cs`]
//!   (a slice need not be NUL-terminated).
//! - Results: `>= 0` success, `-errno` failure. Resolver failures use
//!   codes from [`EAI_BASE`] up; only this module interprets codes.
//! - Byte data lives in the caller's `GcBuf<u8>` (header pointer) as a
//!   region `(buf, off, len)`; reads fill it in place. Variable-length
//!   results (paths, names, values) are copied in up to `len` bytes and
//!   return their full length, so the caller can retry with more room.
//! - Calls that may block are bracketed by `enter_native` /
//!   `leave_native` (804 §8.4.10) so a collection need not wait on them;
//!   nothing allocates GC memory while parked. The caller roots every GC
//!   argument, so it stays in place throughout.

use core::mem::size_of;
use core::ptr;

pub use rokr_common::errno;
use rokr_common::object_header::HEADER_SIZE;
use rokr_gc::world;

use crate::str::{RokStr, build};

type CStrPtr = *const libc::c_char;

/// `r` (a libc `-1`-on-error result) as `>= 0` or `-errno`.
pub fn ret(r: isize) -> isize {
    if r < 0 { -(errno() as isize) } else { r }
}

/// Run a blocking call parked; `errno` survives the re-entry.
pub fn native<R>(f: impl FnOnce() -> R) -> (R, i32) {
    world::enter_native();
    let r = f();
    let e = errno();
    world::leave_native();
    (r, e)
}

/// `s` as a C string for libc: its own bytes when a NUL follows them,
/// else a `malloc`ed copy (no GC allocation, so it works while parked)
/// freed on drop. Keep it alive across the call: `cs(s).p()` inside the
/// call expression.
pub fn cs(s: RokStr) -> CArg {
    if s.len == 0 {
        return CArg(c"".as_ptr(), false);
    }
    // SAFETY: byte `len` of a `str` is readable (its source's next byte
    // or the NUL after it).
    if unsafe { *s.ptr.add(s.len) } == 0 {
        return CArg(s.ptr.cast(), false);
    }
    // SAFETY: malloc'd `len + 1` bytes, filled and terminated.
    unsafe {
        let p = libc::malloc(s.len + 1).cast::<u8>();
        if p.is_null() {
            rokr_common::oom();
        }
        ptr::copy_nonoverlapping(s.ptr, p, s.len);
        *p.add(s.len) = 0;
        CArg(p.cast_const().cast(), true)
    }
}

/// A NUL-terminated string from [`cs`]; `.1`: owned (malloc'd).
pub struct CArg(CStrPtr, bool);

impl CArg {
    pub const fn p(&self) -> CStrPtr {
        self.0
    }
}

impl Drop for CArg {
    fn drop(&mut self) {
        if self.1 {
            // SAFETY: our own malloc block.
            unsafe { libc::free(self.0.cast_mut().cast()) };
        }
    }
}

/// Element `i` of the `GcBuf<i32>` `buf` (header pointer).
///
/// # Safety
/// `buf` must be a live `GcBuf<i32>` with more than `i` elements.
#[allow(clippy::cast_ptr_alignment)] // GC payloads are 8-aligned
const unsafe fn cell(buf: *mut u8, i: usize) -> *mut i32 {
    // SAFETY: caller contract; elements follow the header.
    unsafe { buf.add(HEADER_SIZE).cast::<i32>().add(i) }
}

/// The writable region `off..off + len` of the `GcBuf<u8>` `buf`.
///
/// # Safety
/// `buf` must be a live `GcBuf<u8>` with at least `off + len` bytes.
pub const unsafe fn region(buf: *mut u8, off: usize) -> *mut u8 {
    // SAFETY: caller contract.
    unsafe { buf.add(HEADER_SIZE + off) }
}

/// Copy up to `len` bytes of `src` to `buf[off..]`; `src`'s full length.
fn put(buf: *mut u8, off: usize, len: usize, src: &[u8]) -> isize {
    // SAFETY: the library passes a live region of `len` bytes.
    unsafe { ptr::copy_nonoverlapping(src.as_ptr(), region(buf, off), src.len().min(len)) };
    src.len() as isize
}

/// Bytes of the NUL-terminated `buf` before its NUL.
fn until_nul(buf: &[u8]) -> &[u8] {
    &buf[..buf.iter().position(|&b| b == 0).unwrap_or(buf.len())]
}

// ---------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------

/// First resolver code: `getaddrinfo` failure `e` is `EAI_BASE + |e|`.
pub const EAI_BASE: i32 = 100_000;

/// `IoErrorKind` discriminants (library/std/io.rok declares the same).
mod kind {
    pub const OTHER: i32 = 0;
    pub const NOT_FOUND: i32 = 1;
    pub const PERMISSION_DENIED: i32 = 2;
    pub const ALREADY_EXISTS: i32 = 3;
    pub const NOT_A_DIRECTORY: i32 = 4;
    pub const IS_A_DIRECTORY: i32 = 5;
    pub const DIRECTORY_NOT_EMPTY: i32 = 6;
    pub const INVALID_INPUT: i32 = 7;
    pub const BROKEN_PIPE: i32 = 8;
    pub const INTERRUPTED: i32 = 9;
    pub const WOULD_BLOCK: i32 = 10;
    pub const TIMED_OUT: i32 = 11;
    pub const STORAGE_FULL: i32 = 12;
    pub const CROSSES_DEVICES: i32 = 13;
    pub const UNSUPPORTED: i32 = 14;
}

/// The `IoErrorKind` discriminant of error code `code`.
#[unsafe(no_mangle)]
pub const extern "C" fn rok_os_errno_kind(code: i32) -> i32 {
    match code {
        libc::ENOENT | EAI_BASE.. => kind::NOT_FOUND,
        libc::EACCES | libc::EPERM => kind::PERMISSION_DENIED,
        libc::EEXIST => kind::ALREADY_EXISTS,
        libc::ENOTDIR => kind::NOT_A_DIRECTORY,
        libc::EISDIR => kind::IS_A_DIRECTORY,
        libc::ENOTEMPTY => kind::DIRECTORY_NOT_EMPTY,
        libc::EINVAL => kind::INVALID_INPUT,
        libc::EPIPE => kind::BROKEN_PIPE,
        libc::EINTR => kind::INTERRUPTED,
        libc::EAGAIN => kind::WOULD_BLOCK,
        libc::ETIMEDOUT => kind::TIMED_OUT,
        libc::ENOSPC => kind::STORAGE_FULL,
        libc::EXDEV => kind::CROSSES_DEVICES,
        libc::ENOSYS | libc::ENOTSUP => kind::UNSUPPORTED,
        _ => kind::OTHER,
    }
}

/// The message of error code `code` (`strerror` / `gai_strerror`).
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_strerror(code: i32) -> RokStr {
    if code >= EAI_BASE {
        // glibc numbers EAI codes negative, BSD positive.
        #[cfg(target_os = "linux")]
        let c = EAI_BASE - code;
        #[cfg(not(target_os = "linux"))]
        let c = code - EAI_BASE;
        // SAFETY: gai_strerror returns a static C string.
        let s = unsafe { core::ffi::CStr::from_ptr(libc::gai_strerror(c)) };
        return build(&[s.to_bytes()]);
    }
    let mut buf = [0u8; 256];
    // SAFETY: `buf` is writable for its length.
    unsafe { libc::strerror_r(code, buf.as_mut_ptr().cast(), buf.len()) };
    build(&[until_nul(&buf)])
}

// ---------------------------------------------------------------------
// File descriptors
// ---------------------------------------------------------------------

/// `AT_FDCWD` for a negative `dir` (the root / cwd capability).
const fn at(dir: i32) -> i32 {
    if dir < 0 { libc::AT_FDCWD } else { dir }
}

/// `openat`. `flags` bits: 1 read, 2 write, 4 append, 8 truncate,
/// 16 create, 32 `create_new`, 64 directory. Always `O_CLOEXEC`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_open(dir: i32, path: RokStr, flags: i32, mode: u32) -> i32 {
    let mut o = match (flags & 1 != 0, flags & 6 != 0) {
        (true, true) => libc::O_RDWR,
        (false, true) => libc::O_WRONLY,
        _ => libc::O_RDONLY,
    };
    for (bit, f) in [
        (4, libc::O_APPEND),
        (8, libc::O_TRUNC),
        (16, libc::O_CREAT),
        (32, libc::O_CREAT | libc::O_EXCL),
        (64, libc::O_DIRECTORY),
    ] {
        if flags & bit != 0 {
            o |= f;
        }
    }
    // SAFETY: `path` is a C string; the mode is read only with O_CREAT.
    let (r, _) = native(|| unsafe {
        libc::openat(
            at(dir),
            cs(path).p(),
            o | libc::O_CLOEXEC,
            mode as libc::c_uint,
        )
    });
    ret(r as isize) as i32
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_os_close(fd: i32) -> i32 {
    // SAFETY: plain libc call.
    ret(unsafe { libc::close(fd) } as isize) as i32
}

/// One `read` into `buf[off..off + len]`: the count (0 = EOF) or `-errno`.
///
/// # Safety
/// `buf` must be a live `GcBuf<u8>` with at least `off + len` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_os_read(fd: i32, buf: *mut u8, off: usize, len: usize) -> isize {
    // SAFETY: caller contract.
    let dst = unsafe { region(buf, off) };
    native(|| {
        loop {
            // SAFETY: `dst` is writable for `len` bytes.
            let n = ret(unsafe { libc::read(fd, dst.cast(), len) });
            if n != -(libc::EINTR as isize) {
                break n;
            }
        }
    })
    .0
}

/// One `write` of `buf[off..off + len]`: the count or `-errno`.
///
/// # Safety
/// `buf` must be a live `GcBuf<u8>` with at least `off + len` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_os_write(fd: i32, buf: *mut u8, off: usize, len: usize) -> isize {
    // SAFETY: caller contract.
    let src = unsafe { region(buf, off) };
    native(|| {
        loop {
            // SAFETY: `src` is readable for `len` bytes.
            let n = ret(unsafe { libc::write(fd, src.cast(), len) });
            if n != -(libc::EINTR as isize) {
                break n;
            }
        }
    })
    .0
}

/// Wait until `fd1` or `fd2` (negative: ignored) is readable or hung
/// up: bit 0 / bit 1 set for each ready one, or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_poll_read(fd1: i32, fd2: i32) -> i32 {
    let mut fds = [fd1, fd2].map(|fd| libc::pollfd {
        fd,
        events: libc::POLLIN,
        revents: 0,
    });
    native(|| {
        loop {
            // SAFETY: two entries; negative fds are ignored.
            if unsafe { libc::poll(fds.as_mut_ptr(), 2, -1) } >= 0 {
                break i32::from(fds[0].revents != 0) | (i32::from(fds[1].revents != 0) << 1);
            }
            let e = errno();
            if e != libc::EINTR {
                break -e;
            }
        }
    })
    .0
}

/// `fsync` (`data_only == 0`) or `fdatasync`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_fsync(fd: i32, data_only: i32) -> i32 {
    // SAFETY: plain libc calls.
    let (r, e) = native(|| unsafe {
        #[cfg(not(target_vendor = "apple"))]
        if data_only != 0 {
            return libc::fdatasync(fd);
        }
        let _ = data_only;
        libc::fsync(fd)
    });
    if r < 0 { -e } else { 0 }
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_os_ftruncate(fd: i32, len: u64) -> i32 {
    // SAFETY: plain libc call.
    ret(unsafe { libc::ftruncate(fd, len as libc::off_t) } as isize) as i32
}

/// `lseek`; `whence` 0 start, 1 current, 2 end. New offset or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_lseek(fd: i32, off: i64, whence: i32) -> i64 {
    let w = match whence {
        1 => libc::SEEK_CUR,
        2 => libc::SEEK_END,
        _ => libc::SEEK_SET,
    };
    // SAFETY: plain libc call.
    let r = unsafe { libc::lseek(fd, off as libc::off_t, w) };
    if r < 0 { -i64::from(errno()) } else { r as i64 }
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_os_dup(fd: i32) -> i32 {
    // SAFETY: plain libc call.
    ret(unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, 0) } as isize) as i32
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_os_fchmod(fd: i32, mode: u32) -> i32 {
    // SAFETY: plain libc call.
    ret(unsafe { libc::fchmod(fd, mode as libc::mode_t) } as isize) as i32
}

/// A read-only shared mapping of `len` bytes of `fd` at `offset`: its
/// address, or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_mmap(fd: i32, len: usize, offset: u64) -> i64 {
    if len == 0 {
        return -i64::from(libc::EINVAL);
    }
    // SAFETY: a fresh mapping; the kernel picks the address.
    let (p, e) = native(|| unsafe {
        libc::mmap(
            core::ptr::null_mut(),
            len,
            libc::PROT_READ,
            libc::MAP_SHARED,
            fd,
            offset as libc::off_t,
        )
    });
    if p == libc::MAP_FAILED {
        -i64::from(e)
    } else {
        p as i64
    }
}

/// Unmap a `rok_os_mmap` region: 0 or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_munmap(addr: usize, len: usize) -> i32 {
    // SAFETY: `addr..addr + len` is a mapping from `rok_os_mmap`.
    ret(unsafe { libc::munmap(addr as *mut libc::c_void, len) } as isize) as i32
}

/// Copy `len` bytes at `addr + at` into `buf[off..]`.
///
/// # Safety
/// `addr + at .. + len` must be mapped; `buf` a live `GcBuf<u8>` with at
/// least `off + len` bytes.
#[unsafe(no_mangle)]
pub const unsafe extern "C" fn rok_os_mmap_copy(
    addr: usize,
    at: usize,
    buf: *mut u8,
    off: usize,
    len: usize,
) {
    // SAFETY: caller contract.
    unsafe { core::ptr::copy_nonoverlapping((addr + at) as *const u8, region(buf, off), len) };
}

/// `flock`: `op` 1 shared, 2 exclusive, 8 unlock, | 4 non-blocking.
/// 1 = locked, 0 = would block (non-blocking), `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_flock(fd: i32, op: i32) -> i32 {
    let mut o = 0;
    for (bit, f) in [
        (1, libc::LOCK_SH),
        (2, libc::LOCK_EX),
        (4, libc::LOCK_NB),
        (8, libc::LOCK_UN),
    ] {
        if op & bit != 0 {
            o |= f;
        }
    }
    // SAFETY: plain libc call.
    let (r, e) = native(|| unsafe { libc::flock(fd, o) });
    match (r, e) {
        (0, _) => 1,
        (_, libc::EWOULDBLOCK) if op & 4 != 0 => 0,
        _ => -e,
    }
}

/// Copy `src` → `dst` from their current offsets to EOF: bytes or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_copy_fd(src: i32, dst: i32) -> i64 {
    let (r, e) = native(|| {
        let mut buf = [0u8; 16 * 1024];
        let mut total: i64 = 0;
        loop {
            // SAFETY: `buf` is writable for its length.
            let n = unsafe { libc::read(src, buf.as_mut_ptr().cast(), buf.len()) };
            if n == 0 {
                return total;
            }
            if n < 0 {
                if errno() == libc::EINTR {
                    continue;
                }
                return -1;
            }
            let mut off = 0;
            while off < n as usize {
                // SAFETY: `buf[off..n]` is initialized.
                let w = unsafe { libc::write(dst, buf.as_ptr().add(off).cast(), n as usize - off) };
                if w < 0 {
                    if errno() == libc::EINTR {
                        continue;
                    }
                    return -1;
                }
                off += w as usize;
            }
            total += n as i64;
        }
    });
    if r < 0 { -i64::from(e) } else { r }
}

// ---------------------------------------------------------------------
// Paths and directories
// ---------------------------------------------------------------------

/// Reflink `from` (a regular file) to a new `to`, both under `dir`
/// (macOS `clonefileat`: same-volume APFS copies share their blocks).
/// 0, or `-errno` (`EEXIST`, cross-volume, no support) — the caller
/// then copies the bytes. Elsewhere always `-ENOTSUP`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_clone(dir: i32, from: RokStr, to: RokStr) -> i32 {
    #[cfg(target_os = "macos")]
    {
        // SAFETY: both are C strings.
        let (r, e) =
            native(|| unsafe { libc::clonefileat(at(dir), cs(from).p(), at(dir), cs(to).p(), 0) });
        if r < 0 { -e } else { 0 }
    }
    #[cfg(not(target_os = "macos"))]
    {
        let _ = (dir, from, to);
        -libc::ENOTSUP
    }
}

/// `fstatat` (`fd < 0`) or `fstat(fd)`, filling the `GcBuf<i64>` `out`:
/// `[kind, size, mode, mtime_s, mtime_ns, atime_s, ctime_s, atime_ns]`, kind 1
/// file, 2 dir, 3 symlink, 0 other. 0 or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_stat(dir: i32, path: RokStr, follow: i32, fd: i32, out: *mut u8) -> i32 {
    // SAFETY: zeroed `stat` is a valid out-buffer.
    let mut st: libc::stat = unsafe { core::mem::zeroed() };
    let flags = if follow != 0 {
        0
    } else {
        libc::AT_SYMLINK_NOFOLLOW
    };
    // SAFETY: `path` is a C string; `st` is writable.
    let (r, e) = native(|| unsafe {
        if fd >= 0 {
            libc::fstat(fd, &mut st)
        } else {
            libc::fstatat(at(dir), cs(path).p(), &mut st, flags)
        }
    });
    if r < 0 {
        return -e;
    }
    let kind = match st.st_mode & libc::S_IFMT {
        libc::S_IFREG => 1,
        libc::S_IFDIR => 2,
        libc::S_IFLNK => 3,
        _ => 0,
    };
    let vals = [
        kind,
        st.st_size as i64,
        i64::from(st.st_mode & 0o7777),
        st.st_mtime as i64,
        st.st_mtime_nsec as i64,
        st.st_atime as i64,
        st.st_ctime as i64,
        st.st_atime_nsec as i64,
    ];
    // SAFETY: the library passes a live `GcBuf<i64>` of 8 elements.
    unsafe { ptr::copy_nonoverlapping(vals.as_ptr(), out.add(HEADER_SIZE).cast(), vals.len()) };
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_os_mkdir(dir: i32, path: RokStr, mode: u32) -> i32 {
    // SAFETY: `path` is a C string.
    let (r, e) = native(|| unsafe { libc::mkdirat(at(dir), cs(path).p(), mode as libc::mode_t) });
    if r < 0 { -e } else { 0 }
}

/// `unlinkat`; `is_dir != 0` removes an empty directory.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_unlink(dir: i32, path: RokStr, is_dir: i32) -> i32 {
    let flags = if is_dir != 0 { libc::AT_REMOVEDIR } else { 0 };
    // SAFETY: `path` is a C string.
    let (r, e) = native(|| unsafe { libc::unlinkat(at(dir), cs(path).p(), flags) });
    if r < 0 { -e } else { 0 }
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_os_rename(dir: i32, from: RokStr, to_dir: i32, to: RokStr) -> i32 {
    // SAFETY: both are C strings.
    let (r, e) =
        native(|| unsafe { libc::renameat(at(dir), cs(from).p(), at(to_dir), cs(to).p()) });
    if r < 0 { -e } else { 0 }
}

/// `hard == 0`: symlink `link` → `target`; else hard link.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_link(dir: i32, target: RokStr, link: RokStr, hard: i32) -> i32 {
    // SAFETY: both are C strings.
    let (r, e) = native(|| unsafe {
        if hard != 0 {
            libc::linkat(at(dir), cs(target).p(), at(dir), cs(link).p(), 0)
        } else {
            libc::symlinkat(cs(target).p(), at(dir), cs(link).p())
        }
    });
    if r < 0 { -e } else { 0 }
}

/// Open `path` under `dir` for listing: a `DIR*` (positive) or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_opendir(dir: i32, path: RokStr) -> isize {
    // SAFETY: `path` is a C string; `fdopendir` owns `fd` on success.
    let (d, e) = native(|| unsafe {
        let fd = libc::openat(
            at(dir),
            cs(path).p(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_CLOEXEC,
        );
        if fd < 0 {
            return ptr::null_mut();
        }
        let d = libc::fdopendir(fd);
        if d.is_null() {
            libc::close(fd);
        }
        d
    });
    if d.is_null() {
        -(e as isize)
    } else {
        d as isize
    }
}

/// The next entry name (skipping `.` / `..`) into `buf[off..off + len]`
/// (room for any name: 1024 bytes): its length, 0 at the end, or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_readdir(d: isize, buf: *mut u8, off: usize, len: usize) -> isize {
    loop {
        // SAFETY: errno reset distinguishes end from failure.
        unsafe { set_errno(0) };
        // SAFETY: `d` is a live `DIR*` from `rok_os_opendir`.
        let ent = unsafe { libc::readdir(d as *mut libc::DIR) };
        if ent.is_null() {
            return -(errno() as isize);
        }
        // SAFETY: `d_name` is NUL-terminated.
        let name = unsafe { core::ffi::CStr::from_ptr((*ent).d_name.as_ptr()) }.to_bytes();
        if name.len() > len {
            return -(libc::ENAMETOOLONG as isize);
        }
        if name != b"." && name != b".." {
            return put(buf, off, len, name);
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_os_closedir(d: isize) {
    // SAFETY: `d` is a live `DIR*`.
    unsafe { libc::closedir(d as *mut libc::DIR) };
}

unsafe fn set_errno(v: i32) {
    // SAFETY: errno is this thread's.
    #[cfg(target_vendor = "apple")]
    unsafe {
        *libc::__error() = v;
    }
    // SAFETY: as above.
    #[cfg(not(target_vendor = "apple"))]
    unsafe {
        *libc::__errno_location() = v;
    }
}

/// The working directory into `buf[off..off + len]`: its full length or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_getcwd(buf: *mut u8, off: usize, len: usize) -> isize {
    let mut cwd = [0u8; libc::PATH_MAX as usize + 1];
    // SAFETY: `cwd` is writable for its length.
    if unsafe { libc::getcwd(cwd.as_mut_ptr().cast(), cwd.len()) }.is_null() {
        return -(errno() as isize);
    }
    put(buf, off, len, until_nul(&cwd))
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_os_chdir(path: RokStr) -> i32 {
    // SAFETY: `path` is a C string.
    ret(unsafe { libc::chdir(cs(path).p()) } as isize) as i32
}

/// `realpath(path)` into `buf[off..off + len]`: its full length or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_realpath(path: RokStr, buf: *mut u8, off: usize, len: usize) -> isize {
    let mut real = [0u8; libc::PATH_MAX as usize + 1];
    // SAFETY: `real` has PATH_MAX bytes.
    let (p, e) = native(|| unsafe { libc::realpath(cs(path).p(), real.as_mut_ptr().cast()) });
    if p.is_null() {
        return -(e as isize);
    }
    put(buf, off, len, until_nul(&real))
}

#[cfg(target_vendor = "apple")]
unsafe extern "C" {
    #[link_name = "_NSGetExecutablePath"]
    fn ns_get_executable_path(buf: *mut libc::c_char, size: *mut u32) -> i32;
}

/// Absolute path of the running executable into `buf[off..off + len]`:
/// its full length or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_current_exe(buf: *mut u8, off: usize, len: usize) -> isize {
    let mut path = [0u8; libc::PATH_MAX as usize + 1];
    #[cfg(target_vendor = "apple")]
    {
        let mut raw = [0u8; libc::PATH_MAX as usize + 1];
        let mut size = raw.len() as u32;
        // SAFETY: `raw` is writable for `size` bytes.
        if unsafe { ns_get_executable_path(raw.as_mut_ptr().cast(), &mut size) } != 0 {
            return -(libc::ENAMETOOLONG as isize);
        }
        // SAFETY: `raw` is NUL-terminated; `path` has PATH_MAX bytes.
        if unsafe { libc::realpath(raw.as_ptr().cast(), path.as_mut_ptr().cast()) }.is_null() {
            return -(errno() as isize);
        }
    }
    #[cfg(not(target_vendor = "apple"))]
    {
        // SAFETY: `path` is writable for its length minus the NUL.
        let n = unsafe {
            libc::readlink(
                c"/proc/self/exe".as_ptr(),
                path.as_mut_ptr().cast(),
                path.len() - 1,
            )
        };
        if n < 0 {
            return -(errno() as isize);
        }
    }
    put(buf, off, len, until_nul(&path))
}

// ---------------------------------------------------------------------
// Environment
// ---------------------------------------------------------------------

/// `environ` (Apple: through `_NSGetEnviron`, as executables only see it there).
fn environ() -> *mut *const CStrPtr {
    #[cfg(target_vendor = "apple")]
    {
        // SAFETY: always valid in a running process.
        unsafe { libc::_NSGetEnviron().cast() }
    }
    #[cfg(not(target_vendor = "apple"))]
    {
        unsafe extern "C" {
            static mut environ: *const CStrPtr;
        }
        &raw mut environ
    }
}

/// The C `main`'s argc / argv, captured before `main` runs.
#[cfg(not(target_vendor = "apple"))]
static mut ARGS: (i32, *const CStrPtr) = (0, ptr::null());

/// glibc passes `(argc, argv, envp)` to `.init_array` entries.
#[cfg(not(target_vendor = "apple"))]
#[used]
#[unsafe(link_section = ".init_array")]
static CAPTURE_ARGS: extern "C" fn(i32, *const CStrPtr, *const CStrPtr) = capture_args;

#[cfg(not(target_vendor = "apple"))]
extern "C" fn capture_args(argc: i32, argv: *const CStrPtr, _envp: *const CStrPtr) {
    // SAFETY: runs once, single-threaded, before `main`.
    unsafe { ARGS = (argc, argv) };
}

fn args() -> (usize, *const CStrPtr) {
    #[cfg(target_vendor = "apple")]
    {
        // SAFETY: set by dyld before `main`.
        unsafe { (*libc::_NSGetArgc() as usize, (*libc::_NSGetArgv()).cast()) }
    }
    #[cfg(not(target_vendor = "apple"))]
    {
        // SAFETY: written once before `main`.
        let (c, v) = unsafe { ARGS };
        (c.max(0) as usize, v)
    }
}

/// C string `p` as a GC `str` (null → `""`).
fn from_c(p: CStrPtr) -> RokStr {
    if p.is_null() {
        return build(&[]);
    }
    // SAFETY: a NUL-terminated string from libc.
    build(&[unsafe { core::ffi::CStr::from_ptr(p) }.to_bytes()])
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_os_argc() -> usize {
    args().0
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_os_arg(i: usize) -> RokStr {
    let (n, v) = args();
    if i >= n || v.is_null() {
        return build(&[]);
    }
    // SAFETY: `argv` has `argc` entries.
    from_c(unsafe { *v.add(i) })
}

/// Entry `i` of `environ` (`"KEY=VALUE"`), `""` past the end.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_env_at(i: usize) -> RokStr {
    // SAFETY: `environ` is a null-terminated array; walk up to `i`.
    unsafe {
        let env = *environ();
        if env.is_null() {
            return build(&[]);
        }
        for k in 0..=i {
            if (*env.add(k)).is_null() {
                return build(&[]);
            }
        }
        from_c(*env.add(i))
    }
}

/// `getenv(name)` into `buf[off..off + len]`: its full length, or
/// `-ENOENT` when unset.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_getenv(name: RokStr, buf: *mut u8, off: usize, len: usize) -> isize {
    // SAFETY: `name` is a C string.
    let p = unsafe { libc::getenv(cs(name).p()) };
    if p.is_null() {
        return -(libc::ENOENT as isize);
    }
    // SAFETY: a NUL-terminated string from libc.
    put(
        buf,
        off,
        len,
        unsafe { core::ffi::CStr::from_ptr(p) }.to_bytes(),
    )
}

/// `setenv` (`value` given) / `unsetenv`. 0 or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_setenv(name: RokStr, value: RokStr, unset: i32) -> i32 {
    // SAFETY: C strings. No global env lock (spec 306.3).
    let r = unsafe {
        if unset != 0 {
            libc::unsetenv(cs(name).p())
        } else {
            libc::setenv(cs(name).p(), cs(value).p(), 1)
        }
    };
    ret(r as isize) as i32
}

// ---------------------------------------------------------------------
// Processes
// ---------------------------------------------------------------------

/// Pointers to the NUL-separated pieces of `blob` (`count` of them),
/// null-terminated, in a malloc block.
fn split_blob(blob: RokStr, count: usize) -> *mut CStrPtr {
    // SAFETY: malloc of `count + 1` pointers.
    let v = unsafe { libc::malloc((count + 1) * size_of::<CStrPtr>()) }.cast::<CStrPtr>();
    if v.is_null() {
        rokr_common::oom();
    }
    let mut p = blob.ptr;
    for i in 0..count {
        // SAFETY: the blob holds `count` NUL-terminated pieces.
        unsafe {
            *v.add(i) = p.cast();
            p = p.add(libc::strlen(p.cast()) + 1);
        }
    }
    // SAFETY: slot `count` exists.
    unsafe { *v.add(count) = ptr::null() };
    v
}

/// `fork` + `execvp`. `argv` / `envs` hold `argc` / `envc`
/// NUL-terminated pieces (`envc < 0`: inherit the environment);
/// `cwd` empty = inherit; `pgid >= 0` joins that process group (0: a
/// new one led by the child). Stdio modes: `-1` inherit, `-2` null,
/// `-3` piped, `>= 0` that fd. The pipe ends (or -1) go to
/// `out[0..3]` (stdin write end, stdout / stderr read ends).
/// Returns the pid or `-errno` (exec failures included).
#[unsafe(no_mangle)]
#[allow(clippy::too_many_arguments)]
pub extern "C" fn rok_os_spawn(
    argv: RokStr,
    argc: usize,
    envs: RokStr,
    envc: isize,
    cwd: RokStr,
    stdio_in: i32,
    stdio_out: i32,
    stdio_err: i32,
    pgid: i32,
    out: *mut u8,
) -> i32 {
    let av = split_blob(argv, argc);
    let ev = if envc >= 0 {
        split_blob(envs, envc as usize)
    } else {
        ptr::null_mut()
    };
    // Before the fork: the child must not malloc.
    let cwd_c = cs(cwd);
    let modes = [stdio_in, stdio_out, stdio_err];
    // [child end, parent end] per stream.
    let mut ends = [[-1i32; 2]; 3];
    let mut report = [-1i32; 2];
    let r = native(|| {
        // SAFETY: pipe/fcntl/fork/exec on locals; the child only makes
        // async-signal-safe calls before `execvp` / `_exit`.
        unsafe {
            let cloexec = |fd: i32| libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
            for (i, m) in modes.iter().enumerate() {
                if *m == -3 {
                    let mut p = [0i32; 2];
                    if libc::pipe(p.as_mut_ptr()) < 0 {
                        return -errno();
                    }
                    cloexec(p[0]);
                    cloexec(p[1]);
                    ends[i] = if i == 0 { [p[0], p[1]] } else { [p[1], p[0]] };
                }
            }
            if libc::pipe(report.as_mut_ptr()) < 0 {
                return -errno();
            }
            cloexec(report[0]);
            cloexec(report[1]);
            let pid = libc::fork();
            if pid < 0 {
                return -errno();
            }
            if pid == 0 {
                let fail = |e: i32| -> ! {
                    libc::write(report[1], (&raw const e).cast(), 4);
                    libc::_exit(127)
                };
                for (i, m) in modes.iter().enumerate() {
                    let src = match *m {
                        -1 => continue,
                        -2 => {
                            let fl = if i == 0 {
                                libc::O_RDONLY
                            } else {
                                libc::O_WRONLY
                            };
                            libc::open(c"/dev/null".as_ptr(), fl)
                        }
                        -3 => ends[i][0],
                        fd => fd,
                    };
                    if src < 0 || libc::dup2(src, i as i32) < 0 {
                        fail(errno());
                    }
                }
                if cwd.len > 0 && libc::chdir(cwd_c.p()) < 0 {
                    fail(errno());
                }
                if pgid >= 0 && libc::setpgid(0, pgid) < 0 {
                    fail(errno());
                }
                if !ev.is_null() {
                    *environ() = ev.cast_const();
                }
                libc::execvp(*av, av.cast_const());
                fail(errno());
            }
            for e in &ends {
                if e[0] >= 0 {
                    libc::close(e[0]);
                }
            }
            libc::close(report[1]);
            let mut code = 0i32;
            let n = loop {
                let n = libc::read(report[0], (&raw mut code).cast(), 4);
                if n >= 0 || errno() != libc::EINTR {
                    break n;
                }
            };
            libc::close(report[0]);
            if n == 4 {
                let mut st = 0;
                libc::waitpid(pid, &mut st, 0);
                return -code;
            }
            pid
        }
    })
    .0;
    // SAFETY: malloc blocks from `split_blob`.
    unsafe {
        libc::free(av.cast());
        libc::free(ev.cast());
    }
    for (i, e) in ends.iter().enumerate() {
        if r < 0 && e[1] >= 0 {
            // SAFETY: our own pipe end.
            unsafe { libc::close(e[1]) };
        }
        // SAFETY: the library passes a live `GcBuf<i32>` of 3 elements.
        unsafe { *cell(out, i) = if r < 0 { -1 } else { e[1] } };
    }
    r
}

/// `waitpid`: the pid (status in `out[0]`), 0 if `nohang` and still
/// running, or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_waitpid(pid: i32, nohang: i32, out: *mut u8) -> i32 {
    let mut st = 0;
    let flags = if nohang != 0 { libc::WNOHANG } else { 0 };
    let (r, e) = native(|| {
        loop {
            // SAFETY: plain libc call.
            let r = unsafe { libc::waitpid(pid, &mut st, flags) };
            if r >= 0 || errno() != libc::EINTR {
                break r;
            }
        }
    });
    if r < 0 {
        return -e;
    }
    // SAFETY: a live one-element `GcBuf<i32>`.
    unsafe { *cell(out, 0) = st };
    r
}

/// Write end of the signal pipe (`rok_os_signal_install`), or -1.
static SIGNAL_PIPE: core::sync::atomic::AtomicI32 = core::sync::atomic::AtomicI32::new(-1);

/// The C handler: the signal number as one byte down the pipe. Only
/// async-signal-safe calls; a full pipe drops the signal.
extern "C" fn on_signal(sig: libc::c_int) {
    let fd = SIGNAL_PIPE.load(core::sync::atomic::Ordering::Relaxed);
    if fd >= 0 {
        let saved = errno();
        let b = sig as u8;
        // SAFETY: one byte from a local; `write` is async-signal-safe.
        unsafe {
            libc::write(fd, (&raw const b).cast(), 1);
            set_errno(saved);
        }
    }
}

/// Route signal `sig` to the signal pipe (`process::signal`). The first
/// call creates the pipe; `*read_end` gets its read end (blocking,
/// close-on-exec) on that call, -1 after. 0 or `-errno` (`EINVAL` for
/// `SIGKILL` / `SIGSTOP` / a bad number).
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_signal_install(sig: i32, read_end: *mut u8) -> i32 {
    // SAFETY: the library passes a live `GcBuf<i32>` of 1 element.
    unsafe { *cell(read_end, 0) = -1 };
    if !(1..64).contains(&sig) || sig == libc::SIGKILL || sig == libc::SIGSTOP {
        return -libc::EINVAL;
    }
    if SIGNAL_PIPE.load(core::sync::atomic::Ordering::Acquire) < 0 {
        let mut p = [0i32; 2];
        // SAFETY: `p` is writable; fcntl on our own fds.
        unsafe {
            if libc::pipe(p.as_mut_ptr()) < 0 {
                return -errno();
            }
            for fd in p {
                libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
            }
            let fl = libc::fcntl(p[1], libc::F_GETFL);
            libc::fcntl(p[1], libc::F_SETFL, fl | libc::O_NONBLOCK);
            *cell(read_end, 0) = p[0];
        }
        SIGNAL_PIPE.store(p[1], core::sync::atomic::Ordering::Release);
    }
    // SAFETY: a zeroed `sigaction` with the fields set below is valid.
    unsafe {
        let mut sa: libc::sigaction = core::mem::zeroed();
        sa.sa_sigaction = on_signal as *const () as libc::sighandler_t;
        sa.sa_flags = libc::SA_RESTART;
        libc::sigemptyset(&mut sa.sa_mask);
        if libc::sigaction(sig, &sa, ptr::null_mut()) < 0 {
            return -errno();
        }
    }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_os_raise(sig: i32) -> i32 {
    // SAFETY: plain libc call.
    if unsafe { libc::raise(sig) } != 0 {
        -libc::EINVAL
    } else {
        0
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_os_kill(pid: i32, sig: i32) -> i32 {
    // SAFETY: plain libc call.
    ret(unsafe { libc::kill(pid, sig) } as isize) as i32
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_os_getpid() -> u32 {
    // SAFETY: plain libc call.
    unsafe { libc::getpid() as u32 }
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_os_getppid() -> u32 {
    // SAFETY: plain libc call.
    unsafe { libc::getppid() as u32 }
}

/// Abnormal termination (`SIGABRT`), no cleanup.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_abort() -> ! {
    // SAFETY: never returns.
    unsafe { libc::abort() }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn errno_kinds() {
        assert_eq!(rok_os_errno_kind(libc::ENOENT), kind::NOT_FOUND);
        assert_eq!(rok_os_errno_kind(libc::EPERM), kind::PERMISSION_DENIED);
        assert_eq!(rok_os_errno_kind(libc::EACCES), kind::PERMISSION_DENIED);
        assert_eq!(rok_os_errno_kind(libc::EEXIST), kind::ALREADY_EXISTS);
        assert_eq!(rok_os_errno_kind(libc::ENOTSUP), kind::UNSUPPORTED);
        assert_eq!(rok_os_errno_kind(EAI_BASE + 8), kind::NOT_FOUND);
        assert_eq!(rok_os_errno_kind(0), kind::OTHER);
        assert_eq!(rok_os_errno_kind(-1), kind::OTHER);
    }
}
