//! POSIX helpers behind `rok::std` (stdlib 300: fs, io, env, process).
//! No ABI stability (805 §8.5.12 appendix).
//!
//! Conventions:
//! - `str` arguments are rok strings; every one is NUL-terminated
//!   (808), so `ptr` is passed to libc as a C string.
//! - Integer results: `>= 0` success, `-errno` failure.
//! - `str` results report failure through `err`, a one-element
//!   `GcBuf<i32>` (header pointer): `errno`, or 0 on success.
//! - Byte data travels as `str` values (GC byte strings); the library
//!   validates UTF-8 where a `str` reaches user code.
//! - Calls that may block are bracketed by `enter_native` /
//!   `leave_native` (804 §8.4.10) so a collection need not wait on them;
//!   GC strings are allocated only after leaving.

use core::mem::size_of;
use core::ptr;

use rokr_common::object_header::HEADER_SIZE;
use rokr_gc::world;

use crate::str::{RokStr, build};

type CStrPtr = *const libc::c_char;

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

pub const fn cs(s: RokStr) -> CStrPtr {
    s.ptr.cast()
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

/// Store `e` into the error cell `err` (may be null).
pub fn set_err(err: *mut u8, e: i32) {
    if !err.is_null() {
        // SAFETY: the library passes a live one-element `GcBuf<i32>`.
        unsafe { *cell(err, 0) = e };
    }
}

/// A malloc-backed byte vector (the runtime is `no_std`).
pub struct Bytes {
    pub p: *mut u8,
    pub len: usize,
    pub cap: usize,
}

impl Bytes {
    pub const fn new() -> Self {
        Self {
            p: ptr::null_mut(),
            len: 0,
            cap: 0,
        }
    }

    /// Room for `n` more bytes; returns the spare region.
    pub fn reserve(&mut self, n: usize) -> *mut u8 {
        if self.len + n > self.cap {
            let cap = (self.cap * 2).max(self.len + n).max(4096);
            // SAFETY: `p` is null or from malloc/realloc.
            let q = unsafe { libc::realloc(self.p.cast(), cap) }.cast::<u8>();
            if q.is_null() {
                rokr_common::oom();
            }
            self.p = q;
            self.cap = cap;
        }
        // SAFETY: `len <= cap`.
        unsafe { self.p.add(self.len) }
    }

    pub const fn as_slice(&self) -> &[u8] {
        if self.len == 0 {
            return &[];
        }
        // SAFETY: `p` holds `len` initialized bytes.
        unsafe { core::slice::from_raw_parts(self.p, self.len) }
    }
}

impl Drop for Bytes {
    fn drop(&mut self) {
        // SAFETY: null or a malloc block.
        unsafe { libc::free(self.p.cast()) };
    }
}

// ---------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------

/// `IoErrorKind` discriminant (library/std/io.rok order) of an errno.
#[unsafe(no_mangle)]
pub const extern "C" fn rok_os_errno_kind(code: i32) -> i32 {
    match code {
        libc::ENOENT => 1,
        libc::EACCES | libc::EPERM => 2,
        libc::EEXIST => 3,
        libc::ENOTDIR => 4,
        libc::EISDIR => 5,
        libc::ENOTEMPTY => 6,
        libc::EINVAL => 7,
        libc::EPIPE => 8,
        libc::EINTR => 9,
        libc::EAGAIN => 10,
        libc::ETIMEDOUT => 11,
        libc::ENOSPC => 12,
        libc::EXDEV => 13,
        libc::ENOSYS | libc::ENOTSUP => 14,
        _ => 0,
    }
}

/// `strerror(code)` as a `str`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_strerror(code: i32) -> RokStr {
    let mut buf = [0u8; 256];
    // SAFETY: `buf` is writable for its length.
    unsafe { libc::strerror_r(code, buf.as_mut_ptr().cast(), buf.len()) };
    let n = buf.iter().position(|&b| b == 0).unwrap_or(buf.len());
    build(&[&buf[..n]])
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
        libc::openat(at(dir), cs(path), o | libc::O_CLOEXEC, mode as libc::c_uint)
    });
    ret(r as isize) as i32
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_os_close(fd: i32) -> i32 {
    // SAFETY: plain libc call.
    ret(unsafe { libc::close(fd) } as isize) as i32
}

/// One `read` of up to `max` bytes as a byte `str` (empty = EOF).
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_read(fd: i32, max: usize, err: *mut u8) -> RokStr {
    let mut b = Bytes::new();
    let spare = b.reserve(max.max(1));
    let (n, e) = native(|| {
        loop {
            // SAFETY: `spare` is writable for `max` bytes.
            let n = unsafe { libc::read(fd, spare.cast(), max) };
            if n >= 0 || errno() != libc::EINTR {
                break n;
            }
        }
    });
    if n < 0 {
        set_err(err, e);
        return build(&[]);
    }
    set_err(err, 0);
    b.len = n as usize;
    build(&[b.as_slice()])
}

/// Everything up to EOF as a byte `str`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_read_all(fd: i32, err: *mut u8) -> RokStr {
    let mut b = Bytes::new();
    let (r, e) = native(|| {
        loop {
            let spare = b.reserve(16 * 1024);
            // SAFETY: `spare` is writable for 16 KiB.
            let n = unsafe { libc::read(fd, spare.cast(), 16 * 1024) };
            if n > 0 {
                b.len += n as usize;
            } else if n == 0 {
                return 0;
            } else if errno() != libc::EINTR {
                return -1;
            }
        }
    });
    set_err(err, if r < 0 { e } else { 0 });
    build(&[b.as_slice()])
}

/// One `write` of `s[off..]`: bytes written or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_write(fd: i32, s: RokStr, off: usize) -> isize {
    let off = off.min(s.len);
    let (n, e) = native(|| {
        loop {
            // SAFETY: `s` is valid for `len` bytes and kept alive by the caller.
            let n = unsafe { libc::write(fd, s.ptr.add(off).cast(), s.len - off) };
            if n >= 0 || errno() != libc::EINTR {
                break n;
            }
        }
    });
    if n < 0 { -(e as isize) } else { n }
}

/// All of `s`: 0 or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_write_all(fd: i32, s: RokStr) -> i32 {
    let mut off = 0;
    while off < s.len {
        let n = rok_os_write(fd, s, off);
        if n < 0 {
            return n as i32;
        }
        if n == 0 {
            return -libc::EIO;
        }
        off += n as usize;
    }
    0
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

/// `fstatat` (`fd < 0`) or `fstat(fd)`, filling the `GcBuf<i64>` `out`:
/// `[kind, size, mode, mtime_s, mtime_ns, atime_s, ctime_s]`, kind 1
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
            libc::fstatat(at(dir), cs(path), &mut st, flags)
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
    ];
    // SAFETY: the library passes a live `GcBuf<i64>` of 7 elements.
    unsafe { ptr::copy_nonoverlapping(vals.as_ptr(), out.add(HEADER_SIZE).cast(), vals.len()) };
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_os_mkdir(dir: i32, path: RokStr, mode: u32) -> i32 {
    // SAFETY: `path` is a C string.
    let (r, e) = native(|| unsafe { libc::mkdirat(at(dir), cs(path), mode as libc::mode_t) });
    if r < 0 { -e } else { 0 }
}

/// `unlinkat`; `is_dir != 0` removes an empty directory.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_unlink(dir: i32, path: RokStr, is_dir: i32) -> i32 {
    let flags = if is_dir != 0 { libc::AT_REMOVEDIR } else { 0 };
    // SAFETY: `path` is a C string.
    let (r, e) = native(|| unsafe { libc::unlinkat(at(dir), cs(path), flags) });
    if r < 0 { -e } else { 0 }
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_os_rename(dir: i32, from: RokStr, to_dir: i32, to: RokStr) -> i32 {
    // SAFETY: both are C strings.
    let (r, e) = native(|| unsafe { libc::renameat(at(dir), cs(from), at(to_dir), cs(to)) });
    if r < 0 { -e } else { 0 }
}

/// `hard == 0`: symlink `link` → `target`; else hard link.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_link(dir: i32, target: RokStr, link: RokStr, hard: i32) -> i32 {
    // SAFETY: both are C strings.
    let (r, e) = native(|| unsafe {
        if hard != 0 {
            libc::linkat(at(dir), cs(target), at(dir), cs(link), 0)
        } else {
            libc::symlinkat(cs(target), at(dir), cs(link))
        }
    });
    if r < 0 { -e } else { 0 }
}

/// Open `path` under `dir` for listing: a `DIR*` as `usize`, or 0.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_opendir(dir: i32, path: RokStr, err: *mut u8) -> usize {
    // SAFETY: `path` is a C string; `fdopendir` owns `fd` on success.
    let (d, e) = native(|| unsafe {
        let fd = libc::openat(
            at(dir),
            cs(path),
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
    set_err(err, if d.is_null() { e } else { 0 });
    d as usize
}

/// Next entry name (skipping `.` / `..`); `""` at the end or on error.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_readdir(d: usize, err: *mut u8) -> RokStr {
    loop {
        // SAFETY: errno reset distinguishes end from failure.
        unsafe { set_errno(0) };
        // SAFETY: `d` is a live `DIR*` from `rok_os_opendir`.
        let ent = unsafe { libc::readdir(d as *mut libc::DIR) };
        if ent.is_null() {
            set_err(err, errno());
            return build(&[]);
        }
        // SAFETY: `d_name` is NUL-terminated.
        let name = unsafe { core::ffi::CStr::from_ptr((*ent).d_name.as_ptr()) }.to_bytes();
        if name != b"." && name != b".." {
            set_err(err, 0);
            return build(&[name]);
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_os_closedir(d: usize) {
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

#[unsafe(no_mangle)]
pub extern "C" fn rok_os_getcwd(err: *mut u8) -> RokStr {
    let mut buf = [0u8; 4096];
    // SAFETY: `buf` is writable for its length.
    let p = unsafe { libc::getcwd(buf.as_mut_ptr().cast(), buf.len()) };
    if p.is_null() {
        set_err(err, errno());
        return build(&[]);
    }
    set_err(err, 0);
    let n = buf.iter().position(|&b| b == 0).unwrap_or(0);
    build(&[&buf[..n]])
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_os_chdir(path: RokStr) -> i32 {
    // SAFETY: `path` is a C string.
    ret(unsafe { libc::chdir(cs(path)) } as isize) as i32
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_os_realpath(path: RokStr, err: *mut u8) -> RokStr {
    let mut buf = [0u8; libc::PATH_MAX as usize + 1];
    // SAFETY: `buf` has PATH_MAX bytes.
    let (p, e) = native(|| unsafe { libc::realpath(cs(path), buf.as_mut_ptr().cast()) });
    if p.is_null() {
        set_err(err, e);
        return build(&[]);
    }
    set_err(err, 0);
    let n = buf.iter().position(|&b| b == 0).unwrap_or(0);
    build(&[&buf[..n]])
}

#[cfg(target_vendor = "apple")]
unsafe extern "C" {
    #[link_name = "_NSGetExecutablePath"]
    fn ns_get_executable_path(buf: *mut libc::c_char, size: *mut u32) -> i32;
}

/// Absolute path of the running executable (`env::current_exe`).
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_current_exe(err: *mut u8) -> RokStr {
    let mut buf = [0u8; libc::PATH_MAX as usize + 1];
    #[cfg(target_vendor = "apple")]
    let path = {
        let mut raw = [0u8; libc::PATH_MAX as usize + 1];
        let mut size = raw.len() as u32;
        // SAFETY: `raw` is writable for `size` bytes.
        if unsafe { ns_get_executable_path(raw.as_mut_ptr().cast(), &mut size) } != 0 {
            set_err(err, libc::ENAMETOOLONG);
            return build(&[]);
        }
        // SAFETY: `raw` is NUL-terminated; `buf` has PATH_MAX bytes.
        if unsafe { libc::realpath(raw.as_ptr().cast(), buf.as_mut_ptr().cast()) }.is_null() {
            set_err(err, errno());
            return build(&[]);
        }
        let n = buf.iter().position(|&b| b == 0).unwrap_or(0);
        &buf[..n]
    };
    #[cfg(not(target_vendor = "apple"))]
    let path = {
        // SAFETY: `buf` is writable for its length.
        let n = unsafe {
            libc::readlink(
                c"/proc/self/exe".as_ptr(),
                buf.as_mut_ptr().cast(),
                buf.len(),
            )
        };
        if n < 0 {
            set_err(err, errno());
            return build(&[]);
        }
        &buf[..n as usize]
    };
    set_err(err, 0);
    build(&[path])
}

// ---------------------------------------------------------------------
// Standard streams (stdio `FILE`s, so they order with `print`)
// ---------------------------------------------------------------------

fn stdin_file() -> *mut libc::FILE {
    unsafe extern "C" {
        #[cfg_attr(target_vendor = "apple", link_name = "__stdinp")]
        static mut stdin: *mut libc::FILE;
    }
    // SAFETY: libc initializes `stdin` before `main`.
    unsafe { stdin }
}

/// One line of stdin with its `\n` (`""` = EOF).
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_stdin_line(err: *mut u8) -> RokStr {
    let mut line: *mut libc::c_char = ptr::null_mut();
    let mut cap: libc::size_t = 0;
    // SAFETY: getline allocates `line`; we free it below.
    let (n, e) = native(|| unsafe { libc::getline(&mut line, &mut cap, stdin_file()) });
    // SAFETY: `ferror` on a live stream.
    let failed = n < 0 && unsafe { libc::ferror(stdin_file()) } != 0;
    set_err(err, if failed { e } else { 0 });
    let out = if n > 0 {
        // SAFETY: getline wrote `n` bytes.
        build(&[unsafe { core::slice::from_raw_parts(line.cast::<u8>(), n as usize) }])
    } else {
        build(&[])
    };
    // SAFETY: from getline (or null).
    unsafe { libc::free(line.cast()) };
    out
}

/// Up to `max` bytes of stdin (`""` = EOF; `max == 0` = all of it).
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_stdin_read(max: usize, err: *mut u8) -> RokStr {
    let mut b = Bytes::new();
    let (failed, e) = native(|| {
        loop {
            let want = if max == 0 { 16 * 1024 } else { max - b.len };
            let spare = b.reserve(want);
            // SAFETY: `spare` is writable for `want` bytes.
            let n = unsafe { libc::fread(spare.cast(), 1, want, stdin_file()) };
            b.len += n;
            if n < want || max != 0 {
                // SAFETY: live stream.
                return unsafe { libc::ferror(stdin_file()) } != 0;
            }
        }
    });
    set_err(err, if failed { e } else { 0 });
    build(&[b.as_slice()])
}

/// `fflush(stdout)`: 0 or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_flush_stdout() -> i32 {
    // SAFETY: flushing a live stream.
    let (r, e) = native(|| unsafe { libc::fflush(crate::stdout()) });
    if r != 0 { -e } else { 0 }
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

/// `getenv`; `found` cell = 1 if set.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_getenv(name: RokStr, found: *mut u8) -> RokStr {
    // SAFETY: `name` is a C string.
    let p = unsafe { libc::getenv(cs(name)) };
    set_err(found, i32::from(!p.is_null()));
    from_c(p)
}

/// `setenv` (`value` given) / `unsetenv`. 0 or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_os_setenv(name: RokStr, value: RokStr, unset: i32) -> i32 {
    // SAFETY: C strings. ponytail: no global env lock (spec 306.3).
    let r = unsafe {
        if unset != 0 {
            libc::unsetenv(cs(name))
        } else {
            libc::setenv(cs(name), cs(value), 1)
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
/// `cwd` empty = inherit. Stdio modes: `-1` inherit, `-2` null,
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
    out: *mut u8,
) -> i32 {
    let av = split_blob(argv, argc);
    let ev = if envc >= 0 {
        split_blob(envs, envc as usize)
    } else {
        ptr::null_mut()
    };
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
                if cwd.len > 0 && libc::chdir(cs(cwd)) < 0 {
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

/// Drain two pipes to EOF together (`poll`), so a child filling one
/// while the other is unread cannot deadlock (`Command::output`).
/// Stores the bytes as `str`s into `out[0]` / `out[1]` (a
/// `GcBuf<str>`); `err` gets the errno, or 0.
#[unsafe(no_mangle)]
#[allow(clippy::cast_ptr_alignment)] // GC payloads are 8-aligned
pub extern "C" fn rok_os_read_both(fd1: i32, fd2: i32, out: *mut u8, err: *mut u8) {
    let mut bufs = [Bytes::new(), Bytes::new()];
    let (r, e) = native(|| {
        let mut fds = [
            libc::pollfd {
                fd: fd1,
                events: libc::POLLIN,
                revents: 0,
            },
            libc::pollfd {
                fd: fd2,
                events: libc::POLLIN,
                revents: 0,
            },
        ];
        loop {
            if fds.iter().all(|p| p.fd < 0) {
                return 0;
            }
            // SAFETY: `fds` holds two entries; negative fds are ignored.
            if unsafe { libc::poll(fds.as_mut_ptr(), 2, -1) } < 0 {
                if errno() == libc::EINTR {
                    continue;
                }
                return -1;
            }
            for (p, b) in fds.iter_mut().zip(bufs.iter_mut()) {
                if p.fd < 0 || p.revents == 0 {
                    continue;
                }
                let spare = b.reserve(16 * 1024);
                // SAFETY: `spare` is writable for 16 KiB.
                let n = unsafe { libc::read(p.fd, spare.cast(), 16 * 1024) };
                if n > 0 {
                    b.len += n as usize;
                } else if n == 0 {
                    p.fd = -1;
                } else if errno() != libc::EINTR && errno() != libc::EAGAIN {
                    return -1;
                }
            }
        }
    });
    set_err(err, if r < 0 { e } else { 0 });
    let slots = out.wrapping_add(HEADER_SIZE).cast::<RokStr>();
    // Store each string before allocating the next: `out` (rooted by
    // the caller) keeps the first alive across the second allocation.
    for (i, b) in bufs.iter().enumerate() {
        let st = build(&[b.as_slice()]);
        // SAFETY: the library passes a live two-element `GcBuf<str>`.
        unsafe { slots.add(i).write(st) };
    }
}

/// Bytes `start..end` of `s` as a new `str`, with no UTF-8 boundary
/// check (raw byte buffers inside `rok::std::io`).
#[unsafe(no_mangle)]
pub extern "C" fn rok_bytes_slice(s: RokStr, start: usize, end: usize) -> RokStr {
    let end = end.min(s.len);
    let start = start.min(end);
    if end == start {
        return build(&[]);
    }
    // SAFETY: `start..end` lies within `s`.
    build(&[unsafe { core::slice::from_raw_parts(s.ptr.add(start), end - start) }])
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

// ---------------------------------------------------------------------
// Byte buffers (`StrBuf`, byte lists)
// ---------------------------------------------------------------------

/// `len` bytes of the `GcBuf<u8>` `buf` from `off`, as a new `str`.
///
/// # Safety
/// `buf` must be a live `GcBuf<u8>` with at least `off + len` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_str_from_buf(buf: *mut u8, off: usize, len: usize) -> RokStr {
    // SAFETY: caller contract. `build` may collect before copying; the
    // caller's frame roots `buf` and the collector does not move objects.
    build(&[unsafe { core::slice::from_raw_parts(buf.add(HEADER_SIZE + off), len) }])
}

/// Copy `s` into the `GcBuf<u8>` `buf` at `off`.
///
/// # Safety
/// `buf` must be a live `GcBuf<u8>` with at least `off + s.len` bytes.
#[unsafe(no_mangle)]
pub const unsafe extern "C" fn rok_buf_put_str(buf: *mut u8, off: usize, s: RokStr) {
    if s.len > 0 {
        // SAFETY: caller contract.
        unsafe { ptr::copy_nonoverlapping(s.ptr, buf.add(HEADER_SIZE + off), s.len) };
    }
}

/// Index of the first invalid UTF-8 byte of `s`, or -1 if valid.
#[unsafe(no_mangle)]
pub extern "C" fn rok_str_utf8_error(s: RokStr) -> isize {
    let b = if s.len == 0 {
        &[][..]
    } else {
        // SAFETY: a `str` is valid for `len` bytes.
        unsafe { core::slice::from_raw_parts(s.ptr, s.len) }
    };
    match core::str::from_utf8(b) {
        Ok(_) => -1,
        Err(e) => e.valid_up_to() as isize,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn errno_kinds() {
        assert_eq!(rok_os_errno_kind(libc::ENOENT), 1);
        assert_eq!(rok_os_errno_kind(libc::EPERM), 2);
        assert_eq!(rok_os_errno_kind(libc::EACCES), 2);
        assert_eq!(rok_os_errno_kind(libc::EEXIST), 3);
        assert_eq!(rok_os_errno_kind(libc::ENOTSUP), 14);
        assert_eq!(rok_os_errno_kind(0), 0);
        assert_eq!(rok_os_errno_kind(-1), 0);
    }

    #[test]
    fn utf8_error_offset() {
        let s = |b: &'static [u8]| RokStr {
            ptr: b.as_ptr(),
            len: b.len(),
        };
        assert_eq!(rok_str_utf8_error(s(b"")), -1);
        assert_eq!(rok_str_utf8_error(s("a한".as_bytes())), -1);
        assert_eq!(rok_str_utf8_error(s(b"ab\xFFc")), 2);
        // A truncated multi-byte sequence fails at its first byte.
        assert_eq!(rok_str_utf8_error(s(b"a\xED\x95")), 1);
    }
}
