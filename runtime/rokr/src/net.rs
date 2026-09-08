//! Sockets behind `rok::std::net` (stdlib 302) and the readiness poller
//! of the I/O driver (707): kqueue on BSD / macOS, epoll on Linux. No
//! ABI stability (805 §8.5.12 appendix). Conventions as in `os`:
//! integer results are `>= 0` or `-errno`.
//!
//! Every socket is created non-blocking: the library's blocking calls
//! wait for readiness with [`rok_net_wait`] (so read / write timeouts
//! are the `poll` timeout), its async calls park the task until the
//! driver thread sees the fd ready.
//!
//! Addresses cross as a `GcBuf<i64>` of [`ADDR_WORDS`] words:
//! `[family (4 / 6), port, flow_info, scope_id, byte0 .. byte15]`.

use core::mem::{size_of, zeroed};
use core::sync::atomic::{AtomicBool, AtomicI32, Ordering};

use rokr_common::object_header::HEADER_SIZE;

use crate::os::{Bytes, cs, errno, native, ret, set_err};
use crate::str::{RokStr, build};

const ADDR_WORDS: usize = 20;

/// Word `i` of the `GcBuf<i64>` `buf`.
///
/// # Safety
/// `buf` must be a live `GcBuf<i64>` with more than `i` elements.
#[allow(clippy::cast_ptr_alignment)] // GC payloads are 8-aligned
const unsafe fn word(buf: *mut u8, i: usize) -> *mut i64 {
    // SAFETY: caller contract.
    unsafe { buf.add(HEADER_SIZE).cast::<i64>().add(i) }
}

/// The address in `buf` as a `sockaddr_storage` and its length.
fn read_addr(buf: *mut u8) -> (libc::sockaddr_storage, libc::socklen_t) {
    // SAFETY: the library passes a live `ADDR_WORDS` buffer; the storage
    // is large enough for either family.
    unsafe {
        let w = |i| *word(buf, i);
        let mut ss: libc::sockaddr_storage = zeroed();
        let port = (w(1) as u16).to_be();
        if w(0) == 6 {
            let a = (&raw mut ss).cast::<libc::sockaddr_in6>();
            (*a).sin6_family = libc::AF_INET6 as libc::sa_family_t;
            (*a).sin6_port = port;
            (*a).sin6_flowinfo = w(2) as u32;
            (*a).sin6_scope_id = w(3) as u32;
            for i in 0..16 {
                (*a).sin6_addr.s6_addr[i] = w(4 + i) as u8;
            }
            set_len(&raw mut ss, size_of::<libc::sockaddr_in6>());
            (ss, size_of::<libc::sockaddr_in6>() as libc::socklen_t)
        } else {
            let a = (&raw mut ss).cast::<libc::sockaddr_in>();
            (*a).sin_family = libc::AF_INET as libc::sa_family_t;
            (*a).sin_port = port;
            let b = [w(4) as u8, w(5) as u8, w(6) as u8, w(7) as u8];
            (*a).sin_addr.s_addr = u32::from_ne_bytes(b);
            set_len(&raw mut ss, size_of::<libc::sockaddr_in>());
            (ss, size_of::<libc::sockaddr_in>() as libc::socklen_t)
        }
    }
}

/// BSD sockaddrs carry their length.
#[allow(clippy::missing_const_for_fn)]
unsafe fn set_len(ss: *mut libc::sockaddr_storage, n: usize) {
    #[cfg(any(target_vendor = "apple", target_os = "freebsd"))]
    // SAFETY: caller passes a valid storage.
    unsafe {
        (*ss).ss_len = n as u8;
    }
    let _ = (ss, n);
}

/// Store the address at `sa` into `buf` (no-op for a null `buf`).
#[allow(clippy::cast_ptr_alignment)] // a sockaddr of its own family
fn write_addr(buf: *mut u8, sa: *const libc::sockaddr) {
    if buf.is_null() {
        return;
    }
    // SAFETY: `sa` points at a sockaddr of its own family; `buf` is a
    // live `ADDR_WORDS` buffer.
    unsafe {
        let put = |i, v: i64| *word(buf, i) = v;
        for i in 0..ADDR_WORDS {
            put(i, 0);
        }
        if i32::from((*sa).sa_family) == libc::AF_INET6 {
            let a = sa.cast::<libc::sockaddr_in6>();
            put(0, 6);
            put(1, i64::from(u16::from_be((*a).sin6_port)));
            put(2, i64::from((*a).sin6_flowinfo));
            put(3, i64::from((*a).sin6_scope_id));
            for i in 0..16 {
                put(4 + i, i64::from((*a).sin6_addr.s6_addr[i]));
            }
        } else {
            let a = sa.cast::<libc::sockaddr_in>();
            put(0, 4);
            put(1, i64::from(u16::from_be((*a).sin_port)));
            for (i, b) in (*a).sin_addr.s_addr.to_ne_bytes().iter().enumerate() {
                put(4 + i, i64::from(*b));
            }
        }
    }
}

/// Non-blocking + close-on-exec.
fn prepare(fd: i32) -> i32 {
    // SAFETY: plain fcntl calls on an fd we own.
    unsafe {
        let fl = libc::fcntl(fd, libc::F_GETFL);
        if fl < 0 || libc::fcntl(fd, libc::F_SETFL, fl | libc::O_NONBLOCK) < 0 {
            return -errno();
        }
        if libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) < 0 {
            return -errno();
        }
        #[cfg(target_vendor = "apple")]
        {
            let on: libc::c_int = 1;
            libc::setsockopt(
                fd,
                libc::SOL_SOCKET,
                libc::SO_NOSIGPIPE,
                (&raw const on).cast(),
                size_of::<libc::c_int>() as libc::socklen_t,
            );
        }
    }
    0
}

/// `send` flags: no SIGPIPE where the flag exists.
#[cfg(not(target_vendor = "apple"))]
const SEND_FLAGS: libc::c_int = libc::MSG_NOSIGNAL;
#[cfg(target_vendor = "apple")]
const SEND_FLAGS: libc::c_int = 0;

/// A new non-blocking socket: `family` 4 / 6, `kind` 1 stream / 2
/// datagram. The fd or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_net_socket(family: i32, kind: i32) -> i32 {
    let af = if family == 6 {
        libc::AF_INET6
    } else {
        libc::AF_INET
    };
    let ty = if kind == 2 {
        libc::SOCK_DGRAM
    } else {
        libc::SOCK_STREAM
    };
    // SAFETY: plain libc call.
    let fd = unsafe { libc::socket(af, ty, 0) };
    if fd < 0 {
        return -errno();
    }
    let r = prepare(fd);
    if r < 0 {
        // SAFETY: our fd.
        unsafe { libc::close(fd) };
        return r;
    }
    fd
}

/// `bind` (stream sockets get `SO_REUSEADDR` first).
#[unsafe(no_mangle)]
pub extern "C" fn rok_net_bind(fd: i32, addr: *mut u8) -> i32 {
    let (ss, len) = read_addr(addr);
    // SAFETY: valid sockaddr / option pointers.
    unsafe {
        let mut ty: libc::c_int = 0;
        let mut n = size_of::<libc::c_int>() as libc::socklen_t;
        libc::getsockopt(
            fd,
            libc::SOL_SOCKET,
            libc::SO_TYPE,
            (&raw mut ty).cast(),
            &raw mut n,
        );
        if ty == libc::SOCK_STREAM {
            let on: libc::c_int = 1;
            libc::setsockopt(
                fd,
                libc::SOL_SOCKET,
                libc::SO_REUSEADDR,
                (&raw const on).cast(),
                size_of::<libc::c_int>() as libc::socklen_t,
            );
        }
        ret(libc::bind(fd, (&raw const ss).cast(), len) as isize) as i32
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_net_listen(fd: i32, backlog: i32) -> i32 {
    // SAFETY: plain libc call.
    ret(unsafe { libc::listen(fd, backlog) } as isize) as i32
}

/// Start a connect: 0 when connected, `-EINPROGRESS` while pending
/// (wait for writability, then [`rok_net_sock_error`]).
#[unsafe(no_mangle)]
pub extern "C" fn rok_net_connect(fd: i32, addr: *mut u8) -> i32 {
    let (ss, len) = read_addr(addr);
    loop {
        // SAFETY: valid sockaddr.
        let r = unsafe { libc::connect(fd, (&raw const ss).cast(), len) };
        if r == 0 {
            return 0;
        }
        let e = errno();
        if e != libc::EINTR {
            return -e;
        }
    }
}

/// The pending error of `fd` (`SO_ERROR`): 0 or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_net_sock_error(fd: i32) -> i32 {
    let mut e: libc::c_int = 0;
    let mut n = size_of::<libc::c_int>() as libc::socklen_t;
    // SAFETY: valid out-pointers.
    let r = unsafe {
        libc::getsockopt(
            fd,
            libc::SOL_SOCKET,
            libc::SO_ERROR,
            (&raw mut e).cast(),
            &raw mut n,
        )
    };
    if r < 0 { -errno() } else { -e }
}

/// Accept one connection (non-blocking: `-EAGAIN` if none is queued);
/// its peer goes to `out`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_net_accept(fd: i32, out: *mut u8) -> i32 {
    // SAFETY: zeroed storage is a valid out-buffer.
    let mut ss: libc::sockaddr_storage = unsafe { zeroed() };
    let mut len = size_of::<libc::sockaddr_storage>() as libc::socklen_t;
    let c = loop {
        // SAFETY: valid out-pointers.
        let c = unsafe { libc::accept(fd, (&raw mut ss).cast(), &raw mut len) };
        if c >= 0 || errno() != libc::EINTR {
            break c;
        }
    };
    if c < 0 {
        return -errno();
    }
    let r = prepare(c);
    if r < 0 {
        // SAFETY: our fd.
        unsafe { libc::close(c) };
        return r;
    }
    write_addr(out, (&raw const ss).cast());
    c
}

/// The local (`peer == 0`) or peer address of `fd` into `out`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_net_addr(fd: i32, out: *mut u8, peer: i32) -> i32 {
    // SAFETY: zeroed storage is a valid out-buffer.
    let mut ss: libc::sockaddr_storage = unsafe { zeroed() };
    let mut len = size_of::<libc::sockaddr_storage>() as libc::socklen_t;
    // SAFETY: valid out-pointers.
    let r = unsafe {
        if peer == 0 {
            libc::getsockname(fd, (&raw mut ss).cast(), &raw mut len)
        } else {
            libc::getpeername(fd, (&raw mut ss).cast(), &raw mut len)
        }
    };
    if r < 0 {
        return -errno();
    }
    write_addr(out, (&raw const ss).cast());
    0
}

/// One `send` of `s[off..]` (no SIGPIPE): bytes written or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_net_send(fd: i32, s: RokStr, off: usize) -> isize {
    let off = off.min(s.len);
    loop {
        // SAFETY: `s` is valid for `len` bytes.
        let n = unsafe { libc::send(fd, s.ptr.add(off).cast(), s.len - off, SEND_FLAGS) };
        if n >= 0 {
            return n;
        }
        let e = errno();
        if e != libc::EINTR {
            return -(e as isize);
        }
    }
}

/// One datagram `s` to `addr`: bytes sent or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_net_send_to(fd: i32, s: RokStr, addr: *mut u8) -> isize {
    let (ss, len) = read_addr(addr);
    loop {
        // SAFETY: valid buffer and sockaddr.
        let n = unsafe {
            libc::sendto(
                fd,
                s.ptr.cast(),
                s.len,
                SEND_FLAGS,
                (&raw const ss).cast(),
                len,
            )
        };
        if n >= 0 {
            return n;
        }
        let e = errno();
        if e != libc::EINTR {
            return -(e as isize);
        }
    }
}

/// One `recvfrom` of up to `max` bytes; the sender goes to `out` (may be
/// null), failures to the error cell `err`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_net_recv_from(fd: i32, max: usize, out: *mut u8, err: *mut u8) -> RokStr {
    let mut b = Bytes::new();
    let spare = b.reserve(max.max(1));
    // SAFETY: zeroed storage is a valid out-buffer.
    let mut ss: libc::sockaddr_storage = unsafe { zeroed() };
    let mut len = size_of::<libc::sockaddr_storage>() as libc::socklen_t;
    let n = loop {
        // SAFETY: `spare` is writable for `max` bytes.
        let n =
            unsafe { libc::recvfrom(fd, spare.cast(), max, 0, (&raw mut ss).cast(), &raw mut len) };
        if n >= 0 || errno() != libc::EINTR {
            break n;
        }
    };
    if n < 0 {
        set_err(err, errno());
        return build(&[]);
    }
    set_err(err, 0);
    if len > 0 {
        write_addr(out, (&raw const ss).cast());
    }
    b.len = n as usize;
    build(&[b.as_slice()])
}

/// `shutdown`: `how` 0 read, 1 write, 2 both.
#[unsafe(no_mangle)]
pub extern "C" fn rok_net_shutdown(fd: i32, how: i32) -> i32 {
    let h = match how {
        0 => libc::SHUT_RD,
        1 => libc::SHUT_WR,
        _ => libc::SHUT_RDWR,
    };
    // SAFETY: plain libc call.
    ret(unsafe { libc::shutdown(fd, h) } as isize) as i32
}

fn setopt(fd: i32, level: libc::c_int, name: libc::c_int, v: libc::c_int) -> i32 {
    // SAFETY: valid option pointer.
    let r = unsafe {
        libc::setsockopt(
            fd,
            level,
            name,
            (&raw const v).cast(),
            size_of::<libc::c_int>() as libc::socklen_t,
        )
    };
    ret(r as isize) as i32
}

/// Socket options by library code: 1 `TCP_NODELAY`, 2 keepalive (`val`
/// idle seconds, < 0 off), 3 `SO_BROADCAST`, 4 `IP_MULTICAST_LOOP`, 5
/// `IP_MULTICAST_TTL`, 6 `UDP_SEGMENT` (Linux only).
#[unsafe(no_mangle)]
pub extern "C" fn rok_net_setopt(fd: i32, opt: i32, val: i64) -> i32 {
    let v = val as libc::c_int;
    match opt {
        1 => setopt(fd, libc::IPPROTO_TCP, libc::TCP_NODELAY, v),
        2 => {
            let r = setopt(fd, libc::SOL_SOCKET, libc::SO_KEEPALIVE, i32::from(v >= 0));
            if r < 0 || v < 0 {
                return r;
            }
            #[cfg(target_vendor = "apple")]
            let idle = libc::TCP_KEEPALIVE;
            #[cfg(not(target_vendor = "apple"))]
            let idle = libc::TCP_KEEPIDLE;
            setopt(fd, libc::IPPROTO_TCP, idle, v.max(1))
        }
        3 => setopt(fd, libc::SOL_SOCKET, libc::SO_BROADCAST, v),
        4 => {
            // SAFETY: a one-byte option on BSD.
            #[cfg(target_vendor = "apple")]
            unsafe {
                let b = u8::from(v != 0);
                ret(libc::setsockopt(
                    fd,
                    libc::IPPROTO_IP,
                    libc::IP_MULTICAST_LOOP,
                    (&raw const b).cast(),
                    1,
                ) as isize) as i32
            }
            #[cfg(not(target_vendor = "apple"))]
            setopt(fd, libc::IPPROTO_IP, libc::IP_MULTICAST_LOOP, v)
        }
        5 => setopt(fd, libc::IPPROTO_IP, libc::IP_MULTICAST_TTL, v),
        #[cfg(target_os = "linux")]
        6 => setopt(fd, libc::SOL_UDP, libc::UDP_SEGMENT, v),
        _ => -libc::ENOTSUP,
    }
}

/// Join (`join != 0`) or leave IPv4 multicast `group` on `iface` (both
/// as `a.b.c.d` octets in a big-endian `u32`).
#[unsafe(no_mangle)]
pub extern "C" fn rok_net_multicast_v4(fd: i32, group: u32, iface: u32, join: i32) -> i32 {
    let m = libc::ip_mreq {
        imr_multiaddr: libc::in_addr {
            s_addr: group.to_be(),
        },
        imr_interface: libc::in_addr {
            s_addr: iface.to_be(),
        },
    };
    let name = if join != 0 {
        libc::IP_ADD_MEMBERSHIP
    } else {
        libc::IP_DROP_MEMBERSHIP
    };
    // SAFETY: valid option pointer.
    let r = unsafe {
        libc::setsockopt(
            fd,
            libc::IPPROTO_IP,
            name,
            (&raw const m).cast(),
            size_of::<libc::ip_mreq>() as libc::socklen_t,
        )
    };
    ret(r as isize) as i32
}

/// Block (parked for the GC) until `fd` is readable (`write == 0`) or
/// writable, at most `timeout_ns` (< 0: no limit). 1 ready, 0 timed out,
/// or `-errno`. Hang-ups and errors count as ready (the next call
/// reports them).
#[unsafe(no_mangle)]
pub extern "C" fn rok_net_wait(fd: i32, write: i32, timeout_ns: i64) -> i32 {
    let mut p = libc::pollfd {
        fd,
        events: if write != 0 {
            libc::POLLOUT
        } else {
            libc::POLLIN
        },
        revents: 0,
    };
    let ms = if timeout_ns < 0 {
        -1
    } else {
        // Round up: a 1 ns timeout still waits one tick.
        (timeout_ns.saturating_add(999_999) / 1_000_000).min(i64::from(i32::MAX)) as libc::c_int
    };
    let mut poll = |ms| {
        loop {
            // SAFETY: one valid pollfd.
            let r = unsafe { libc::poll(&raw mut p, 1, ms) };
            if r >= 0 || errno() != libc::EINTR {
                break r;
            }
        }
    };
    if ms == 0 {
        let r = poll(0);
        return if r < 0 { -errno() } else { i32::from(r > 0) };
    }
    let (r, e) = native(|| poll(ms));
    if r < 0 { -e } else { i32::from(r > 0) }
}

/// `EAI_*` results of [`rok_net_resolve`] are `-(EAI_BASE + code)`.
const EAI_BASE: i32 = 100_000;

/// Resolve `host` (a name or numeric address) with `port`: up to `max`
/// addresses into `out` (`max * ADDR_WORDS` words), stream sockets only.
/// The count, `-errno`, or `-(100000 + EAI_*)`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_net_resolve(host: RokStr, port: u16, out: *mut u8, max: usize) -> i32 {
    // SAFETY: zeroed hints are valid; `host` is NUL-terminated (808).
    let mut hints: libc::addrinfo = unsafe { zeroed() };
    hints.ai_socktype = libc::SOCK_STREAM;
    let mut res: *mut libc::addrinfo = core::ptr::null_mut();
    let (r, e) = native(|| unsafe {
        libc::getaddrinfo(cs(host), core::ptr::null(), &raw const hints, &raw mut res)
    });
    if r != 0 {
        if r == libc::EAI_SYSTEM {
            return -e;
        }
        return -(EAI_BASE + r.abs());
    }
    let mut n = 0;
    let mut p = res;
    while !p.is_null() && n < max {
        // SAFETY: a list from getaddrinfo; `out` has room for `max`.
        unsafe {
            let fam = (*p).ai_family;
            if fam == libc::AF_INET || fam == libc::AF_INET6 {
                let slot = out.add(n * ADDR_WORDS * 8);
                write_addr(slot, (*p).ai_addr);
                *word(slot, 1) = i64::from(port);
                n += 1;
            }
            p = (*p).ai_next;
        }
    }
    // SAFETY: from getaddrinfo.
    unsafe { libc::freeaddrinfo(res) };
    n as i32
}

/// Message of a [`rok_net_resolve`] `EAI_*` code (without the base).
#[unsafe(no_mangle)]
pub extern "C" fn rok_net_gai_strerror(code: i32) -> RokStr {
    // Platforms number EAI codes negative (glibc) or positive (BSD).
    #[cfg(target_os = "linux")]
    let c = -code;
    #[cfg(not(target_os = "linux"))]
    let c = code;
    // SAFETY: gai_strerror returns a static C string.
    let s = unsafe { libc::gai_strerror(c) };
    // SAFETY: as above.
    let n = unsafe { libc::strlen(s) };
    // SAFETY: `s` is valid for `n` bytes.
    build(&[unsafe { core::slice::from_raw_parts(s.cast::<u8>(), n) }])
}

// ---------------------------------------------------------------------
// The I/O driver's poller (707 §7.7.1)
// ---------------------------------------------------------------------

static POLLER: AtomicI32 = AtomicI32::new(-1);
static CLAIMED: AtomicBool = AtomicBool::new(false);

/// The process's kqueue / epoll fd, created on first use.
#[unsafe(no_mangle)]
pub extern "C" fn rok_io_poller() -> i32 {
    let p = POLLER.load(Ordering::Acquire);
    if p >= 0 {
        return p;
    }
    // SAFETY: plain libc calls.
    #[cfg(any(target_vendor = "apple", target_os = "freebsd"))]
    let fd = unsafe {
        let fd = libc::kqueue();
        if fd >= 0 {
            libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
        }
        fd
    };
    // SAFETY: plain libc call.
    #[cfg(target_os = "linux")]
    let fd = unsafe { libc::epoll_create1(libc::EPOLL_CLOEXEC) };
    if fd < 0 {
        rokr_common::fatal(b"rok: cannot create the I/O poller\n");
    }
    match POLLER.compare_exchange(-1, fd, Ordering::AcqRel, Ordering::Acquire) {
        Ok(_) => fd,
        Err(cur) => {
            // SAFETY: our own extra fd.
            unsafe { libc::close(fd) };
            cur
        }
    }
}

/// 1 for the first caller only (it starts the driver thread).
#[unsafe(no_mangle)]
pub extern "C" fn rok_io_driver_claim() -> i32 {
    i32::from(!CLAIMED.swap(true, Ordering::AcqRel))
}

/// Watch `fd` for readability and writability, edge-triggered (an
/// event per change, so a waiter must re-check after it parks). Watching
/// a watched fd again is harmless. 0 or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_io_watch(fd: i32) -> i32 {
    let p = rok_io_poller();
    #[cfg(any(target_vendor = "apple", target_os = "freebsd"))]
    {
        // SAFETY: zeroed kevents are valid; filled below.
        let mut ch: [libc::kevent; 2] = unsafe { zeroed() };
        for (k, filter) in ch.iter_mut().zip([libc::EVFILT_READ, libc::EVFILT_WRITE]) {
            k.ident = fd as libc::uintptr_t;
            k.filter = filter;
            k.flags = libc::EV_ADD | libc::EV_CLEAR;
        }
        // SAFETY: two valid changes, no event buffer.
        let r = unsafe {
            libc::kevent(
                p,
                ch.as_ptr(),
                2,
                core::ptr::null_mut(),
                0,
                core::ptr::null(),
            )
        };
        ret(r as isize) as i32
    }
    #[cfg(target_os = "linux")]
    {
        let mut ev = libc::epoll_event {
            events: (libc::EPOLLIN | libc::EPOLLOUT | libc::EPOLLRDHUP | libc::EPOLLET) as u32,
            u64: fd as u64,
        };
        // SAFETY: a valid event.
        let r = unsafe { libc::epoll_ctl(p, libc::EPOLL_CTL_ADD, fd, &raw mut ev) };
        if r < 0 && errno() == libc::EEXIST {
            return 0;
        }
        ret(r as isize) as i32
    }
}

/// Block (parked for the GC) until watched fds change; up to `max`
/// events go to the `GcBuf<i64>` `out` as `fd * 2 + (0 read | 1 write)`.
/// The count, or `-errno`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_io_poll(out: *mut u8, max: usize) -> i32 {
    const N: usize = 64;
    let p = rok_io_poller();
    let mut keys = [0i64; 2 * N];
    let (n, e) = native(|| {
        let mut n = 0usize;
        #[cfg(any(target_vendor = "apple", target_os = "freebsd"))]
        {
            // SAFETY: zeroed kevents are a valid out-buffer.
            let mut evs: [libc::kevent; N] = unsafe { zeroed() };
            // SAFETY: valid buffer; no timeout.
            let r = unsafe {
                libc::kevent(
                    p,
                    core::ptr::null(),
                    0,
                    evs.as_mut_ptr(),
                    N as libc::c_int,
                    core::ptr::null(),
                )
            };
            if r < 0 {
                return -1;
            }
            for ev in &evs[..r as usize] {
                let dir = i64::from(ev.filter == libc::EVFILT_WRITE);
                keys[n] = ev.ident as i64 * 2 + dir;
                n += 1;
            }
        }
        #[cfg(target_os = "linux")]
        {
            // SAFETY: zeroed events are a valid out-buffer.
            let mut evs: [libc::epoll_event; N] = unsafe { zeroed() };
            // SAFETY: valid buffer.
            let r = unsafe { libc::epoll_wait(p, evs.as_mut_ptr(), N as libc::c_int, -1) };
            if r < 0 {
                return -1;
            }
            for ev in &evs[..r as usize] {
                let fd = ev.u64 as i64;
                let bits = ev.events;
                let err = (libc::EPOLLERR | libc::EPOLLHUP) as u32;
                if bits & (libc::EPOLLIN as u32 | libc::EPOLLRDHUP as u32 | err) != 0 {
                    keys[n] = fd * 2;
                    n += 1;
                }
                if bits & (libc::EPOLLOUT as u32 | err) != 0 {
                    keys[n] = fd * 2 + 1;
                    n += 1;
                }
            }
        }
        n as isize
    });
    if n < 0 {
        return if e == libc::EINTR { 0 } else { -e };
    }
    let n = (n as usize).min(max);
    for (i, k) in keys[..n].iter().enumerate() {
        // SAFETY: the library passes `max` words.
        unsafe { *word(out, i) = *k };
    }
    n as i32
}
