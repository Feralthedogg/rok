//! `librokr.a` — facade staticlib for the rok runtime.
//!
//! Bundles `rokr_common`, `rokr_gc`, `rokr_scheduler`, `rokr_coroutine`
//! into one static archive so cross-crate inlining (TLAB bump, safepoint
//! polls, write barriers) survives the codegen boundary.
//!
//! ABI symbols follow spec 008-abi/805; the convenience symbols at the
//! bottom are the 805 §8.5.12 appendix (no ABI stability).
//!
//! Not implemented yet (calls hit [`unimplemented`] → fatal, exit 101):
//! scheduler (007-runtime/706, 707), coroutines (708). OS threads (805
//! §8.5.4) are in `thread`. The GC (`rokr_gc`) is a non-moving Immix-style
//! mark-region (703) without generations or concurrent marking (704, 705).

#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(test), no_main)]

use core::ptr;

use core::sync::atomic::Ordering;

use rokr_common::object_header::{FLAG_PINNED, HEADER_ALIGN, ObjectHeader};
use rokr_common::{fatal, tls, write_stderr};

mod deque;
mod fmt;
mod fmt_spec;
mod math;
mod net;
mod os;
mod par;
mod stack;
mod str;
mod thread;
pub use str::RokStr;

/// Rust panic inside the runtime = inconsistent runtime state. Report
/// to stderr and abort. Rok exceptions are not Rust panics.
///
/// `cargo test` pulls in `std`, which already supplies a panic handler.
#[cfg(not(test))]
#[panic_handler]
fn panic(info: &core::panic::PanicInfo<'_>) -> ! {
    use core::fmt::Write as _;
    struct Stderr;
    impl core::fmt::Write for Stderr {
        fn write_str(&mut self, s: &str) -> core::fmt::Result {
            // SAFETY: `s` is valid for its own length.
            unsafe { write_stderr(s.as_ptr(), s.len()) };
            Ok(())
        }
    }
    let _ = writeln!(Stderr, "rok runtime internal error: {info}");
    // SAFETY: abort never returns and has no preconditions.
    unsafe { libc::abort() }
}

// The precompiled `core` / `compiler_builtins` reference
// `rust_eh_personality` even under `panic = "abort"`. Define it *weak* so
// linking librokr.a next to another Rust staticlib or std does not hit a
// duplicate-symbol error (a strong `#[no_mangle]` stub did).
//
// TODO(symbol hygiene): the archive still exports every non-generic
// `core` / `compiler_builtins` / mangled Rust symbol. Cargo cannot
// localize them; a post-build step would: macOS
// `ld -r -exported_symbols_list <rok_* list>`, ELF `ld -r --whole-archive`
// + `objcopy --keep-global-symbols`, then re-`ar` the single object.
#[cfg(all(not(test), target_vendor = "apple"))]
core::arch::global_asm!(
    ".globl _rust_eh_personality",
    ".weak_definition _rust_eh_personality",
    ".p2align 2",
    "_rust_eh_personality:",
    "ret",
);
#[cfg(all(not(test), not(target_vendor = "apple")))]
core::arch::global_asm!(
    ".weak rust_eh_personality",
    ".type rust_eh_personality, %function",
    "rust_eh_personality:",
    "ret",
);

/// Fatal "not implemented yet" for runtime entries whose subsystem does
/// not exist. Better than returning null and letting codegen continue.
fn unimplemented(what: &[u8]) -> ! {
    let prefix = b"rok runtime: unimplemented: ";
    // SAFETY: slice is valid for its own length.
    unsafe { write_stderr(prefix.as_ptr(), prefix.len()) };
    fatal(what)
}

// ---------------------------------------------------------------------
// 8.5.1 GC
// ---------------------------------------------------------------------

/// malloc-backed allocation for `rok_alloc` (manual, never collected).
/// Fatal on non-power-of-two `align`, size overflow, or OOM; never null.
fn raw_alloc(size: usize, align: usize) -> *mut u8 {
    if !align.is_power_of_two() {
        fatal(b"rok runtime: allocation align is not a power of two");
    }
    let Some(rounded) = size.checked_add(align - 1).map(|s| s & !(align - 1)) else {
        fatal(b"rok runtime: allocation size overflow");
    };
    let p = if align <= HEADER_ALIGN {
        // SAFETY: plain malloc; malloc alignment >= 8 on supported targets.
        unsafe { libc::malloc(rounded) }
    } else {
        let mut p: *mut libc::c_void = ptr::null_mut();
        // SAFETY: valid out-pointer; `align` is a power of two > 8, hence
        // a multiple of `size_of::<*mut c_void>()`.
        if unsafe { libc::posix_memalign(&mut p, align, rounded) } != 0 {
            p = ptr::null_mut();
        }
        p
    };
    if p.is_null() {
        rokr_common::oom();
    }
    p.cast()
}

/// GC allocation (702 §7.2.3, 805 §8.5.1).
///
/// `size` includes the 16-byte
/// header. Returns a pointer to the initialized header with a zeroed
/// payload; never null (OOM is fatal). May run a collection first, so
/// every live GC reference of the caller must be rooted.
#[unsafe(no_mangle)]
pub extern "C" fn rok_gc_alloc_slow(size: usize, align: usize, type_id: u32) -> *mut u8 {
    rokr_gc::alloc(size, align, type_id)
}

// Mark-sweep is neither generational nor incremental: nothing to log.
// Kept callable for codegen that already emits barriers (8.9.10).
#[unsafe(no_mangle)]
pub const extern "C" fn rok_gc_wb_slow(_obj: *mut u8) {}

/// # Safety
/// `scan_table` must be a valid 802 `ScanTable` that lives for the rest
/// of the process.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_gc_register_type(type_id: u32, scan_table: *const u8) {
    rokr_gc::register_type(type_id, scan_table);
}

/// Non-moving collector: pinning only keeps the object (and what it
/// references) alive until `rok_gc_unpin`.
///
/// # Safety
/// `obj` must be a live GC object.
#[unsafe(no_mangle)]
#[allow(clippy::cast_ptr_alignment)] // GC objects are 8-aligned
pub unsafe extern "C" fn rok_gc_pin(obj: *mut u8) -> *mut u8 {
    // SAFETY: caller contract.
    unsafe {
        (*obj.cast::<ObjectHeader>())
            .gc_flags
            .fetch_or(FLAG_PINNED, Ordering::Relaxed)
    };
    obj
}

/// # Safety
/// `obj` must be a live GC object.
#[unsafe(no_mangle)]
#[allow(clippy::cast_ptr_alignment)] // GC objects are 8-aligned
pub unsafe extern "C" fn rok_gc_unpin(obj: *mut u8) {
    // SAFETY: caller contract.
    unsafe {
        (*obj.cast::<ObjectHeader>())
            .gc_flags
            .fetch_and(!FLAG_PINNED, Ordering::Relaxed)
    };
}

/// Register `word` (a static's reference word) as a GC root for the
/// rest of the process. Compiled code calls it at startup.
#[unsafe(no_mangle)]
pub extern "C" fn rok_gc_add_root(word: *const usize) {
    rokr_gc::world::add_root(word);
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_gc_collect() {
    rokr_gc::collect();
}

/// Bytes held by not-yet-swept GC objects, headers included (tests,
/// diagnostics; no ABI stability).
#[unsafe(no_mangle)]
pub extern "C" fn rok_gc_stats_live_bytes() -> usize {
    rokr_gc::live_bytes()
}

/// Number of completed collections (tests, diagnostics).
#[unsafe(no_mangle)]
pub extern "C" fn rok_gc_stats_collections() -> u64 {
    rokr_gc::collections()
}

// ---------------------------------------------------------------------
// 8.5.2 Runtime
// ---------------------------------------------------------------------

#[unsafe(no_mangle)]
pub extern "C" fn rok_runtime_init() {
    init_thread(true);
}

/// The main thread is done with rok code: from here it counts as
/// stopped, so threads still running can collect without it.
#[unsafe(no_mangle)]
pub extern "C" fn rok_runtime_shutdown() {
    rokr_gc::world::enter_native();
}

/// Safepoint slow path (804 §8.4.3): park while another thread stops
/// the world.
#[unsafe(no_mangle)]
pub extern "C" fn rok_runtime_yield() {
    rokr_gc::world::safepoint();
}

/// Initialize this thread's TLS slots (803 §8.3.6) and register it as a
/// mutator (its shadow stack becomes a GC root set).
#[unsafe(no_mangle)]
pub extern "C" fn rok_thread_init() {
    init_thread(false);
}

fn init_thread(main: bool) {
    tls::thread_init();
    rokr_gc::world::attach_current();
    stack::thread_start(main);
}

/// Unregister this thread; it must not touch GC objects afterwards.
#[unsafe(no_mangle)]
pub extern "C" fn rok_thread_shutdown() {
    rokr_gc::world::detach();
    stack::thread_exit();
}

// ---------------------------------------------------------------------
// 8.5.3 Coroutine
// ---------------------------------------------------------------------

/// "Almost identical to `rok_gc_alloc_slow`" (805 §8.5.3).
#[unsafe(no_mangle)]
pub extern "C" fn rok_coro_frame_alloc(size: usize, type_id: u32) -> *mut u8 {
    rok_gc_alloc_slow(size, HEADER_ALIGN, type_id)
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_coro_park(_frame: *mut u8, _waker: *mut u8) {
    unimplemented(b"rok_coro_park (coroutines, spec 007-runtime/708)")
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_coro_unpark(_frame: *mut u8) {
    unimplemented(b"rok_coro_unpark (coroutines, spec 007-runtime/708)")
}

// ---------------------------------------------------------------------
// 8.5.4 Scheduler
// ---------------------------------------------------------------------

/// This thread's running executor (`rok::core::task`): a GC object,
/// pinned while installed so the collector keeps it (and every task)
/// alive.
#[unsafe(no_mangle)]
pub extern "C" fn rok_task_exec_active() -> i32 {
    i32::from(rok_task_exec_get() != 0)
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_task_exec_get() -> usize {
    // SAFETY: this thread's own slot.
    unsafe { tls::task_exec().read() }
}

/// # Safety
/// `exec` must be a live GC object.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_task_exec_set(exec: usize) {
    rok_task_exec_clear();
    // SAFETY: caller contract; this thread's own slot.
    unsafe {
        rok_gc_pin(exec as *mut u8);
        tls::task_exec().write(exec);
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_task_exec_clear() {
    let old = rok_task_exec_get();
    if old != 0 {
        // SAFETY: the slot only holds a pinned, hence live, object.
        unsafe {
            rok_gc_unpin(old as *mut u8);
            tls::task_exec().write(0);
        }
    }
}

/// The process-wide registry of tasks parked on a key (async waits on a
/// `Mutex` / channel, `rok::core::task::park` / `unpark`): installed
/// once, pinned for good.
static TASK_PARKING: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);

#[unsafe(no_mangle)]
pub extern "C" fn rok_task_parking_ready() -> i32 {
    i32::from(TASK_PARKING.load(Ordering::Acquire) != 0)
}

/// Install `obj` unless a registry exists; the registry in use.
///
/// # Safety
/// `obj` must be a live GC object.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_task_parking_install(obj: usize) -> usize {
    match TASK_PARKING.compare_exchange(0, obj, Ordering::AcqRel, Ordering::Acquire) {
        Ok(_) => {
            // SAFETY: caller contract (the caller's frame still roots it).
            unsafe { rok_gc_pin(obj as *mut u8) };
            obj
        }
        Err(cur) => cur,
    }
}

/// A GC object's address as a parking key (`GcBuf<i32>` argument).
#[unsafe(no_mangle)]
pub const extern "C" fn rok_task_key_i32(obj: usize) -> usize {
    obj
}

/// A GC object's address as a parking key (`GcBuf<usize>` argument).
#[unsafe(no_mangle)]
pub const extern "C" fn rok_task_key_usize(obj: usize) -> usize {
    obj
}

/// Monotonic clock in nanoseconds (707 timers).
#[unsafe(no_mangle)]
#[allow(clippy::unnecessary_cast)] // `time_t` / `c_long` widths vary by target
pub extern "C" fn rok_time_now_ns() -> i64 {
    let mut ts = libc::timespec {
        tv_sec: 0,
        tv_nsec: 0,
    };
    // SAFETY: valid out-pointer.
    unsafe { libc::clock_gettime(libc::CLOCK_MONOTONIC, &mut ts) };
    ts.tv_sec as i64 * 1_000_000_000 + ts.tv_nsec as i64
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_task_spawn(_coro_frame: *mut u8) -> *mut u8 {
    unimplemented(b"rok_task_spawn (scheduler, spec 007-runtime/706)")
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_task_await(_handle: *mut u8) -> *mut u8 {
    unimplemented(b"rok_task_await (scheduler, spec 007-runtime/706)")
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_task_cancel(_handle: *mut u8) {
    unimplemented(b"rok_task_cancel (scheduler, spec 007-runtime/706)")
}

// ---------------------------------------------------------------------
// 8.5.5 I/O / timer
// ---------------------------------------------------------------------

#[unsafe(no_mangle)]
pub extern "C" fn rok_io_register(_fd: i32, _interest: u32, _waker: *mut u8) {
    unimplemented(b"rok_io_register (I/O driver, spec 007-runtime/707)")
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_timer_register(_deadline_ns: u64, _waker: *mut u8) {
    unimplemented(b"rok_timer_register (timing wheel, spec 007-runtime/707)")
}

// ---------------------------------------------------------------------
// 8.5.6 Errors
// ---------------------------------------------------------------------
// `throw` / `try` / `catch` are value-based (a throwing function returns
// an `is_err` flag with its payload) and need no runtime support. Only
// an error escaping a throwing `main` reaches the runtime.

/// Uncaught error out of `fn main() throws (..)` (spec 4.16.4): a fixed
/// prefix, the error's description, `\n` to stderr, then exit status 1.
#[unsafe(no_mangle)]
pub extern "C" fn rok_uncaught_error(what: RokStr) -> ! {
    const PREFIX: &[u8] = b"error: `main` returned an uncaught error: ";
    // SAFETY: `what` is a valid `str`; `exit` flushes buffered stdout.
    unsafe {
        write_stderr(PREFIX.as_ptr(), PREFIX.len());
        write_stderr(what.ptr, what.len);
        write_stderr(b"\n".as_ptr(), 1);
        libc::exit(1)
    }
}

// ---------------------------------------------------------------------
// 8.5.7 Diagnostics
// ---------------------------------------------------------------------

/// Unrecoverable panic: `msg` + `\n` to stderr, then exit 101.
///
/// # Safety
/// `msg` must be null or valid for reads of `msg_len` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_panic(msg: *const u8, msg_len: usize) -> ! {
    if msg.is_null() {
        fatal(b"panic");
    }
    // SAFETY: caller contract.
    unsafe { write_stderr(msg, msg_len) };
    fatal(b"")
}

/// `rok::core::panic::oom()` (stdlib 2.14.5 `oom_fn`): out of memory,
/// exit 101. Runtime allocation failures take the same path.
#[unsafe(no_mangle)]
pub extern "C" fn rok_oom() -> ! {
    rokr_common::oom()
}

/// `rok::core::panic::panic(msg)` (stdlib 2.14.5): `rok_panic` for a
/// rok `str` value.
#[unsafe(no_mangle)]
pub extern "C" fn rok_panic_str(msg: RokStr) -> ! {
    // SAFETY: a rok `str` is valid for `len` bytes.
    unsafe { rok_panic(msg.ptr, msg.len) }
}

// ---------------------------------------------------------------------
// 8.5.12 appendix: convenience symbols (no ABI stability)
// ---------------------------------------------------------------------

/// `rok_assert(cond)`: fatal (exit 101) if `cond` is zero, else 0.
#[unsafe(no_mangle)]
pub extern "C" fn rok_assert(cond: i32) -> i32 {
    if cond == 0 {
        fatal(b"assertion failed");
    }
    0
}

/// `rok::std::env::exit(code)` (spec 4.16.4): exit now with `code`.
/// `finally` and `Drop` do not run; `exit` flushes buffered stdout.
#[unsafe(no_mangle)]
pub extern "C" fn rok_exit(code: i32) -> ! {
    // SAFETY: plain libc call.
    unsafe { libc::exit(code) }
}

/// User-facing allocator: no header, `size == 0` → null, otherwise
/// fatal on bad `align` / OOM.
#[unsafe(no_mangle)]
pub extern "C" fn rok_alloc(size: usize, align: usize) -> *mut u8 {
    if size == 0 {
        return ptr::null_mut();
    }
    raw_alloc(size, align)
}

/// `rok::bare::alloc::alloc` (stdlib 1.4): like `rok_alloc`, but null on
/// failure (`size == 0`, bad `align`, overflow, OOM) instead of
/// aborting. `zeroed != 0` zero-fills. Freed with `rok_free`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_alloc_raw(size: usize, align: usize, zeroed: i32) -> *mut u8 {
    if size == 0 || !align.is_power_of_two() {
        return ptr::null_mut();
    }
    let Some(rounded) = size.checked_add(align - 1).map(|s| s & !(align - 1)) else {
        return ptr::null_mut();
    };
    let p: *mut libc::c_void = if align <= HEADER_ALIGN {
        // SAFETY: plain malloc; malloc alignment >= 8 on supported targets.
        unsafe { libc::malloc(rounded) }
    } else {
        let mut p: *mut libc::c_void = ptr::null_mut();
        // SAFETY: valid out-pointer; `align` is a power of two > 8.
        if unsafe { libc::posix_memalign(&mut p, align, rounded) } != 0 {
            p = ptr::null_mut();
        }
        p
    };
    if !p.is_null() && zeroed != 0 {
        // SAFETY: `p` is valid for `rounded` bytes.
        unsafe { ptr::write_bytes(p.cast::<u8>(), 0, rounded) };
    }
    p.cast()
}

/// `rok::bare::alloc::realloc`: a block of `new_size` bytes holding the
/// first `min(old_size, new_size)` bytes of `ptr`; null on failure (then
/// `ptr` stays valid). `ptr` is freed on success.
///
/// # Safety
/// `ptr` must be a live block from `rok_alloc_raw` with `old_size` and
/// `align`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_realloc_raw(
    ptr: *mut u8,
    old_size: usize,
    align: usize,
    new_size: usize,
) -> *mut u8 {
    let q = rok_alloc_raw(new_size, align, 0);
    if !q.is_null() {
        // SAFETY: both blocks are valid for the copied length; caller
        // contract on `ptr`.
        unsafe {
            ptr::copy_nonoverlapping(ptr, q, old_size.min(new_size));
            libc::free(ptr.cast());
        }
    }
    q
}

/// # Safety
/// `ptr` must be null or a live pointer returned by `rok_alloc`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_free(ptr: *mut u8) {
    // SAFETY: caller contract; free(NULL) is a no-op.
    unsafe { libc::free(ptr.cast()) };
}

// Typed load/store. Pointers cross the FFI boundary as `usize`.

/// # Safety
/// `ptr` must be valid and aligned for an `i32` read.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_load_i32(ptr: *const i32) -> i32 {
    // SAFETY: caller contract.
    unsafe { *ptr }
}

/// # Safety
/// `ptr` must be valid and aligned for an `i32` write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_store_i32(ptr: *mut i32, val: i32) {
    // SAFETY: caller contract.
    unsafe { *ptr = val }
}

/// # Safety
/// `ptr` must be valid and aligned for an `i64` read.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_load_i64(ptr: *const i64) -> i64 {
    // SAFETY: caller contract.
    unsafe { *ptr }
}

/// # Safety
/// `ptr` must be valid and aligned for an `i64` write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_store_i64(ptr: *mut i64, val: i64) {
    // SAFETY: caller contract.
    unsafe { *ptr = val }
}

/// # Safety
/// `ptr` must be valid and aligned for an `f64` read.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_load_f64(ptr: *const f64) -> f64 {
    // SAFETY: caller contract.
    unsafe { *ptr }
}

/// # Safety
/// `ptr` must be valid and aligned for an `f64` write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_store_f64(ptr: *mut f64, val: f64) {
    // SAFETY: caller contract.
    unsafe { *ptr = val }
}

// Printers over libc `printf` (stdout). Each returns 0 so it composes
// as an i32-returning expression.

#[unsafe(no_mangle)]
pub extern "C" fn rok_print_i64(n: i64) -> i32 {
    // SAFETY: format matches the argument.
    unsafe { libc::printf(c"%lld\n".as_ptr(), n) };
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_print_i32(n: i32) -> i32 {
    // SAFETY: format matches the argument.
    unsafe { libc::printf(c"%d\n".as_ptr(), n) };
    0
}

/// C string + `\n`. Null prints as an empty line.
///
/// `s` + `\n` to stdout (`println`), under the stream lock so lines
/// printed from different threads never interleave.
#[unsafe(no_mangle)]
pub extern "C" fn rok_print_str(s: RokStr) -> i32 {
    unsafe extern "C" {
        fn flockfile(f: *mut libc::FILE);
        fn funlockfile(f: *mut libc::FILE);
    }
    let out = stdout();
    // SAFETY: `out` is libc's stdout; lock / unlock pair up.
    unsafe {
        flockfile(out);
        rok_write_str(s);
        libc::fputc(i32::from(b'\n'), out);
        funlockfile(out);
    }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_print_f64(d: f64) -> i32 {
    // SAFETY: format matches the argument.
    unsafe { libc::printf(c"%g\n".as_ptr(), d) };
    0
}

/// Bool passed as i32 (no stable C ABI for i1). No trailing newline.
#[unsafe(no_mangle)]
pub extern "C" fn rok_print_bool(b: i32) -> i32 {
    let s = if b != 0 { c"true" } else { c"false" };
    // SAFETY: format matches the argument.
    unsafe { libc::printf(c"%s".as_ptr(), s.as_ptr()) };
    0
}

// `rok_write_*`: same as `rok_print_*` without the trailing newline.

/// `s` to stdout (through stdio, so it orders with `printf` output).
#[unsafe(no_mangle)]
pub extern "C" fn rok_write_str(s: RokStr) -> i32 {
    if s.len > 0 {
        // SAFETY: `s` is valid for `len` bytes; `stdout` is libc's stream.
        unsafe { libc::fwrite(s.ptr.cast(), 1, s.len, stdout()) };
    }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_write_i64(n: i64) -> i32 {
    // SAFETY: format matches the argument.
    unsafe { libc::printf(c"%lld".as_ptr(), n) };
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_write_f64(d: f64) -> i32 {
    // SAFETY: format matches the argument.
    unsafe { libc::printf(c"%g".as_ptr(), d) };
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_write_hex(n: i64) -> i32 {
    // SAFETY: format matches the argument.
    unsafe { libc::printf(c"0x%llx".as_ptr(), n) };
    0
}

/// Byte length of `s` (stdlib 2.15 `str::len`).
#[unsafe(no_mangle)]
pub const extern "C" fn rok_str_len(s: RokStr) -> usize {
    s.len
}

/// 1 if `a` and `b` hold the same bytes, else 0.
#[unsafe(no_mangle)]
pub extern "C" fn rok_str_eq(a: RokStr, b: RokStr) -> i32 {
    i32::from(str::rok_str_cmp(a, b) == 0)
}

/// `s` to stderr (unbuffered).
/// `s` + `\n` to stderr (`eprintln`) in one `writev`, so lines from
/// different threads never interleave.
#[unsafe(no_mangle)]
pub extern "C" fn rok_eprint_str(s: RokStr) -> i32 {
    let iov = [
        libc::iovec {
            iov_base: s.ptr.cast_mut().cast(),
            iov_len: s.len,
        },
        libc::iovec {
            iov_base: c"\n".as_ptr().cast_mut().cast(),
            iov_len: 1,
        },
    ];
    // SAFETY: both buffers are valid for their lengths.
    let n = usize::try_from(unsafe { libc::writev(2, iov.as_ptr(), 2) }).unwrap_or(0);
    // A short write (big line, full pipe): finish it piecewise.
    if n < s.len {
        // SAFETY: `n < len`, inside `s`.
        unsafe { write_stderr(s.ptr.add(n), s.len - n) };
    }
    if n <= s.len {
        // SAFETY: a one-byte static buffer.
        unsafe { write_stderr(c"\n".as_ptr().cast(), 1) };
    }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_ewrite_str(s: RokStr) -> i32 {
    // SAFETY: `s` is valid for `len` bytes.
    unsafe { write_stderr(s.ptr, s.len) };
    0
}

/// libc's `stdout` stream.
fn stdout() -> *mut libc::FILE {
    unsafe extern "C" {
        #[cfg_attr(target_vendor = "apple", link_name = "__stdoutp")]
        static mut stdout: *mut libc::FILE;
    }
    // SAFETY: libc initializes `stdout` before `main`.
    unsafe { stdout }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[allow(clippy::cast_ptr_alignment)] // asserted 64-aligned below
    fn gc_alloc_initializes_header_and_alignment() {
        let p = rok_gc_alloc_slow(24, 64, 12345);
        assert_eq!(p as usize % 64, 0);
        // SAFETY: fresh 24-byte allocation with an initialized header.
        let h = unsafe { &*p.cast::<ObjectHeader>() };
        assert_eq!(h.type_id, 12345);
        // Over-aligned: a LOS object; `gc_word` is the size (801 §8.1.4).
        assert_eq!(
            h.gc_flags.load(Ordering::Relaxed),
            rokr_common::object_header::FLAG_LARGE
        );
        assert_eq!(h.gc_word, 24);
        // Block objects keep their 8-rounded size in `gc_word` too.
        // SAFETY: as above.
        let h = unsafe { &*rok_gc_alloc_slow(20, 8, 7).cast::<ObjectHeader>() };
        assert_eq!((h.type_id, h.gc_word), (7, 24));
        str::tests::string_ops();
        fmt::tests::fmt_ops();
    }
}
