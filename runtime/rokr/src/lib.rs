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
//! scheduler (007-runtime/706, 707), coroutines (708), threads (805
//! §8.5.4). Immix GC (703–705) is replaced by a malloc-backed mark-sweep
//! (`rokr_gc`).

#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(test), no_main)]

use core::ptr;

use core::sync::atomic::Ordering;

use rokr_common::object_header::{FLAG_PINNED, HEADER_ALIGN, ObjectHeader};
use rokr_common::{fatal, tls, write_stderr};

mod str;
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
        fatal(b"rok runtime: out of memory");
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
    rok_thread_init();
}

#[unsafe(no_mangle)]
pub const extern "C" fn rok_runtime_shutdown() {}

/// Safepoint slow path (804). No GC to cooperate with: just clear the
/// request.
#[unsafe(no_mangle)]
pub extern "C" fn rok_runtime_yield() {
    tls::clear_yield();
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_thread_init() {
    tls::thread_init();
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_thread_shutdown() {
    tls::thread_shutdown();
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

#[unsafe(no_mangle)]
pub extern "C" fn rok_thread_spawn(_closure: *mut u8) -> *mut u8 {
    unimplemented(b"rok_thread_spawn (spec 007-runtime/706 7.6.6)")
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_thread_join(_handle: *mut u8) -> *mut u8 {
    unimplemented(b"rok_thread_join (spec 007-runtime/706 7.6.6)")
}

/// `par::for_each` desugar. `callback` is `Ptr<u8>` in 805, i.e.
/// nullable. ponytail: runs sequentially on the caller thread; the
/// work-stealing pool (706) will split the range.
#[unsafe(no_mangle)]
pub extern "C" fn rok_par_for(
    start: i64,
    end: i64,
    step: i64,
    callback: Option<unsafe extern "C" fn(i64)>,
) {
    let Some(cb) = callback else {
        fatal(b"rok_par_for: null callback");
    };
    if step == 0 {
        fatal(b"rok_par_for: step is zero");
    }
    let mut i = start;
    while (step > 0 && i < end) || (step < 0 && i > end) {
        // SAFETY: the compiler passes a valid `extern "C" fn(i64)`.
        unsafe { cb(i) };
        let Some(next) = i.checked_add(step) else {
            break;
        };
        i = next;
    }
}

/// `par::scope` desugar. ponytail: runs the body inline (no spawned
/// work can exist yet). The scope handle argument is null until the
/// scheduler defines one.
#[unsafe(no_mangle)]
pub extern "C" fn rok_par_scope(callback: Option<unsafe extern "C" fn(*mut u8)>) {
    let Some(cb) = callback else {
        fatal(b"rok_par_scope: null callback");
    };
    // SAFETY: the compiler passes a valid `extern "C" fn(*mut u8)`.
    unsafe { cb(ptr::null_mut()) };
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
/// `s` + `\n` to stdout.
#[unsafe(no_mangle)]
pub extern "C" fn rok_print_str(s: RokStr) -> i32 {
    rok_write_str(s);
    // SAFETY: format matches (no arguments).
    unsafe { libc::printf(c"\n".as_ptr()) };
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
    use core::sync::atomic::AtomicI64;

    #[test]
    #[allow(clippy::cast_ptr_alignment)] // asserted 64-aligned below
    fn gc_alloc_initializes_header_and_alignment() {
        let p = rok_gc_alloc_slow(24, 64, 12345);
        assert_eq!(p as usize % 64, 0);
        // SAFETY: fresh 24-byte allocation with an initialized header.
        let h = unsafe { &*p.cast::<ObjectHeader>() };
        assert_eq!(h.type_id, 12345);
        assert_eq!(h.gc_flags.load(Ordering::Relaxed), 0);
        assert_eq!(h.gc_word, 0);
        str::tests::string_ops();
    }

    static SUM: AtomicI64 = AtomicI64::new(0);
    extern "C" fn add(i: i64) {
        SUM.fetch_add(i, Ordering::Relaxed);
    }

    #[test]
    fn par_for_runs_every_iteration() {
        rok_par_for(0, 10, 3, Some(add)); // 0+3+6+9
        rok_par_for(10, 0, -4, Some(add)); // 10+6+2
        assert_eq!(SUM.load(Ordering::Relaxed), 36);
    }
}
