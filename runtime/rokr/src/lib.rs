//! `librokr.a`: the rok runtime as one static archive, so cross-crate
//! inlining (TLAB bump, safepoint polls, write barriers) survives the
//! codegen boundary.
//!
//! ABI symbols follow spec 008-abi/805; the convenience symbols at the
//! bottom are the 805 §8.5.12 appendix (no ABI stability). The task
//! executor itself is rok code (`rok::core::task`) on top of OS threads
//! (`thread`). The GC (`rokr_gc`) is an Immix-style mark-region (703)
//! with opportunistic evacuation and sticky mark-bit generations (704),
//! without concurrent marking (705). Objects a root reaches never move,
//! so a GC pointer a runtime function got as an argument stays valid
//! across its allocations and blocking calls.

#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(test), no_main)]

use core::ptr;

use core::sync::atomic::Ordering;

use rokr_common::object_header::HEADER_ALIGN;
use rokr_common::{fatal, tls};

mod bignum;
mod deque;
mod fmt;
mod fmt_spec;
#[cfg(test)]
mod fuzz_tests;
mod lane;
mod math;
#[cfg_attr(windows, path = "net_windows.rs")]
mod net;
#[cfg_attr(windows, path = "os_windows.rs")]
mod os;
#[cfg(not(target_family = "wasm"))]
mod session;

/// No REPL session on wasm32: no thread is ever found gone.
#[cfg(target_family = "wasm")]
#[unsafe(no_mangle)]
pub const extern "C" fn rok_thread_lost(_id: u64) -> i32 {
    0
}

/// No REPL session on wasm32: no gates, no lock notes.
#[cfg(target_family = "wasm")]
#[unsafe(no_mangle)]
pub const extern "C" fn rok_session_enter() {}

#[cfg(target_family = "wasm")]
#[unsafe(no_mangle)]
pub const extern "C" fn rok_session_leave() {}

#[cfg(target_family = "wasm")]
#[unsafe(no_mangle)]
pub const extern "C" fn rok_session_pass() {}

#[cfg(target_family = "wasm")]
#[unsafe(no_mangle)]
pub const extern "C" fn rok_lock_note(_buf: *mut u8, _kind: i32) -> i32 {
    0
}

#[cfg(target_family = "wasm")]
#[unsafe(no_mangle)]
pub const extern "C" fn rok_lock_drop(_buf: *mut u8) {}

#[cfg(target_family = "wasm")]
#[unsafe(no_mangle)]
pub const extern "C" fn rok_lock_notes() -> i32 {
    0
}
#[cfg_attr(windows, path = "stack_windows.rs")]
#[cfg_attr(target_family = "wasm", path = "stack_wasm.rs")]
mod stack;
mod stdio;
mod str;
mod thread;
mod unicode;
mod unicode_tables;
#[cfg(any(windows, test))]
mod winargs;
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
            unsafe { rokr_common::write_stderr(s.as_ptr(), s.len()) };
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
// Cargo's archive also exports every non-generic `core` /
// `compiler_builtins` / mangled Rust symbol; `localize.sh` (run by
// dist.sh) keeps only `rok_*` global in the shipped one.
#[cfg(all(not(test), target_vendor = "apple"))]
core::arch::global_asm!(
    ".globl _rust_eh_personality",
    ".weak_definition _rust_eh_personality",
    ".p2align 2",
    "_rust_eh_personality:",
    "ret",
);
// MSVC targets use `__CxxFrameHandler3`, not this symbol.
#[cfg(all(
    not(test),
    not(target_vendor = "apple"),
    not(windows),
    not(target_arch = "arm"),
    not(target_family = "wasm")
))]
core::arch::global_asm!(
    ".weak rust_eh_personality",
    ".type rust_eh_personality, %function",
    "rust_eh_personality:",
    "ret",
);
// ARM EHABI unwind tables also name the personality routines libgcc
// would bring; nothing here unwinds.
#[cfg(all(not(test), target_arch = "arm"))]
core::arch::global_asm!(
    ".weak rust_eh_personality",
    ".type rust_eh_personality, %function",
    "rust_eh_personality:",
    ".weak __aeabi_unwind_cpp_pr0",
    ".type __aeabi_unwind_cpp_pr0, %function",
    "__aeabi_unwind_cpp_pr0:",
    ".weak __aeabi_unwind_cpp_pr1",
    ".type __aeabi_unwind_cpp_pr1, %function",
    "__aeabi_unwind_cpp_pr1:",
    ".weak __aeabi_unwind_cpp_pr2",
    ".type __aeabi_unwind_cpp_pr2, %function",
    "__aeabi_unwind_cpp_pr2:",
    "bx lr",
);

// ---------------------------------------------------------------------
// 8.5.1 GC
// ---------------------------------------------------------------------

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

/// Write barrier slow path (704 §7.4.2, 809 §8.9.10): compiled code
/// calls it before storing a GC reference into the old object `obj`
/// (its `UNLOGGED` header bit set); `obj` joins the remembered set.
///
/// During a concurrent mark it also logs the references `obj` holds
/// (snapshot at the beginning).
///
/// # Safety
/// `obj` must be a live GC object.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_gc_wb_slow(obj: *mut u8) {
    // SAFETY: caller contract.
    unsafe { rokr_gc::write_barrier_slow(obj) };
}

/// # Safety
/// `scan_table` must be a valid 802 `ScanTable` that lives for the rest
/// of the process.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_gc_register_type(type_id: u32, scan_table: *const u8) {
    rokr_gc::register_type(type_id, scan_table);
}

/// Keep `obj` (and what it references) alive and in place until
/// `rok_gc_unpin`.
///
/// # Safety
/// `obj` must be a live GC object.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_gc_pin(obj: *mut u8) -> *mut u8 {
    // SAFETY: caller contract.
    unsafe { rokr_gc::pin(obj) };
    obj
}

/// # Safety
/// `obj` must be a live GC object.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_gc_unpin(obj: *mut u8) {
    // SAFETY: caller contract.
    unsafe { rokr_gc::unpin(obj) };
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

/// A minor collection (tests, diagnostics).
#[unsafe(no_mangle)]
pub extern "C" fn rok_gc_collect_young() {
    rokr_gc::collect_young();
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

/// Bytes evacuation has copied so far (tests, diagnostics).
#[unsafe(no_mangle)]
pub extern "C" fn rok_gc_stats_moved_bytes() -> u64 {
    rokr_gc::moved_bytes()
}

// ---------------------------------------------------------------------
// 8.5.2 Runtime
// ---------------------------------------------------------------------

#[unsafe(no_mangle)]
pub extern "C" fn rok_runtime_init() {
    init_thread(true);
}

/// The main thread is done with rok code: every other rok thread (the
/// executor's worker pool, threads still running) stops for good before
/// the process exits.
#[cfg(not(all(rok_solo, target_env = "p1")))]
#[unsafe(no_mangle)]
pub extern "C" fn rok_runtime_shutdown() {
    rokr_gc::world::halt();
}

/// The browser's module (a reactor, one thread) stays up after `main`
/// for its exports.
#[cfg(all(rok_solo, target_env = "p1"))]
#[unsafe(no_mangle)]
pub const extern "C" fn rok_runtime_shutdown() {}

/// Into an `extern "C"` call: the thread counts as `PARKED`.
///
/// 804 §8.4.10: a C call that blocks does not hold up a collection; the
/// caller's GC references are in its shadow-stack frame. Compiled code
/// inlines the fast path (store the state, read the yield flag) and
/// calls this, or [`rok_leave_native`], only when the flag is up.
#[unsafe(no_mangle)]
pub extern "C" fn rok_enter_native() {
    rokr_gc::world::enter_native();
}

/// Back from C: waits out a running collection.
#[unsafe(no_mangle)]
pub extern "C" fn rok_leave_native() {
    rokr_gc::world::leave_native();
}

/// The C entry of a rok `extern "C" fn`: a call from C code that this
/// thread entered from rok (`PARKED`) runs rok code again until
/// [`rok_native_resume`]. Returns whether it was parked.
#[unsafe(no_mangle)]
pub extern "C" fn rok_native_reenter() -> u32 {
    let parked = rokr_common::tls::mutator_state().load(core::sync::atomic::Ordering::Relaxed)
        == rokr_common::tls::MUTATOR_PARKED;
    if parked {
        rokr_gc::world::leave_native();
    }
    u32::from(parked)
}

/// End of [`rok_native_reenter`]'s bracket: back to C.
#[unsafe(no_mangle)]
pub extern "C" fn rok_native_resume(parked: u32) {
    if parked != 0 {
        rokr_gc::world::enter_native();
    }
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
    thread::thread_exit();
}

// ---------------------------------------------------------------------
// 8.5.3 Coroutine
// ---------------------------------------------------------------------

/// "Almost identical to `rok_gc_alloc_slow`" (805 §8.5.3).
#[unsafe(no_mangle)]
pub extern "C" fn rok_coro_frame_alloc(size: usize, type_id: u32) -> *mut u8 {
    rok_gc_alloc_slow(size, HEADER_ALIGN, type_id)
}

/// Park `waker` on coroutine `frame` (a GC object; its address is the
/// parking key) until `rok_coro_unpark(frame)`.
///
/// # Safety
/// `frame` and `waker` must be live GC objects.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_coro_park(frame: *mut u8, waker: *mut u8) {
    // SAFETY: an installed hook; caller contract.
    unsafe { (hooks().park)(frame, waker) };
}

/// Wake every waker parked on `frame`.
///
/// # Safety
/// `frame` must be a live GC object.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_coro_unpark(frame: *mut u8) {
    // SAFETY: as above.
    unsafe { (hooks().unpark)(frame) };
}

// ---------------------------------------------------------------------
// 8.5.4 Scheduler
// ---------------------------------------------------------------------

/// A GC object's address as a parking key: from now on the collector
/// never moves it, so the key stays its own. Only for keys that outlive
/// the call (identity tests use `buf_same`, which pins nothing).
///
/// # Safety
/// `obj` must be a live GC object.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_task_key(obj: *mut u8) -> usize {
    // SAFETY: caller contract.
    unsafe { rokr_gc::no_move(obj) };
    obj as usize
}

/// Monotonic clock in nanoseconds, stopped during suspend (`Instant`,
/// 707 timers; 3.3.7: `CLOCK_UPTIME_RAW` on macOS, whose
/// `CLOCK_MONOTONIC` counts sleep; `QueryPerformanceCounter` on Windows).
#[unsafe(no_mangle)]
pub extern "C" fn rok_time_now_ns() -> i64 {
    rokr_common::sys::monotonic_ns()
}

/// Wall clock, nanoseconds since the Unix epoch (`SystemTime`, 3.3.3).
#[unsafe(no_mangle)]
pub extern "C" fn rok_time_realtime_ns() -> i64 {
    rokr_common::sys::realtime_ns()
}

/// Time since boot, counting suspend (`BootTime`, 3.3.4).
///
/// `CLOCK_BOOTTIME` on Linux, `CLOCK_MONOTONIC` (which counts sleep) on
/// macOS, the `Instant` clock on Windows (3.3.7).
#[unsafe(no_mangle)]
pub extern "C" fn rok_time_boot_ns() -> i64 {
    rokr_common::sys::boot_ns()
}

// ---------------------------------------------------------------------
// 8.5.5 I/O / timer
// ---------------------------------------------------------------------

// `rok_io_register` / `rok_timer_register` and 8.5.3's `rok_coro_park` /
// `rok_coro_unpark` act on `rok::core::task`'s parking table and timers,
// so they call into it through hooks the executor installs when it
// starts. Defining them in rok (`#[export_name]`) would compile the
// executor into every program. A `waker` is a one-element `GcBuf<Waker>`.

/// The executor's hooks (C function pointers to rok `extern "C" fn`s).
#[derive(Clone, Copy)]
struct Hooks {
    io: unsafe extern "C" fn(i32, u32, *mut u8),
    timer: unsafe extern "C" fn(u64, *mut u8),
    park: unsafe extern "C" fn(*mut u8, *mut u8),
    unpark: unsafe extern "C" fn(*mut u8),
    /// After a failed REPL cell (`session`): start again what ran on
    /// threads that are gone.
    #[cfg_attr(target_family = "wasm", allow(dead_code))]
    restart: unsafe extern "C" fn(),
}

static HOOKS: core::sync::atomic::AtomicPtr<Hooks> =
    core::sync::atomic::AtomicPtr::new(ptr::null_mut());

/// Install `rok::core::task`'s hooks (the first call wins).
#[unsafe(no_mangle)]
pub extern "C" fn rok_task_hooks_install(
    io: unsafe extern "C" fn(i32, u32, *mut u8),
    timer: unsafe extern "C" fn(u64, *mut u8),
    park: unsafe extern "C" fn(*mut u8, *mut u8),
    unpark: unsafe extern "C" fn(*mut u8),
    restart: unsafe extern "C" fn(),
) {
    // SAFETY: plain allocation, never freed: the hooks live as long as
    // the process.
    let h = unsafe { libc::malloc(core::mem::size_of::<Hooks>()) }.cast::<Hooks>();
    if h.is_null() {
        rokr_common::oom();
    }
    // SAFETY: fresh allocation.
    unsafe {
        h.write(Hooks {
            io,
            timer,
            park,
            unpark,
            restart,
        });
    }
    if HOOKS
        .compare_exchange(ptr::null_mut(), h, Ordering::AcqRel, Ordering::Acquire)
        .is_err()
    {
        // SAFETY: ours, never published.
        unsafe { libc::free(h.cast()) };
    }
}

/// The executor's restart hook, if it started (`session`).
#[cfg(not(target_family = "wasm"))]
fn restart_executor() {
    let h = HOOKS.load(Ordering::Acquire);
    if !h.is_null() {
        // SAFETY: published once, never freed; a rok `extern "C" fn`.
        unsafe { ((*h).restart)() };
    }
}

fn hooks() -> Hooks {
    let h = HOOKS.load(Ordering::Acquire);
    if h.is_null() {
        fatal(b"rok runtime: rok_io_register / rok_timer_register / rok_coro_park outside a task");
    }
    // SAFETY: published once, never freed.
    unsafe { *h }
}

/// Wake `waker` once `fd` may be readable (`interest & 1`) or writable
/// (`interest & 2`); one-shot, edge-triggered (spurious wakes possible).
///
/// # Safety
/// `waker` must be a live `GcBuf<Waker>`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_io_register(fd: i32, interest: u32, waker: *mut u8) {
    // SAFETY: an installed hook; caller contract.
    unsafe { (hooks().io)(fd, interest, waker) };
}

/// Wake `waker` once `rok_time_now_ns()` reaches `deadline` (ns).
///
/// # Safety
/// `waker` must be a live `GcBuf<Waker>`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_timer_register(deadline: u64, waker: *mut u8) {
    // SAFETY: as above.
    unsafe { (hooks().timer)(deadline, waker) };
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
    uncaught(&[UNCAUGHT, what.bytes(), b"\n"])
}

const UNCAUGHT: &[u8] = b"error: `main` returned an uncaught error: ";

/// `rok_uncaught_error` plus the `path:line:col` the error left `main`
/// at, on a second line.
#[unsafe(no_mangle)]
pub extern "C" fn rok_uncaught_error_at(what: RokStr, at: RokStr) -> ! {
    uncaught(&[UNCAUGHT, what.bytes(), b"\n  --> ", at.bytes(), b"\n"])
}

fn uncaught(parts: &[&[u8]]) -> ! {
    rokr_common::write_all(2, parts);
    exit(1)
}

// ---------------------------------------------------------------------
// 8.5.7 Diagnostics
// ---------------------------------------------------------------------

/// Unrecoverable panic: `thread '<name>' panicked:`, `msg` and `\n` to
/// stderr, then exit 101.
///
/// # Safety
/// `msg` must be null or valid for reads of `msg_len` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_panic(msg: *const u8, msg_len: usize) -> ! {
    let msg = RokStr {
        ptr: msg,
        len: if msg.is_null() { 0 } else { msg_len },
    };
    panic_at(msg.bytes(), None)
}

/// A panic's report, `thread '<name>' panicked at <at>:\n<msg>\n` (no
/// ` at <at>` without a location), then exit 101.
pub(crate) fn panic_at(msg: &[u8], at: Option<&[u8]>) -> ! {
    let mut buf = [0u8; 64];
    let name = stack::thread_name(&mut buf);
    let (sep, at) = at.map_or((&b""[..], &b""[..]), |a| (&b" at "[..], a));
    rokr_common::write_all(
        2,
        &[
            b"thread '",
            name,
            b"' panicked",
            sep,
            at,
            b":\n",
            msg,
            b"\n",
        ],
    );
    exit(101)
}

/// `rok_panic_str` with the `path:line:col` of the code that panicked
/// (a failed runtime check, or the first caller outside a
/// `#[track_caller]` chain).
#[unsafe(no_mangle)]
pub extern "C" fn rok_panic_at(msg: RokStr, at: RokStr) -> ! {
    panic_at(msg.bytes(), Some(at.bytes()))
}

/// `rok::core::panic::oom()` (stdlib 2.14.5 `oom_fn`): out of memory,
/// exit 101. Runtime allocation failures take the same path.
#[unsafe(no_mangle)]
pub extern "C" fn rok_oom() -> ! {
    rokr_common::oom()
}

/// `rok_panic` for a rok `str` value.
#[unsafe(no_mangle)]
pub extern "C" fn rok_panic_str(msg: RokStr) -> ! {
    panic_at(msg.bytes(), None)
}

// ---------------------------------------------------------------------
// 8.5.12 appendix: convenience symbols (no ABI stability)
// ---------------------------------------------------------------------

/// `rok::std::env::exit(code)` (spec 4.16.4): exit now with `code`.
/// `finally` and `Drop` do not run; `exit` flushes buffered stdout.
#[unsafe(no_mangle)]
pub extern "C" fn rok_exit(code: i32) -> ! {
    exit(code)
}

/// The hook `rok_set_exit_hook` sets (null: none).
static EXIT_HOOK: core::sync::atomic::AtomicPtr<()> =
    core::sync::atomic::AtomicPtr::new(ptr::null_mut());

/// The hook a panic, an uncaught error, `exit` or (Windows) a stack
/// overflow calls before ending the process; null: none.
///
/// It gets the exit status, on the thread ending the process, which
/// ends when it returns. The Windows REPL host ends just the running
/// cell instead (it does not return).
#[unsafe(no_mangle)]
pub extern "C" fn rok_set_exit_hook(hook: Option<extern "C" fn(i32)>) {
    EXIT_HOOK.store(
        hook.map_or(ptr::null_mut(), |h| h as *mut ()),
        Ordering::Release,
    );
}

/// Run the exit hook, if any, for status `code`.
pub(crate) fn ending(code: i32) {
    let h = EXIT_HOOK.load(Ordering::Acquire);
    if !h.is_null() {
        // SAFETY: only `rok_set_exit_hook` stores, a function of this type.
        let hook = unsafe { core::mem::transmute::<*mut (), extern "C" fn(i32)>(h) };
        hook(code);
    }
}

/// The exit hook, then end the process with `code`; `exit` flushes
/// buffered stdout.
fn exit(code: i32) -> ! {
    ending(code);
    // SAFETY: plain libc call.
    unsafe { libc::exit(code) }
}

/// `rok::bare::alloc::alloc` (stdlib 1.4): null on failure (`size == 0`, bad `align`, overflow, OOM) instead of
/// aborting. `zeroed != 0` zero-fills. Freed with `rok_free`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_alloc_raw(size: usize, align: usize, zeroed: i32) -> *mut u8 {
    if size == 0 || !align.is_power_of_two() {
        return ptr::null_mut();
    }
    let Some(rounded) = size.checked_add(align - 1).map(|s| s & !(align - 1)) else {
        return ptr::null_mut();
    };
    let p = rokr_common::sys::alloc_aligned(rounded, align);
    if !p.is_null() && zeroed != 0 {
        // SAFETY: `p` is valid for `rounded` bytes.
        unsafe { ptr::write_bytes(p, 0, rounded) };
    }
    p
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
            rok_free(ptr);
        }
    }
    q
}

/// # Safety
/// `ptr` must be null or a live pointer returned by `rok_alloc_raw`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_free(ptr: *mut u8) {
    // SAFETY: caller contract; freeing null is a no-op.
    unsafe { rokr_common::sys::free_aligned(ptr) };
}

// Typed load/store through raw pointers.

/// # Safety
/// `ptr` must be valid and aligned for an `i32` read.
#[unsafe(no_mangle)]
pub const unsafe extern "C" fn rok_load_i32(ptr: *const i32) -> i32 {
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
pub const unsafe extern "C" fn rok_load_i64(ptr: *const i64) -> i64 {
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
pub const unsafe extern "C" fn rok_load_f64(ptr: *const f64) -> f64 {
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

#[cfg(test)]
mod tests {
    use super::*;
    use rokr_common::object_header::ObjectHeader;

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
        fmt::tests::formatter_ops();
        fuzz_tests::allocating();
    }
}
