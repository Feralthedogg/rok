//! Mutator TLS slots (spec 008-abi/803).
//!
//! Every slot of 803 §8.3.1 is its own exported `thread_local` global
//! (`rok_tls_yield_flag`, ...), defined in per-target assembly below
//! because stable `no_std` Rust cannot define exported TLS symbols
//! (`#[thread_local]` is unstable). Compiled code addresses the slots by
//! name; the runtime reaches its own thread's copy through a hidden
//! accessor per slot that returns the slot's address. Another thread's
//! slot is reached through the address its owner published in the thread
//! registry (`rokr_gc::world`).
//!
//! Targets: Mach-O `arm64` / `x86_64` (`__thread_vars`), ELF `x86_64`
//! (initial-exec) / `aarch64` (local-exec: the runtime is always linked
//! into the executable).

use core::sync::atomic::{AtomicU8, AtomicU64, Ordering};

pub const MUTATOR_RUNNING: u8 = 0;
pub const MUTATOR_GC_COOPERATING: u8 = 1;
pub const MUTATOR_PARKED: u8 = 2;

static NEXT_WORKER_ID: AtomicU64 = AtomicU64::new(0);

/// Defines each slot (`rok_tls_<name>`, `size` bytes, 2^`align` aligned,
/// zero-initialized) plus its address accessor `<acc>`, and a
/// `pub fn <name>() -> *mut u8` returning this thread's slot address.
macro_rules! tls_slots {
    ($($name:ident => $acc:ident, $size:literal, $align:literal;)*) => {
        #[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
        core::arch::global_asm!($(concat!(
            ".tbss _rok_tls_", stringify!($name), "$tlv$init, ", $size, ", ", $align, "\n",
            ".section __DATA,__thread_vars,thread_local_variables\n",
            ".globl _rok_tls_", stringify!($name), "\n",
            "_rok_tls_", stringify!($name), ":\n",
            ".quad __tlv_bootstrap\n",
            ".quad 0\n",
            ".quad _rok_tls_", stringify!($name), "$tlv$init\n",
            ".text\n",
            ".private_extern _", stringify!($acc), "\n",
            ".globl _", stringify!($acc), "\n",
            ".p2align 2\n",
            "_", stringify!($acc), ":\n",
            "adrp x0, _rok_tls_", stringify!($name), "@TLVPPAGE\n",
            "ldr x0, [x0, _rok_tls_", stringify!($name), "@TLVPPAGEOFF]\n",
            "ldr x16, [x0]\n",
            // Tail-call the TLV thunk: it returns the address in x0.
            "br x16\n",
        )),*);
        #[cfg(all(target_vendor = "apple", target_arch = "x86_64"))]
        core::arch::global_asm!($(concat!(
            ".tbss _rok_tls_", stringify!($name), "$tlv$init, ", $size, ", ", $align, "\n",
            ".section __DATA,__thread_vars,thread_local_variables\n",
            ".globl _rok_tls_", stringify!($name), "\n",
            "_rok_tls_", stringify!($name), ":\n",
            ".quad __tlv_bootstrap\n",
            ".quad 0\n",
            ".quad _rok_tls_", stringify!($name), "$tlv$init\n",
            ".text\n",
            ".private_extern _", stringify!($acc), "\n",
            ".globl _", stringify!($acc), "\n",
            "_", stringify!($acc), ":\n",
            "mov rdi, qword ptr [rip + _rok_tls_", stringify!($name), "@TLVP]\n",
            "jmp qword ptr [rdi]\n",
        )),*);
        #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
        core::arch::global_asm!($(concat!(
            ".pushsection .tbss,\"awT\",@nobits\n",
            ".p2align ", $align, "\n",
            ".globl rok_tls_", stringify!($name), "\n",
            ".type rok_tls_", stringify!($name), ",@object\n",
            ".size rok_tls_", stringify!($name), ",", $size, "\n",
            "rok_tls_", stringify!($name), ":\n",
            ".zero ", $size, "\n",
            ".popsection\n",
            ".globl ", stringify!($acc), "\n",
            ".hidden ", stringify!($acc), "\n",
            ".type ", stringify!($acc), ",@function\n",
            stringify!($acc), ":\n",
            "mov rax, qword ptr fs:[0]\n",
            "add rax, qword ptr [rip + rok_tls_", stringify!($name), "@GOTTPOFF]\n",
            "ret\n",
        )),*);
        #[cfg(all(target_os = "linux", target_arch = "aarch64"))]
        core::arch::global_asm!($(concat!(
            ".pushsection .tbss,\"awT\",@nobits\n",
            ".p2align ", $align, "\n",
            ".globl rok_tls_", stringify!($name), "\n",
            ".type rok_tls_", stringify!($name), ",@object\n",
            ".size rok_tls_", stringify!($name), ",", $size, "\n",
            "rok_tls_", stringify!($name), ":\n",
            ".zero ", $size, "\n",
            ".popsection\n",
            ".globl ", stringify!($acc), "\n",
            ".hidden ", stringify!($acc), "\n",
            ".type ", stringify!($acc), ",%function\n",
            stringify!($acc), ":\n",
            "mrs x0, tpidr_el0\n",
            "add x0, x0, :tprel_hi12:rok_tls_", stringify!($name), "\n",
            "add x0, x0, :tprel_lo12_nc:rok_tls_", stringify!($name), "\n",
            "ret\n",
        )),*);

        /// Address of this thread's `rok_tls_<name>` slot.
        pub mod slot {
            unsafe extern "C" {
                $(fn $acc() -> *mut u8;)*
            }
            $(
                pub fn $name() -> *mut u8 {
                    // SAFETY: the accessor takes no arguments and only
                    // returns the address of this thread's TLS slot.
                    unsafe { $acc() }
                }
            )*
        }
    };
}

#[cfg(not(any(
    target_vendor = "apple",
    all(
        target_os = "linux",
        any(target_arch = "x86_64", target_arch = "aarch64")
    )
)))]
compile_error!("rokr: no `rok_tls_*` definitions for this target");

// 803 §8.3.1. Pointer slots are 8 bytes: every supported target is
// 64-bit (§8.3.5 makes them pointer-width).
tls_slots! {
    yield_flag => rokr_tls_yield_flag_addr, 1, 0;
    tlab_cursor => rokr_tls_tlab_cursor_addr, 8, 3;
    tlab_limit => rokr_tls_tlab_limit_addr, 8, 3;
    shadow_stack_top => rokr_tls_shadow_stack_top_addr, 8, 3;
    wb_log_cursor => rokr_tls_wb_log_cursor_addr, 8, 3;
    wb_log_limit => rokr_tls_wb_log_limit_addr, 8, 3;
    mutator_state => rokr_tls_mutator_state_addr, 1, 0;
    worker_id => rokr_tls_worker_id_addr, 8, 3;
    // Not an 803 slot: the GC address of this thread's running task
    // executor (`rok::core::task`, `rok_task_exec_*`), 0 = none.
    task_exec => rokr_tls_task_exec_addr, 8, 3;
}

/// Address of this thread's `rok_tls_shadow_stack_top` (the head of its
/// shadow-stack frame chain, pushed / popped by compiled code).
#[allow(clippy::cast_ptr_alignment)] // 8-aligned slot
pub fn shadow_stack_top() -> *mut *mut u8 {
    slot::shadow_stack_top().cast()
}

/// This thread's `rok_tls_yield_flag` (set by a collecting thread).
pub fn yield_flag() -> &'static AtomicU8 {
    // SAFETY: the slot is a live, 1-byte TLS global of this thread;
    // `AtomicU8` has the layout of `u8`.
    unsafe { &*slot::yield_flag().cast::<AtomicU8>() }
}

/// This thread's `rok_tls_mutator_state` (read by a collecting thread).
pub fn mutator_state() -> &'static AtomicU8 {
    // SAFETY: as above.
    unsafe { &*slot::mutator_state().cast::<AtomicU8>() }
}

/// `rok_thread_init` slot values (803 §8.3.6). The TLAB starts empty
/// (the first allocation refills it); no write barrier log exists
/// (non-generational mark-region needs no barrier), so it stays null.
#[allow(clippy::cast_ptr_alignment)] // 8-aligned slots
pub fn thread_init() {
    yield_flag().store(0, Ordering::Relaxed);
    mutator_state().store(MUTATOR_RUNNING, Ordering::Relaxed);
    // SAFETY: each accessor returns this thread's own, aligned slot.
    unsafe {
        slot::tlab_cursor().cast::<usize>().write(0);
        slot::tlab_limit().cast::<usize>().write(0);
        shadow_stack_top().write(core::ptr::null_mut());
        slot::wb_log_cursor().cast::<usize>().write(0);
        slot::wb_log_limit().cast::<usize>().write(0);
        slot::worker_id().cast::<u64>().write(new_worker_id());
        slot::task_exec().cast::<usize>().write(0);
    }
}

/// Addresses of this thread's `rok_tls_tlab_cursor` and
/// `rok_tls_tlab_limit` (the bump range compiled code allocates from).
#[allow(clippy::cast_ptr_alignment)] // 8-aligned slots
pub fn tlab() -> [*mut usize; 2] {
    [slot::tlab_cursor().cast(), slot::tlab_limit().cast()]
}

/// Address of this thread's `rok_tls_task_exec` (its running executor).
#[allow(clippy::cast_ptr_alignment)] // 8-aligned slot
pub fn task_exec() -> *mut usize {
    slot::task_exec().cast()
}

/// Address of this thread's `rok_tls_worker_id`.
#[allow(clippy::cast_ptr_alignment)] // 8-aligned slot
pub fn worker_id() -> *mut u64 {
    slot::worker_id().cast()
}

/// A fresh, process-unique worker id.
pub fn new_worker_id() -> u64 {
    NEXT_WORKER_ID.fetch_add(1, Ordering::Relaxed)
}
