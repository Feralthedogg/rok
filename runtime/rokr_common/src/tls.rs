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
//! (initial-exec) / `aarch64` / `x86` (`%gs`) / `arm` (`TPIDRURO`, what
//! `__aeabi_read_tp` reads on Linux) (local-exec: the runtime is always
//! linked into the executable), COFF `x86_64` / `aarch64` / `x86`
//! (`.tls$`, through `_tls_index` and the TEB's TLS array; rokc's
//! startup object defines `_tls_index` and the TLS directory). wasm32
//! without threads: plain globals; `wasm32-wasi-threads`: rokc's startup
//! object defines them (and their accessors) in wasm TLS (`__tls_base`).
//!
//! Sizes and alignments are spliced into the assembly as text: `{p}` /
//! `{pa}` are the pointer width and its log2 alignment (803 §8.3.5),
//! `{p2}` two pointers.

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
        tls_slots!(@asm $($name => $acc, $size, $align;)*);
        /// Address of this thread's `rok_tls_<name>` slot (on
        /// `wasm32-wasi-threads` rokc's startup object defines the slots
        /// and accessors: stable Rust cannot define wasm TLS).
        #[cfg(not(rok_solo))]
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
        /// One thread: each slot is a plain global (what LLVM makes of
        /// compiled code's `thread_local` globals without the atomics
        /// feature), 16 bytes, room for the largest (`{p2}`).
        #[cfg(rok_solo)]
        pub mod slot {
            #[repr(C, align(8))]
            struct Slot(core::cell::UnsafeCell<[u8; 16]>);
            // SAFETY: one thread.
            unsafe impl Sync for Slot {}
            $(
                #[unsafe(export_name = concat!("rok_tls_", stringify!($name)))]
                #[allow(non_upper_case_globals)]
                static $acc: Slot = Slot(core::cell::UnsafeCell::new([0; 16]));
                // Not `const`: the other targets' accessors cannot be.
                #[allow(clippy::missing_const_for_fn)]
                pub fn $name() -> *mut u8 {
                    $acc.0.get().cast()
                }
            )*
        }
    };
    (@asm $($name:ident => $acc:ident, $size:literal, $align:literal;)*) => {
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
        )),*, p = const PTR, pa = const PTR_ALIGN, p2 = const 2 * PTR);
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
        )),*, p = const PTR, pa = const PTR_ALIGN, p2 = const 2 * PTR);
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
        )),*, p = const PTR, pa = const PTR_ALIGN, p2 = const 2 * PTR);
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
        )),*, p = const PTR, pa = const PTR_ALIGN, p2 = const 2 * PTR);

        #[cfg(all(windows, target_arch = "x86_64"))]
        core::arch::global_asm!($(concat!(
            ".section .tls$,\"dw\"\n",
            ".p2align ", $align, "\n",
            ".globl rok_tls_", stringify!($name), "\n",
            "rok_tls_", stringify!($name), ":\n",
            ".zero ", $size, "\n",
            ".text\n",
            ".globl ", stringify!($acc), "\n",
            ".p2align 4\n",
            stringify!($acc), ":\n",
            "mov eax, dword ptr [rip + _tls_index]\n",
            "mov rcx, qword ptr gs:[0x58]\n",
            "mov rcx, qword ptr [rcx + 8*rax]\n",
            "lea rax, [rcx + rok_tls_", stringify!($name), "@SECREL32]\n",
            "ret\n",
        )),*, p = const PTR, pa = const PTR_ALIGN, p2 = const 2 * PTR);
        #[cfg(all(windows, target_arch = "aarch64"))]
        core::arch::global_asm!($(concat!(
            ".section .tls$,\"dw\"\n",
            ".p2align ", $align, "\n",
            ".globl rok_tls_", stringify!($name), "\n",
            "rok_tls_", stringify!($name), ":\n",
            ".zero ", $size, "\n",
            ".text\n",
            ".globl ", stringify!($acc), "\n",
            ".p2align 2\n",
            stringify!($acc), ":\n",
            "adrp x8, _tls_index\n",
            "ldr w8, [x8, :lo12:_tls_index]\n",
            "ldr x9, [x18, #0x58]\n",
            "ldr x9, [x9, x8, lsl #3]\n",
            "add x9, x9, :secrel_hi12:rok_tls_", stringify!($name), "\n",
            "add x0, x9, :secrel_lo12:rok_tls_", stringify!($name), "\n",
            "ret\n",
        )),*, p = const PTR, pa = const PTR_ALIGN, p2 = const 2 * PTR);
        #[cfg(all(target_os = "linux", target_arch = "x86"))]
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
            "mov eax, dword ptr gs:[0]\n",
            "lea eax, [eax + rok_tls_", stringify!($name), "@NTPOFF]\n",
            "ret\n",
        )),*, p = const PTR, pa = const PTR_ALIGN, p2 = const 2 * PTR);
        #[cfg(all(target_os = "linux", target_arch = "arm"))]
        core::arch::global_asm!($(concat!(
            ".pushsection .tbss,\"awT\",%nobits\n",
            ".p2align ", $align, "\n",
            ".globl rok_tls_", stringify!($name), "\n",
            ".type rok_tls_", stringify!($name), ",%object\n",
            ".size rok_tls_", stringify!($name), ",", $size, "\n",
            "rok_tls_", stringify!($name), ":\n",
            ".zero ", $size, "\n",
            ".popsection\n",
            ".globl ", stringify!($acc), "\n",
            ".hidden ", stringify!($acc), "\n",
            ".type ", stringify!($acc), ",%function\n",
            ".p2align 2\n",
            stringify!($acc), ":\n",
            "mrc p15, 0, r0, c13, c0, 3\n",
            "ldr r1, 1f\n",
            "add r0, r0, r1\n",
            "bx lr\n",
            "1: .long rok_tls_", stringify!($name), "(TPOFF)\n",
        )),*, p = const PTR, pa = const PTR_ALIGN, p2 = const 2 * PTR);
        // C names carry a leading underscore on x86 COFF.
        #[cfg(all(windows, target_arch = "x86"))]
        core::arch::global_asm!($(concat!(
            ".section .tls$,\"dw\"\n",
            ".p2align ", $align, "\n",
            ".globl _rok_tls_", stringify!($name), "\n",
            "_rok_tls_", stringify!($name), ":\n",
            ".zero ", $size, "\n",
            ".text\n",
            ".globl _", stringify!($acc), "\n",
            ".p2align 4\n",
            "_", stringify!($acc), ":\n",
            "mov eax, dword ptr [__tls_index]\n",
            "mov ecx, dword ptr fs:[0x2c]\n",
            "mov ecx, dword ptr [ecx + 4*eax]\n",
            "lea eax, [ecx + _rok_tls_", stringify!($name), "@SECREL32]\n",
            "ret\n",
        )),*, p = const PTR, pa = const PTR_ALIGN, p2 = const 2 * PTR);
    };
}

// The assembly's `{p}` / `{pa}` (wasm32 has no assembly).
#[cfg(not(target_family = "wasm"))]
const PTR: usize = size_of::<usize>();
#[cfg(not(target_family = "wasm"))]
const PTR_ALIGN: u32 = PTR.trailing_zeros();

#[cfg(not(any(
    target_vendor = "apple",
    target_family = "wasm",
    all(
        any(target_os = "linux", windows),
        any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "x86")
    ),
    all(target_os = "linux", target_arch = "arm")
)))]
compile_error!("rokr: no `rok_tls_*` definitions for this target");

// 803 §8.3.1; pointer slots are pointer-width (§8.3.5). `wasm32-wasi-threads`
// gets them from rokc (`WASM_TLS_SLOTS`, rokc_driver toolchain.rs): keep
// both in step.
tls_slots! {
    yield_flag => rokr_tls_yield_flag_addr, 1, 0;
    tlab_cursor => rokr_tls_tlab_cursor_addr, "{p}", "{pa}";
    tlab_limit => rokr_tls_tlab_limit_addr, "{p}", "{pa}";
    shadow_stack_top => rokr_tls_shadow_stack_top_addr, "{p}", "{pa}";
    wb_log_cursor => rokr_tls_wb_log_cursor_addr, "{p}", "{pa}";
    wb_log_limit => rokr_tls_wb_log_limit_addr, "{p}", "{pa}";
    mutator_state => rokr_tls_mutator_state_addr, 1, 0;
    worker_id => rokr_tls_worker_id_addr, 8, 3;
    // Not an 803 slot: this thread's task-executor worker
    // (`rok::core::task`), a pinned GC object, 0 = none.
    task_worker => rokr_tls_task_worker_addr, "{p}", "{pa}";
    // Not an 803 slot: the executor lane this thread runs (`rokr::lane`),
    // a malloc'd record, 0 = none.
    task_lane => rokr_tls_task_lane_addr, "{p}", "{pa}";
    // Not an 803 slot: `[lo, hi)`, the addresses whose fault means this
    // thread overflowed its stack (`rokr::stack`); `[0, 0)` = unknown.
    stack_guard => rokr_tls_stack_guard_addr, "{p2}", "{pa}";
    // Not 803 slots: this thread's SATB log chunk (`rokr_gc`, concurrent
    // marking), like the wb log pair.
    satb_cursor => rokr_tls_satb_cursor_addr, "{p}", "{pa}";
    satb_limit => rokr_tls_satb_limit_addr, "{p}", "{pa}";
    // Not an 803 slot: the head of this thread's list of running static
    // initializers (`rokr::thread`), null = none.
    static_inits => rokr_tls_static_inits_addr, "{p}", "{pa}";
    // Not an 803 slot: the locks this thread holds outside the task
    // executor (`rokr_gc::world::note_lock`), a malloc'd record, null =
    // none yet.
    held_locks => rokr_tls_held_locks_addr, "{p}", "{pa}";
}

/// Address of this thread's `rok_tls_stack_guard` (`[lo, hi)`).
#[allow(clippy::cast_ptr_alignment)] // pointer-aligned slot
pub fn stack_guard() -> *mut [usize; 2] {
    slot::stack_guard().cast()
}

/// Address of this thread's `rok_tls_shadow_stack_top` (the head of its
/// shadow-stack frame chain, pushed / popped by compiled code).
#[allow(clippy::cast_ptr_alignment)] // pointer-aligned slot
pub fn shadow_stack_top() -> *mut *mut u8 {
    slot::shadow_stack_top().cast()
}

/// The `rok_tls_yield_flag` bit of a stop (the runtime raises and clears
/// it).
///
/// Other bits are the embedder's: the Windows REPL host raises one to
/// end a running cell. Compiled code's polls take the slow path for any
/// nonzero flag.
pub const YIELD_STOP: u8 = 1;

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
/// (the first allocation refills it); the write barrier logs into its
/// own remembered-set chunk, allocated by the first logged store.
#[allow(clippy::cast_ptr_alignment)] // pointer-aligned slots
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
        slot::satb_cursor().cast::<usize>().write(0);
        slot::satb_limit().cast::<usize>().write(0);
        slot::worker_id().cast::<u64>().write(new_worker_id());
        slot::task_worker().cast::<usize>().write(0);
        slot::task_lane().cast::<usize>().write(0);
        slot::held_locks().cast::<usize>().write(0);
    }
}

/// Addresses of this thread's `rok_tls_wb_log_cursor` and
/// `rok_tls_wb_log_limit` (its remembered-set chunk, `rokr_gc`).
#[allow(clippy::cast_ptr_alignment)] // pointer-aligned slots
pub fn wb_log() -> [*mut usize; 2] {
    [slot::wb_log_cursor().cast(), slot::wb_log_limit().cast()]
}

/// Addresses of this thread's `rok_tls_satb_cursor` and
/// `rok_tls_satb_limit` (its SATB log chunk, `rokr_gc`).
#[allow(clippy::cast_ptr_alignment)] // pointer-aligned slots
pub fn satb_log() -> [*mut usize; 2] {
    [slot::satb_cursor().cast(), slot::satb_limit().cast()]
}

/// Addresses of this thread's `rok_tls_tlab_cursor` and
/// `rok_tls_tlab_limit` (the bump range compiled code allocates from).
#[allow(clippy::cast_ptr_alignment)] // pointer-aligned slots
pub fn tlab() -> [*mut usize; 2] {
    [slot::tlab_cursor().cast(), slot::tlab_limit().cast()]
}

/// Address of this thread's `rok_tls_task_worker`.
#[allow(clippy::cast_ptr_alignment)] // pointer-aligned slot
pub fn task_worker() -> *mut usize {
    slot::task_worker().cast()
}

/// Address of this thread's `rok_tls_static_inits`.
#[allow(clippy::cast_ptr_alignment)] // pointer-aligned slot
pub fn static_inits() -> *mut usize {
    slot::static_inits().cast()
}

/// Address of this thread's `rok_tls_held_locks`.
#[allow(clippy::cast_ptr_alignment)] // pointer-aligned slot
pub fn held_locks() -> *mut usize {
    slot::held_locks().cast()
}

/// Address of this thread's `rok_tls_task_lane`.
#[allow(clippy::cast_ptr_alignment)] // pointer-aligned slot
pub fn task_lane() -> *mut usize {
    slot::task_lane().cast()
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
