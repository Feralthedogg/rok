//! Per-thread mutator TLS block (spec 008-abi/803).
//!
//! The 64-byte ABI-stable layout below matches 803 §8.3.1 exactly
//! (pointer slots are `u64` so offsets are identical on 32-bit, §8.3.5).
//!
//! GAP (803 §8.3.8): the spec has compiler-emitted code address each slot
//! as an exported `thread_local` global (`@rok_tls_yield_flag`, ...).
//! Stable Rust 1.85 `no_std` cannot define exported TLS symbols
//! (`#[thread_local]` is unstable), so the block lives behind a pthread
//! key and is reachable only through [`current`]. The one slot codegen
//! already uses, `rok_tls_shadow_stack_top`, is a real TLS symbol
//! defined in per-target assembly below ([`shadow_stack_top`]); its
//! `TlsBlock` field is unused. Upgrade path for the other slots: the same
//! `global_asm!`, or `#[thread_local]` once stable.

use core::mem::{offset_of, size_of};
use core::ptr;
use core::sync::atomic::{AtomicU8, AtomicU64, AtomicUsize, Ordering};

pub const MUTATOR_RUNNING: u8 = 0;
pub const MUTATOR_GC_COOPERATING: u8 = 1;
pub const MUTATOR_PARKED: u8 = 2;

#[repr(C, align(64))]
pub struct TlsBlock {
    /// Set by the GC (from another thread) to request a safepoint yield.
    pub yield_flag: AtomicU8,
    _pad0: [u8; 7],
    pub tlab_cursor: u64,
    pub tlab_limit: u64,
    pub shadow_stack_top: u64,
    pub wb_log_cursor: u64,
    pub wb_log_limit: u64,
    /// Read by the GC from another thread.
    pub mutator_state: AtomicU8,
    _pad1: [u8; 7],
    pub worker_id: u64,
}

const _: () = {
    assert!(size_of::<TlsBlock>() == 64);
    assert!(offset_of!(TlsBlock, yield_flag) == 0);
    assert!(offset_of!(TlsBlock, tlab_cursor) == 8);
    assert!(offset_of!(TlsBlock, tlab_limit) == 16);
    assert!(offset_of!(TlsBlock, shadow_stack_top) == 24);
    assert!(offset_of!(TlsBlock, wb_log_cursor) == 32);
    assert!(offset_of!(TlsBlock, wb_log_limit) == 40);
    assert!(offset_of!(TlsBlock, mutator_state) == 48);
    assert!(offset_of!(TlsBlock, worker_id) == 56);
};

/// pthread key + 1 (0 = not yet created).
static KEY: AtomicUsize = AtomicUsize::new(0);
static NEXT_WORKER_ID: AtomicU64 = AtomicU64::new(0);

unsafe extern "C" fn free_block(p: *mut libc::c_void) {
    // SAFETY: `p` came from `posix_memalign` in `current`.
    unsafe { libc::free(p) };
}

fn key() -> libc::pthread_key_t {
    let k = KEY.load(Ordering::Acquire);
    if k != 0 {
        return (k - 1) as libc::pthread_key_t;
    }
    let mut new: libc::pthread_key_t = 0;
    // SAFETY: `new` is a valid out-pointer; `free_block` matches the
    // destructor signature.
    if unsafe { libc::pthread_key_create(&mut new, Some(free_block)) } != 0 {
        crate::fatal(b"rok runtime: pthread_key_create failed");
    }
    match KEY.compare_exchange(0, new as usize + 1, Ordering::AcqRel, Ordering::Acquire) {
        Ok(_) => new,
        Err(won) => {
            // Lost the race: another thread created the key first.
            // SAFETY: `new` is our own, unused key.
            unsafe { libc::pthread_key_delete(new) };
            (won - 1) as libc::pthread_key_t
        }
    }
}

/// Reset `b` to the `rok_thread_init` state (803 §8.3.6). No GC exists
/// yet, so TLAB / shadow-stack / wb-log slots stay null.
fn reset(b: &mut TlsBlock) {
    b.yield_flag.store(0, Ordering::Relaxed);
    b.tlab_cursor = 0;
    b.tlab_limit = 0;
    b.shadow_stack_top = 0;
    b.wb_log_cursor = 0;
    b.wb_log_limit = 0;
    b.mutator_state.store(MUTATOR_RUNNING, Ordering::Relaxed);
    b.worker_id = NEXT_WORKER_ID.fetch_add(1, Ordering::Relaxed);
}

/// This thread's TLS block, allocated and initialized on first use.
/// Fatal on OOM; never null.
pub fn current() -> *mut TlsBlock {
    let k = key();
    // SAFETY: `k` is a live key.
    let p = unsafe { libc::pthread_getspecific(k) }.cast::<TlsBlock>();
    if !p.is_null() {
        return p;
    }
    let mut raw: *mut libc::c_void = ptr::null_mut();
    // SAFETY: valid out-pointer; 64 is a power of two multiple of
    // `size_of::<*mut c_void>()`.
    if unsafe { libc::posix_memalign(&mut raw, 64, size_of::<TlsBlock>()) } != 0 {
        crate::fatal(b"rok runtime: out of memory (TLS block)");
    }
    let p = raw.cast::<TlsBlock>();
    // SAFETY: fresh 64-byte, 64-aligned allocation; all-zero is a valid
    // `TlsBlock`, then `reset` fills the real values.
    unsafe {
        ptr::write_bytes(p, 0, 1);
        reset(&mut *p);
        libc::pthread_setspecific(k, raw);
    }
    p
}

/// `rok_thread_init` body: (re)initialize this thread's block.
pub fn thread_init() {
    // SAFETY: `current` never returns null and the block is owned by
    // this thread.
    unsafe { reset(&mut *current()) };
}

/// `rok_thread_shutdown` body: release this thread's block. A later
/// runtime call on this thread lazily allocates a fresh one.
pub fn thread_shutdown() {
    let k = key();
    // SAFETY: `k` is a live key; the stored block (if any) came from
    // `posix_memalign` and is only referenced by this thread.
    unsafe {
        let p = libc::pthread_getspecific(k);
        if !p.is_null() {
            libc::pthread_setspecific(k, ptr::null());
            libc::free(p);
        }
    }
}

/// Clear this thread's yield request (`rok_runtime_yield` slow path).
pub fn clear_yield() {
    // SAFETY: `current` never returns null.
    unsafe { (*current()).yield_flag.store(0, Ordering::Relaxed) };
}

// `rok_tls_shadow_stack_top` (803 §8.3.8, 704 §7.4.1): head of this
// thread's shadow-stack frame chain, pushed / popped by compiled code.
// Zero-initialized TLS, plus a hidden accessor returning its address so
// the runtime can read it without `#[thread_local]`.
#[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
core::arch::global_asm!(
    ".tbss _rok_tls_shadow_stack_top$tlv$init, 8, 3",
    ".section __DATA,__thread_vars,thread_local_variables",
    ".globl _rok_tls_shadow_stack_top",
    "_rok_tls_shadow_stack_top:",
    ".quad __tlv_bootstrap",
    ".quad 0",
    ".quad _rok_tls_shadow_stack_top$tlv$init",
    ".text",
    ".private_extern _rokr_tls_shadow_stack_top_addr",
    ".globl _rokr_tls_shadow_stack_top_addr",
    ".p2align 2",
    "_rokr_tls_shadow_stack_top_addr:",
    "adrp x0, _rok_tls_shadow_stack_top@TLVPPAGE",
    "ldr x0, [x0, _rok_tls_shadow_stack_top@TLVPPAGEOFF]",
    "ldr x16, [x0]",
    "br x16", // tail-call the TLV thunk: it returns the address in x0
);
#[cfg(all(target_vendor = "apple", target_arch = "x86_64"))]
core::arch::global_asm!(
    ".tbss _rok_tls_shadow_stack_top$tlv$init, 8, 3",
    ".section __DATA,__thread_vars,thread_local_variables",
    ".globl _rok_tls_shadow_stack_top",
    "_rok_tls_shadow_stack_top:",
    ".quad __tlv_bootstrap",
    ".quad 0",
    ".quad _rok_tls_shadow_stack_top$tlv$init",
    ".text",
    ".private_extern _rokr_tls_shadow_stack_top_addr",
    ".globl _rokr_tls_shadow_stack_top_addr",
    "_rokr_tls_shadow_stack_top_addr:",
    "mov rdi, qword ptr [rip + _rok_tls_shadow_stack_top@TLVP]",
    "jmp qword ptr [rdi]",
);
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
core::arch::global_asm!(
    ".pushsection .tbss,\"awT\",@nobits",
    ".p2align 3",
    ".globl rok_tls_shadow_stack_top",
    ".type rok_tls_shadow_stack_top,@object",
    ".size rok_tls_shadow_stack_top,8",
    "rok_tls_shadow_stack_top:",
    ".zero 8",
    ".popsection",
    ".globl rokr_tls_shadow_stack_top_addr",
    ".hidden rokr_tls_shadow_stack_top_addr",
    ".type rokr_tls_shadow_stack_top_addr,@function",
    "rokr_tls_shadow_stack_top_addr:",
    #[cfg(target_arch = "x86_64")]
    "mov rax, qword ptr fs:[0]",
    #[cfg(target_arch = "x86_64")]
    "add rax, qword ptr [rip + rok_tls_shadow_stack_top@GOTTPOFF]",
    // Local-exec: the runtime is always linked into the executable.
    #[cfg(target_arch = "aarch64")]
    "mrs x0, tpidr_el0",
    #[cfg(target_arch = "aarch64")]
    "add x0, x0, :tprel_hi12:rok_tls_shadow_stack_top",
    #[cfg(target_arch = "aarch64")]
    "add x0, x0, :tprel_lo12_nc:rok_tls_shadow_stack_top",
    "ret",
);
#[cfg(not(any(
    target_vendor = "apple",
    all(
        target_os = "linux",
        any(target_arch = "x86_64", target_arch = "aarch64")
    )
)))]
compile_error!("rokr: no `rok_tls_shadow_stack_top` definition for this target");

unsafe extern "C" {
    fn rokr_tls_shadow_stack_top_addr() -> *mut *mut u8;
}

/// Address of this thread's `rok_tls_shadow_stack_top`.
pub fn shadow_stack_top() -> *mut *mut u8 {
    // SAFETY: the assembly above takes no arguments and only returns the
    // address of this thread's TLS slot.
    unsafe { rokr_tls_shadow_stack_top_addr() }
}
