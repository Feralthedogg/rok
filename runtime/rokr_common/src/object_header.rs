//! 16-byte object header carried by every GC-managed allocation
//! (spec 008-abi/801, 007-runtime/702 §7.2.4).
//!
//! Layout (offsets in bytes):
//!   0  : `type_id`   u32
//!   4  : `gc_flags`  u32 (bit 0=MARK, 1=STICKY, 2=PINNED, 3=FORWARDED,
//!                          4=LARGE, 5=IMMORTAL)
//!   8  : `gc_word`   u64 (forwarding pointer or LOS payload size)
//!   16 : payload     ...

use core::mem::{align_of, offset_of, size_of};
use core::sync::atomic::AtomicU32;

/// `gc_flags` is atomic because MARK / FORWARDED are set during
/// concurrent mark / evacuate (801 §8.1.3).
#[repr(C, align(8))]
pub struct ObjectHeader {
    pub type_id: u32,
    pub gc_flags: AtomicU32,
    pub gc_word: u64,
}

pub const FLAG_MARK: u32 = 1 << 0;
pub const FLAG_STICKY: u32 = 1 << 1;
pub const FLAG_PINNED: u32 = 1 << 2;
pub const FLAG_FORWARDED: u32 = 1 << 3;
pub const FLAG_LARGE: u32 = 1 << 4;
pub const FLAG_IMMORTAL: u32 = 1 << 5;

pub const HEADER_SIZE: usize = 16;
pub const HEADER_ALIGN: usize = 8;

const _: () = {
    assert!(size_of::<ObjectHeader>() == HEADER_SIZE);
    assert!(align_of::<ObjectHeader>() == HEADER_ALIGN);
    assert!(offset_of!(ObjectHeader, type_id) == 0);
    assert!(offset_of!(ObjectHeader, gc_flags) == 4);
    assert!(offset_of!(ObjectHeader, gc_word) == 8);
};

impl ObjectHeader {
    /// Write a fresh header (702 §7.2.4): `type_id`, `gc_flags = 0`,
    /// `gc_word = 0`.
    ///
    /// # Safety
    /// `obj` must be valid for writes of `HEADER_SIZE` bytes and
    /// `HEADER_ALIGN`-aligned.
    #[allow(clippy::cast_ptr_alignment)] // alignment is the caller contract
    pub const unsafe fn init(obj: *mut u8, type_id: u32) {
        let header = Self {
            type_id,
            gc_flags: AtomicU32::new(0),
            gc_word: 0,
        };
        // SAFETY: caller guarantees size and alignment.
        unsafe { obj.cast::<Self>().write(header) };
    }
}
