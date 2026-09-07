//! OS threads (706 §7.6.6, 805 §8.5.4) and the address-keyed wait queue
//! the `rok::core::sync` primitives block on.

use core::mem::size_of;
use core::ptr;
use core::sync::atomic::{AtomicI32, Ordering};

use rokr_common::object_header::HEADER_SIZE;
use rokr_common::tls;
use rokr_gc::world;

/// A rok `fn()` value: `{code, env}`; `code` takes the env first (808).
#[repr(C)]
#[derive(Clone, Copy)]
pub struct RokFn {
    code: Option<unsafe extern "C" fn(*mut u8)>,
    env: *mut u8,
}

struct Start {
    me: *mut world::Mutator,
    f: RokFn,
}

/// Default stack of a spawned thread: rok frames are large in debug
/// builds and the platform default (512 KiB on macOS) is small.
const DEFAULT_STACK: usize = 8 << 20;

extern "C" fn thread_main(arg: *mut libc::c_void) -> *mut libc::c_void {
    // SAFETY: `arg` is the `Start` that `rok_thread_spawn` leaked to us.
    let s = unsafe { ptr::read(arg.cast::<Start>()) };
    // SAFETY: allocated with `malloc` in `rok_thread_spawn`.
    unsafe { libc::free(arg) };
    tls::thread_init();
    // SAFETY: registered for this thread by `rok_thread_spawn`.
    unsafe { world::attach(s.me) };
    if let Some(code) = s.f.code {
        // SAFETY: a rok `fn()` code pointer called with its own env.
        unsafe { code(s.f.env) };
    }
    world::detach();
    ptr::null_mut()
}

/// A fresh thread id for [`rok_thread_spawn`].
#[unsafe(no_mangle)]
pub extern "C" fn rok_thread_new_id() -> u64 {
    tls::new_worker_id()
}

/// Start an OS thread running the rok closure `f` (`stack_size` bytes of
/// stack, 0 = default) whose `rok_tls_worker_id` is `id` (from
/// [`rok_thread_new_id`]). Returns an opaque join handle, or 0 if the
/// thread could not be created. `f`'s environment stays a GC root until
/// the thread ends.
// ponytail: 805 gives `rok_thread_spawn(closure: Ptr<u8>) -> Ptr<u8>`;
// a rok closure is the `{code, env}` pair, so it crosses as that pair.
#[unsafe(no_mangle)]
pub extern "C" fn rok_thread_spawn(f: RokFn, stack_size: usize, id: u64) -> usize {
    let me = world::register(f.env, id);
    // SAFETY: plain allocation.
    let start = unsafe { libc::malloc(size_of::<Start>()) }.cast::<Start>();
    if start.is_null() {
        rokr_common::oom();
    }
    // SAFETY: `start` is fresh; the attr / thread calls get valid
    // out-pointers.
    unsafe {
        start.write(Start { me, f });
        let mut attr: libc::pthread_attr_t = core::mem::zeroed();
        libc::pthread_attr_init(&mut attr);
        let size = if stack_size == 0 {
            DEFAULT_STACK
        } else {
            stack_size.max(libc::PTHREAD_STACK_MIN)
        };
        libc::pthread_attr_setstacksize(&mut attr, size);
        let mut tid: libc::pthread_t = core::mem::zeroed();
        let rc = libc::pthread_create(&mut tid, &attr, thread_main, start.cast());
        libc::pthread_attr_destroy(&mut attr);
        if rc != 0 {
            libc::free(start.cast());
            world::unregister(me); // the thread never started
            return 0;
        }
        tid as usize
    }
}

/// Wait for the thread behind `handle` to finish. 0 on success.
// ponytail: a handle that is never joined leaks its pthread (no detach
// on drop: rok has no implicit drop). `JoinHandle::detach` is the fix.
#[unsafe(no_mangle)]
pub extern "C" fn rok_thread_join(handle: usize) -> i32 {
    world::enter_native();
    // SAFETY: `handle` came from `rok_thread_spawn`.
    let rc = unsafe { libc::pthread_join(handle as libc::pthread_t, ptr::null_mut()) };
    world::leave_native();
    rc
}

/// This thread's worker id (`rok_tls_worker_id`), the `ThreadId`.
#[unsafe(no_mangle)]
#[allow(clippy::cast_ptr_alignment)] // 8-aligned slot
pub extern "C" fn rok_thread_id() -> u64 {
    // SAFETY: this thread's own slot.
    unsafe { tls::worker_id().read() }
}

/// Block the calling thread for `ns` nanoseconds (negative = 0).
#[unsafe(no_mangle)]
pub extern "C" fn rok_thread_sleep_ns(ns: i64) {
    let ns = ns.max(0);
    let mut ts = libc::timespec {
        tv_sec: (ns / 1_000_000_000) as libc::time_t,
        tv_nsec: (ns % 1_000_000_000) as libc::c_long,
    };
    world::enter_native();
    // SAFETY: `ts` is valid for read and write (remaining time).
    while unsafe { libc::nanosleep(&ts, &mut ts) } != 0 {}
    world::leave_native();
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_thread_yield_now() {
    // SAFETY: no preconditions.
    unsafe { libc::sched_yield() };
}

// ---------------------------------------------------------------------
// Wait queue: futex semantics over a fixed table of pthread
// mutex/condvar buckets keyed by address. Spurious wakeups are allowed
// (callers re-check), so a bucket shared by unrelated words is fine.
// ponytail: portable stand-in for futex (Linux) / `__ulock` (macOS).
// ---------------------------------------------------------------------

struct Bucket {
    lock: core::cell::UnsafeCell<libc::pthread_mutex_t>,
    cond: core::cell::UnsafeCell<libc::pthread_cond_t>,
}

// SAFETY: pthread objects are designed for shared use.
unsafe impl Sync for Bucket {}

static BUCKETS: [Bucket; 64] = [const {
    Bucket {
        lock: core::cell::UnsafeCell::new(libc::PTHREAD_MUTEX_INITIALIZER),
        cond: core::cell::UnsafeCell::new(libc::PTHREAD_COND_INITIALIZER),
    }
}; 64];

fn bucket(addr: usize) -> &'static Bucket {
    &BUCKETS[(addr >> 2) % BUCKETS.len()]
}

/// Address of `i32` element `index` of the `GcBuf<i32>` object `buf`.
#[allow(clippy::cast_ptr_alignment)] // i32 buffer elements are 4-aligned
fn word(buf: *mut u8, index: usize) -> &'static AtomicI32 {
    // SAFETY: the caller's frame keeps `buf` alive; the collector does not
    // move objects; element `index` is inside it.
    unsafe { &*buf.add(HEADER_SIZE + index * 4).cast::<AtomicI32>() }
}

/// Block while element `index` of the `GcBuf<i32>` `buf` equals
/// `expected` (or until woken; may return spuriously). The thread counts
/// as stopped for the GC meanwhile.
#[unsafe(no_mangle)]
pub extern "C" fn rok_sync_wait(buf: *mut u8, index: usize, expected: i32) {
    let w = word(buf, index);
    let b = bucket(ptr::from_ref(w) as usize);
    world::enter_native();
    // SAFETY: statically initialized pthread objects.
    unsafe {
        libc::pthread_mutex_lock(b.lock.get());
        if w.load(Ordering::SeqCst) == expected {
            libc::pthread_cond_wait(b.cond.get(), b.lock.get());
        }
        libc::pthread_mutex_unlock(b.lock.get());
    }
    world::leave_native();
}

/// Wake every thread blocked in `rok_sync_wait` on that element.
#[unsafe(no_mangle)]
pub extern "C" fn rok_sync_wake(buf: *mut u8, index: usize) {
    let b = bucket(ptr::from_ref(word(buf, index)) as usize);
    // SAFETY: statically initialized pthread objects.
    unsafe {
        libc::pthread_mutex_lock(b.lock.get());
        libc::pthread_cond_broadcast(b.cond.get());
        libc::pthread_mutex_unlock(b.lock.get());
    }
}
