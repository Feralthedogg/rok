//! OS threads (706 §7.6.6, 805 §8.5.4) and the one address-keyed wait
//! queue every blocking wait in the runtime and in `rok::core::sync`
//! goes through.

use core::mem::size_of;
use core::ptr;
use core::sync::atomic::{AtomicI32, AtomicU8, AtomicUsize, Ordering};

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

/// Rok frames are large in debug builds and the macOS default (512 KiB)
/// is small.
const DEFAULT_STACK: usize = 8 << 20;

extern "C" fn thread_main(arg: *mut libc::c_void) -> *mut libc::c_void {
    // SAFETY: `arg` is the `Start` that `rok_thread_spawn` leaked to us.
    let s = unsafe { ptr::read(arg.cast::<Start>()) };
    // SAFETY: allocated with `malloc` in `rok_thread_spawn`.
    unsafe { libc::free(arg) };
    tls::thread_init();
    crate::stack::thread_start(false);
    // SAFETY: registered for this thread by `rok_thread_spawn`.
    unsafe { world::attach(s.me) };
    if let Some(code) = s.f.code {
        // SAFETY: a rok `fn()` code pointer called with its own env.
        unsafe { code(s.f.env) };
    }
    thread_exit();
    ptr::null_mut()
}

/// Leave the mutator registry; the thread must not touch GC objects
/// afterwards.
pub fn thread_exit() {
    rok_task_worker_clear();
    world::detach();
    crate::stack::thread_exit();
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
/// the thread ends. 805 has `rok_thread_spawn(closure: Ptr<u8>)`; a rok
/// closure crosses as its `{code, env}` pair.
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
            world::unregister(me);
            return 0;
        }
        tid as usize
    }
}

/// Wait for the thread behind `handle` to finish. 0 on success.
#[unsafe(no_mangle)]
pub extern "C" fn rok_thread_join(handle: usize) -> i32 {
    world::enter_native();
    // SAFETY: `handle` came from `rok_thread_spawn`.
    let rc = unsafe { libc::pthread_join(handle as libc::pthread_t, ptr::null_mut()) };
    world::leave_native();
    rc
}

/// Let the thread behind `handle` release its OS resources when it ends;
/// the handle is no longer joinable. 0 on success.
#[unsafe(no_mangle)]
pub extern "C" fn rok_thread_detach(handle: usize) -> i32 {
    // SAFETY: `handle` came from `rok_thread_spawn` and was not joined.
    unsafe { libc::pthread_detach(handle as libc::pthread_t) }
}

/// Online CPUs (at least 1): the executor's width.
#[unsafe(no_mangle)]
pub extern "C" fn rok_cpu_count() -> usize {
    // SAFETY: plain sysconf query.
    let n = unsafe { libc::sysconf(libc::_SC_NPROCESSORS_ONLN) };
    n.max(1) as usize
}

/// This thread's worker id (`rok_tls_worker_id`), the `ThreadId`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_thread_id() -> u64 {
    // SAFETY: this thread's own slot.
    unsafe { tls::worker_id().read() }
}

/// Block the calling thread for `ns` nanoseconds (negative = 0).
#[unsafe(no_mangle)]
pub extern "C" fn rok_thread_sleep_ns(ns: i64) {
    let mut ts = timespec(ns.max(0));
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
// This thread's task-executor worker (`rok::core::task`): a GC object
// held in `rok_tls_task_worker`, pinned while installed.
// ---------------------------------------------------------------------

/// 1 if this thread is an executor worker.
#[unsafe(no_mangle)]
pub extern "C" fn rok_task_worker_present() -> i32 {
    i32::from(rok_task_worker_get() != 0)
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_task_worker_get() -> usize {
    // SAFETY: this thread's own slot.
    unsafe { tls::task_worker().read() }
}

/// Install `w` (a live GC object, or 0 to clear) as this thread's
/// worker, releasing the previous one.
#[unsafe(no_mangle)]
pub extern "C" fn rok_task_worker_set(w: usize) {
    let old = rok_task_worker_get();
    // SAFETY: the slot only holds pinned, hence live, objects; the
    // caller passes a live object or 0.
    unsafe {
        if old != 0 {
            rokr_gc::unpin(old as *mut u8);
        }
        if w != 0 {
            rokr_gc::pin(w as *mut u8);
        }
        tls::task_worker().write(w);
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_task_worker_clear() {
    rok_task_worker_set(0);
}

// ---------------------------------------------------------------------
// Wait queue: futex semantics over a fixed table of pthread mutex /
// condvar buckets keyed by address. Spurious wakeups are allowed
// (callers re-check), so a bucket shared by unrelated words is fine.
// A waiter counts as stopped for the GC.
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

/// A word a thread can wait on.
pub trait Futex {
    fn value(&self) -> i32;
}

impl Futex for AtomicI32 {
    fn value(&self) -> i32 {
        self.load(Ordering::SeqCst)
    }
}

impl Futex for AtomicU8 {
    fn value(&self) -> i32 {
        i32::from(self.load(Ordering::SeqCst))
    }
}

#[allow(clippy::unnecessary_cast)] // `time_t` / `c_long` widths vary by target
const fn timespec(ns: i64) -> libc::timespec {
    libc::timespec {
        tv_sec: (ns / 1_000_000_000) as libc::time_t,
        tv_nsec: (ns % 1_000_000_000) as libc::c_long,
    }
}

/// Block while `w` holds `expected`, at most `timeout_ns` (< 0: no
/// limit); may return spuriously.
#[allow(clippy::unnecessary_cast)] // `time_t` / `c_long` widths vary by target
pub fn wait_on<W: Futex>(w: &W, expected: i32, timeout_ns: i64) {
    let b = bucket(ptr::from_ref(w) as usize);
    world::enter_native();
    // SAFETY: statically initialized pthread objects; valid timespecs.
    unsafe {
        libc::pthread_mutex_lock(b.lock.get());
        if w.value() == expected {
            if timeout_ns < 0 {
                libc::pthread_cond_wait(b.cond.get(), b.lock.get());
            } else {
                // `pthread_cond_timedwait` takes a CLOCK_REALTIME deadline.
                let mut now: libc::timespec = core::mem::zeroed();
                libc::clock_gettime(libc::CLOCK_REALTIME, &mut now);
                let at = timespec(
                    (now.tv_sec as i64)
                        .saturating_mul(1_000_000_000)
                        .saturating_add(now.tv_nsec as i64)
                        .saturating_add(timeout_ns),
                );
                libc::pthread_cond_timedwait(b.cond.get(), b.lock.get(), &at);
            }
        }
        libc::pthread_mutex_unlock(b.lock.get());
    }
    world::leave_native();
}

/// Wake every thread blocked in [`wait_on`] on `w`.
pub fn wake<W: Futex>(w: &W) {
    let b = bucket(ptr::from_ref(w) as usize);
    // SAFETY: statically initialized pthread objects.
    unsafe {
        libc::pthread_mutex_lock(b.lock.get());
        libc::pthread_cond_broadcast(b.cond.get());
        libc::pthread_mutex_unlock(b.lock.get());
    }
}

/// Element `index` of the `GcBuf<i32>` `buf`.
#[allow(clippy::cast_ptr_alignment)] // i32 buffer elements are 4-aligned
fn word(buf: *mut u8, index: usize) -> &'static AtomicI32 {
    // SAFETY: the caller's frame roots `buf`, so it is alive and stays in
    // place while this thread waits; element `index` is inside it.
    unsafe { &*buf.add(HEADER_SIZE + index * 4).cast::<AtomicI32>() }
}

/// Block while element `index` of the `GcBuf<i32>` `buf` equals
/// `expected`, at most `timeout_ns` (< 0: no limit), or until woken;
/// may return spuriously.
#[unsafe(no_mangle)]
pub extern "C" fn rok_sync_wait(buf: *mut u8, index: usize, expected: i32, timeout_ns: i64) {
    wait_on(word(buf, index), expected, timeout_ns);
}

/// Wake every thread blocked in `rok_sync_wait` on that element.
#[unsafe(no_mangle)]
pub extern "C" fn rok_sync_wake(buf: *mut u8, index: usize) {
    wake(word(buf, index));
}

// ---------------------------------------------------------------------
// Lazily initialized statics: compiled code checks the state byte
// (0 new, 1 running, 2 ready) and calls these around the initializer.
// ---------------------------------------------------------------------

/// This thread's running initializers, innermost first: a malloc'd
/// list behind a pthread key (no limit on nesting or concurrency).
struct Initializing {
    state: usize,
    next: *mut Initializing,
}

/// The pthread key holding each thread's `Initializing` list head.
fn init_key() -> libc::pthread_key_t {
    static KEY: AtomicUsize = AtomicUsize::new(usize::MAX);
    let k = KEY.load(Ordering::Acquire);
    if k != usize::MAX {
        return k as libc::pthread_key_t;
    }
    let mut new: libc::pthread_key_t = 0;
    // SAFETY: valid out-pointer; no destructor (a thread exits with an
    // empty list: every `begin` that pushed is matched by an `end`).
    if unsafe { libc::pthread_key_create(&mut new, None) } != 0 {
        rokr_common::fatal(b"rok runtime: pthread_key_create failed");
    }
    match KEY.compare_exchange(
        usize::MAX,
        new as usize,
        Ordering::AcqRel,
        Ordering::Acquire,
    ) {
        Ok(_) => new,
        Err(won) => {
            // SAFETY: our unused key.
            unsafe { libc::pthread_key_delete(new) };
            won as libc::pthread_key_t
        }
    }
}

fn initializing_head() -> *mut Initializing {
    // SAFETY: a key from `init_key`.
    unsafe { libc::pthread_getspecific(init_key()) }.cast()
}

fn set_initializing_head(head: *mut Initializing) {
    // SAFETY: a key from `init_key`.
    unsafe { libc::pthread_setspecific(init_key(), head.cast()) };
}

/// 1: the caller runs the initializer, then calls
/// [`rok_static_init_end`]. 0: it is ready (another thread may have
/// just finished it while this one waited). An initializer that reads
/// its own static panics (refs-lang 5.3).
#[unsafe(no_mangle)]
pub extern "C" fn rok_static_init_begin(state: *const AtomicU8) -> i32 {
    // SAFETY: compiled code passes its static's state byte.
    let s = unsafe { &*state };
    if s.compare_exchange(0, 1, Ordering::Acquire, Ordering::Acquire)
        .is_ok()
    {
        // SAFETY: malloc of one node, freed in `rok_static_init_end`.
        let node = unsafe { libc::malloc(size_of::<Initializing>()) }.cast::<Initializing>();
        if node.is_null() {
            rokr_common::oom();
        }
        // SAFETY: fresh node.
        unsafe {
            node.write(Initializing {
                state: state as usize,
                next: initializing_head(),
            });
        }
        set_initializing_head(node);
        return 1;
    }
    if s.load(Ordering::Acquire) != 2 {
        let mut n = initializing_head();
        let mut mine = false;
        while !n.is_null() {
            // SAFETY: nodes of this thread's list.
            unsafe {
                mine |= (*n).state == state as usize;
                n = (*n).next;
            }
        }
        if mine {
            let msg = b"static initializer reads its own static (recursive initialization)";
            // SAFETY: valid message.
            unsafe { crate::rok_panic(msg.as_ptr(), msg.len()) };
        }
        while s.load(Ordering::Acquire) != 2 {
            wait_on(s, 1, -1);
        }
    }
    0
}

/// The initializer stored the value: publish it.
#[unsafe(no_mangle)]
pub extern "C" fn rok_static_init_end(state: *const AtomicU8) {
    // Unlink this static's node (the innermost one, as initializers nest).
    let mut link: *mut *mut Initializing = ptr::null_mut();
    let mut n = initializing_head();
    while !n.is_null() {
        // SAFETY: nodes of this thread's list.
        unsafe {
            if (*n).state == state as usize {
                if link.is_null() {
                    set_initializing_head((*n).next);
                } else {
                    *link = (*n).next;
                }
                libc::free(n.cast());
                break;
            }
            link = &raw mut (*n).next;
            n = (*n).next;
        }
    }
    // SAFETY: as above.
    let s = unsafe { &*state };
    s.store(2, Ordering::Release);
    wake(s);
}

#[cfg(test)]
mod tests {
    use super::*;

    // 0 = uninitialized, 1 = running, 2 = ready (refs-lang 5.3).
    #[test]
    fn static_init_states_nest() {
        let outer = AtomicU8::new(0);
        let inner = AtomicU8::new(0);
        assert_eq!(rok_static_init_begin(&raw const outer), 1);
        assert_eq!(outer.load(Ordering::Relaxed), 1);
        // An initializer touching another static initializes it first.
        assert_eq!(rok_static_init_begin(&raw const inner), 1);
        rok_static_init_end(&raw const inner);
        assert_eq!(inner.load(Ordering::Relaxed), 2);
        rok_static_init_end(&raw const outer);
        assert_eq!(outer.load(Ordering::Relaxed), 2);
        // Ready statics are not re-run, and the per-thread list is empty.
        assert_eq!(rok_static_init_begin(&raw const outer), 0);
        assert!(initializing_head().is_null());
    }

    #[test]
    fn wait_times_out_and_wakes() {
        rokr_common::tls::thread_init();
        rokr_gc::world::attach_current();
        let w = AtomicI32::new(7);
        // A timed wait on an unchanged word returns after the timeout.
        wait_on(&w, 7, 1_000_000);
        // A wait on a word that differs returns at once.
        wait_on(&w, 0, -1);
        std::thread::scope(|s| {
            s.spawn(|| {
                std::thread::sleep(std::time::Duration::from_millis(5));
                w.store(8, Ordering::SeqCst);
                wake(&w);
            });
            while w.load(Ordering::SeqCst) == 7 {
                wait_on(&w, 7, -1);
            }
        });
    }
}
