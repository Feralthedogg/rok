//! `rok_par_for` / `rok_par_scope` (805 §8.5.4): the C-level parallel
//! loop and scope. Work runs on OS threads that are registered mutators
//! (`rok_thread_spawn`), so the callbacks may allocate and collect; a
//! waiting caller counts as parked (`rok_thread_join`).
//!
//! ponytail: threads are spawned per call (tens of µs each) instead of
//! a persistent pool; `rok::core::par` uses the task executor's
//! work-stealing pool and does not come through here.

use core::mem::size_of;
use core::ptr;
use core::sync::atomic::{AtomicI64, AtomicU32, Ordering};

use rokr_common::fatal;

use crate::thread::{RokFn, rok_cpu_count, rok_thread_join, rok_thread_new_id, rok_thread_spawn};

struct ForJob {
    /// Next unclaimed iteration (index, not value).
    next: AtomicI64,
    count: i64,
    chunk: i64,
    start: i64,
    step: i64,
    cb: unsafe extern "C" fn(i64),
}

/// Run claimed chunks of `job` until none is left.
fn for_worker(job: &ForJob) {
    loop {
        let k = job.next.fetch_add(job.chunk, Ordering::Relaxed);
        if k >= job.count {
            return;
        }
        for j in k..job.count.min(k + job.chunk) {
            // SAFETY: the compiler passes a valid `extern "C" fn(i64)`;
            // `j < count` keeps `start + j * step` in range.
            unsafe { (job.cb)(job.start + j * job.step) };
        }
    }
}

#[allow(clippy::cast_ptr_alignment)] // `env` is a `&ForJob`
extern "C" fn for_thread(env: *mut u8) {
    // SAFETY: `env` is the caller's `ForJob`, alive until it joins us.
    for_worker(unsafe { &*env.cast::<ForJob>() });
}

/// Iterations of `start, start + step, ..` short of `end`.
const fn iterations(start: i64, end: i64, step: i64) -> i64 {
    let (span, step) = if step > 0 {
        (end as i128 - start as i128, step as i128)
    } else {
        (start as i128 - end as i128, -(step as i128))
    };
    if span <= 0 {
        0
    } else {
        ((span + step - 1) / step) as i64
    }
}

/// `par::for_each` desugar: `callback(i)` for `i` in `start..end` by
/// `step`, spread over the CPUs (order unspecified). `callback` is
/// `Ptr<u8>` in 805, i.e. nullable.
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
    let count = iterations(start, end, step);
    let threads = (rok_cpu_count() as i64).min(count).max(1);
    let job = ForJob {
        next: AtomicI64::new(0),
        count,
        // A few chunks per thread: balance without a claim per item.
        chunk: (count / (threads * 4)).max(1),
        start,
        step,
        cb,
    };
    let env = ptr::from_ref(&job).cast_mut().cast::<u8>();
    let mut handles = [0usize; 64];
    let helpers = (threads as usize - 1).min(handles.len());
    for h in handles.iter_mut().take(helpers) {
        *h = rok_thread_spawn(RokFn::new(for_thread, env), 0, rok_thread_new_id());
    }
    for_worker(&job);
    for &h in handles.iter().take(helpers).filter(|&&h| h != 0) {
        rok_thread_join(h);
    }
}

/// A `rok_par_scope` handle: the threads `rok_par_spawn` started.
pub struct Scope {
    lock: AtomicU32,
    handles: *mut usize,
    len: usize,
    cap: usize,
}

impl Scope {
    fn with<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        while self
            .lock
            .compare_exchange_weak(0, 1, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            core::hint::spin_loop();
        }
        let r = f(self);
        self.lock.store(0, Ordering::Release);
        r
    }
}

/// `par::scope` desugar: `callback(scope)`, then wait for every thread
/// spawned on `scope` (also those spawned by spawned threads).
#[unsafe(no_mangle)]
pub extern "C" fn rok_par_scope(callback: Option<unsafe extern "C" fn(*mut Scope)>) {
    let Some(cb) = callback else {
        fatal(b"rok_par_scope: null callback");
    };
    let mut scope = Scope {
        lock: AtomicU32::new(0),
        handles: ptr::null_mut(),
        len: 0,
        cap: 0,
    };
    // SAFETY: the compiler passes a valid `extern "C" fn(*mut u8)`.
    unsafe { cb(&raw mut scope) };
    loop {
        let next = scope.with(|s| {
            (s.len > 0).then(|| {
                s.len -= 1;
                // SAFETY: `len < cap` entries are initialized.
                unsafe { *s.handles.add(s.len) }
            })
        });
        let Some(h) = next else { break };
        rok_thread_join(h);
    }
    // SAFETY: our own buffer (or null).
    unsafe { libc::free(scope.handles.cast()) };
}

/// Run the rok closure `f` on its own thread inside `scope`; the scope
/// waits for it. (`par_scope`'s handle is not in 805: impl-defined.)
///
/// # Safety
/// `scope` is a handle `rok_par_scope` passed to its callback (or to a
/// thread spawned on it), still inside that call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_par_spawn(scope: *mut Scope, f: RokFn) {
    let h = rok_thread_spawn(f, 0, rok_thread_new_id());
    if h == 0 {
        fatal(b"rok_par_spawn: cannot start a thread");
    }
    // SAFETY: caller contract.
    unsafe { &mut *scope }.with(|s| {
        if s.len == s.cap {
            let cap = (s.cap * 2).max(8);
            // SAFETY: realloc of our own buffer (or null).
            let p = unsafe { libc::realloc(s.handles.cast(), cap * size_of::<usize>()) };
            if p.is_null() {
                rokr_common::oom();
            }
            s.handles = p.cast();
            s.cap = cap;
        }
        // SAFETY: `len < cap`.
        unsafe { *s.handles.add(s.len) = h };
        s.len += 1;
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::sync::atomic::AtomicUsize;

    static SUM: AtomicI64 = AtomicI64::new(0);
    static THREADS: AtomicUsize = AtomicUsize::new(0);
    extern "C" fn add(i: i64) {
        SUM.fetch_add(i, Ordering::Relaxed);
    }

    #[test]
    fn par_for_runs_every_iteration() {
        rokr_common::tls::thread_init();
        rokr_gc::world::attach_current();
        rok_par_for(0, 10, 3, Some(add)); // 0+3+6+9
        rok_par_for(10, 0, -4, Some(add)); // 10+6+2
        rok_par_for(0, 0, 1, Some(add));
        rok_par_for(1, 1001, 1, Some(add)); // 500500
        assert_eq!(SUM.load(Ordering::Relaxed), 36 + 500_500);
        assert_eq!(iterations(i64::MAX - 2, i64::MAX, 5), 1);
        assert_eq!(iterations(i64::MIN, i64::MAX, i64::MAX), 3);
        scope_spawns();
    }

    extern "C" fn count(_env: *mut u8) {
        THREADS.fetch_add(1, Ordering::Relaxed);
    }

    extern "C" fn body(s: *mut Scope) {
        for _ in 0..5 {
            // SAFETY: inside `rok_par_scope`.
            unsafe { rok_par_spawn(s, RokFn::new(count, ptr::null_mut())) };
        }
    }

    fn scope_spawns() {
        rok_par_scope(Some(body));
        assert_eq!(THREADS.load(Ordering::Relaxed), 5);
    }
}
