//! Time and Timers
//!
//! This module allows Rust code to operate jiffy-based timestamps and timers.
//!
//! C header: [`include/linux/jiffies.h`](../../../../include/linux/jiffies.h)
use core::sync::atomic::{compiler_fence, AtomicUsize, Ordering};

pub mod timer;

/// The time unit of Linux kernel. One jiffy equals (1/HZ) second.
pub type Jiffies = core::ffi::c_ulong;

/// Gets the current jiffies counter.
pub fn jiffies_now() -> Jiffies {
    extern "C" {
        static jiffies: core::cell::UnsafeCell<Jiffies>;
    }

    compiler_fence(Ordering::SeqCst); // Enforces volatile.

    // SAFETY: For linux targets,`core::ffi::c_ulong` == `usize`, therefore it's safe to covert
    // the address of `jiffies` into a `*const AtomicUsize`.
    //
    // The atomic load is needed here because Linux kernel memory model assumes volatile reads and
    // writes on natural aligned words are atomic, while `read_volatile` of Rust doesn't provide
    // the same guarantee, so convert to atomic load to avoid data race. Besides since Rust atomic
    // is not volatile, compiler barriers are used to enforce the volatile semantics of load on
    // `jiffies`.
    let j = unsafe { &*(jiffies.get() as *const AtomicUsize) }.load(Ordering::Relaxed) as Jiffies;

    compiler_fence(Ordering::SeqCst); // Enforces volatile.

    j
}

/// Gets the current + `duration` jiffies.
pub fn jiffies_later(duration: Jiffies) -> Jiffies {
    jiffies_now().wrapping_add(duration)
}

/// Checks whether `t1` is before or equals to `t2`.
///
/// See `time_before_eq()` in the Linux header file.
pub fn before_or_equal(t1: Jiffies, t2: Jiffies) -> bool {
    t2.wrapping_sub(t1) as core::ffi::c_long >= 0
}

/// Checks whether `expires` has been expired.
pub fn jiffies_expired(expires: Jiffies) -> bool {
    before_or_equal(expires, jiffies_now())
}
