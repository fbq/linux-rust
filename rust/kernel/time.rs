// SPDX-License-Identifier: GPL-2.0

//! Timekeeping functions.
//!
//! C header: [`include/linux/ktime.h`](../../../../include/linux/ktime.h)
//! C header: [`include/linux/timekeeping.h`](../../../../include/linux/timekeeping.h)

use crate::bindings;
use core::marker::PhantomData;
// Re-exports [`Duration`], so that it's easy to provide kernel's own implemention in the future.
pub use core::time::Duration;

/// Provides a `now` function to get the current timestamp.
pub trait TimeNow: Sized + Copy {
    /// Returns the current timestamp.
    fn now() -> Instant<Self>;
}

/// A timestamp of monotonic clocks.
#[derive(Clone, Copy)]
pub struct Instant<T: TimeNow> {
    ns: u64,
    _type: PhantomData<T>,
}

impl<T: TimeNow> Instant<T> {
    fn new(ns: u64) -> Instant<T> {
        Instant {
            ns,
            _type: PhantomData,
        }
    }

    /// Returns the duration since this timestamp.
    pub fn elasped(&self) -> Duration {
        let now = T::now();

        Duration::from_nanos(now.ns.saturating_sub(self.ns))
    }

    /// Returns the duration from another timestamp to this one.
    pub fn duration_since(&self, earlier: Self) -> Duration {
        Duration::from_nanos(self.ns.saturating_sub(earlier.ns))
    }
}

/// CLOCK_MONOTONIC.
#[derive(Clone, Copy)]
pub struct ClockMonotonic;

impl TimeNow for ClockMonotonic {
    fn now() -> Instant<Self> {
        // SAFETY: `ktime_get()` is always safe to call.
        Instant::<Self>::new(unsafe { bindings::ktime_get() }.try_into().unwrap())
    }
}

/// CLOCK_BOOTTIME.
#[derive(Clone, Copy)]
pub struct ClockBoottime;

impl TimeNow for ClockBoottime {
    fn now() -> Instant<Self> {
        Instant::<Self>::new(
            // SAFETY: `ktime_get_with_offset()` is always safe to call.
            unsafe { bindings::ktime_get_with_offset(bindings::tk_offsets_TK_OFFS_BOOT) }
                .try_into()
                .unwrap(),
        )
    }
}
