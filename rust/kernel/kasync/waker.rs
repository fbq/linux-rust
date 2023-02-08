// SPDX-License-Identifier: GPL-2.0

//! Kernel support for Waker

use core::{
    cell::UnsafeCell,
    ptr::addr_of,
    sync::atomic::{AtomicPtr, Ordering},
    task::{Waker, RawWaker, RawWakerVTable},
};

/// Synchronization for waker registering and taking.
pub struct AtomicWaker {
    data_ptr: AtomicPtr<()>,
    table: UnsafeCell<&'static RawWakerVTable>,
}

static TAKING_DATA: usize = 0;
static TAKEN_DATA: usize = 1;
static REGISTERING_DATA: usize = 2;

struct StateKeys {
    taking: *const (),
    taken: *const (),
    registering: *const (),
}

// Just use the address as keys.
unsafe impl Sync for StateKeys {}

static KEY: StateKeys = StateKeys {
    taking: addr_of!(TAKING_DATA) as _,
    taken: addr_of!(TAKEN_DATA) as _,
    registering: addr_of!(REGISTERING_DATA) as _,
};

fn not_a_waker(_: *const ()) {
    panic!("I am not a real waker");
}

fn not_a_waker_clone(_: *const()) -> RawWaker {
    panic!("I am not a real waker, don't clone");
}

static VTABLE: RawWakerVTable = RawWakerVTable::new(not_a_waker_clone, not_a_waker, not_a_waker, not_a_waker);

impl AtomicWaker {
    /// TODO
    pub fn new() -> Self {
        AtomicWaker {
            data_ptr: AtomicPtr::new(KEY.taken as _),
            table: UnsafeCell::new(&VTABLE),
        }
    }

    /// TODO
    pub fn take(&self) -> Option<Waker> {
        let old = self.data_ptr.swap(KEY.taking as _, Ordering::AcqRel) as *const ();

        // Hope not all `*const ()` are equal???
        let res = if old != KEY.taken && old != KEY.taking && old != KEY.registering {
            // We win the race
            Some(unsafe { Waker::from_raw(RawWaker::new(old, *self.table.get())) })
        } else {
            None
        };

        self.data_ptr.store(KEY.taken as _, Ordering::Release);

        res
    }

    /// TODO
    pub fn register(&self, waker: &Waker) -> bool {
        let old = self.data_ptr.swap(KEY.registering as _, Ordering::AcqRel) as *const ();

        // Hope not all `*const ()` are equal???
        if old != KEY.registering && old != KEY.taking {
            let waker = waker.clone();
            // We win the race
            if old != KEY.taken {
                // We have a old waker, need to drop it.
                unsafe { Waker::from_raw(RawWaker::new(old, *self.table.get())) };
            }

            unsafe { *self.table.get() = waker.as_raw().vtable(); }

            // Release the lock and set the Waker
            self.data_ptr.store(waker.as_raw().data() as _, Ordering::Release);

            false
        } else {
            // If we get `registering` that means multiple `register` calls, no guarantee, no need
            // to wake.
            //
            // Otherwse we get `taking`, that means Some one is taking an existing waker, we may
            // need to requeue the task. Also no need to worry about the `data_ptr`, since the
            // `take` caller will handle it.
            old != KEY.registering
        }
    }

    /// TODO
    pub fn wake(&self) {
        if let Some(w) = self.take() {
            w.wake();
        }
    }
}

/// TODO
unsafe impl Send for AtomicWaker { }
/// TODO
unsafe impl Sync for AtomicWaker { }

impl Drop for AtomicWaker {
    fn drop(&mut self) {
        self.take(); // Drop the waker if there is any.
    }
}

impl Default for AtomicWaker {
    fn default() -> Self {
        AtomicWaker::new()
    }
}
