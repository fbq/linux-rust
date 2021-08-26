// SPDX-License-Identifier: GPL-2.0

//! CPUMask

use crate::bindings;
use crate::sync::{ReadGuard, ReadLock};

pub type CPUId = i32;
pub struct CPUIterator<'a> {
    curr: CPUId,
    mask: &'a bindings::cpumask,
}

impl<'a> CPUIterator<'a> {
    /// Creates a new [`CPUIterator`] starting at cpu `start`.
    fn new_start_at(start: CPUId, mask: &'a bindings::cpumask) -> Self {
        CPUIterator { curr: start, mask }
    }

    /// Creates a new [`CPUIterator`] starting at cpu `0`.
    fn new(mask: &'a bindings::cpumask) -> Self {
        Self::new_start_at(0, mask)
    }
}

impl<'a> Iterator for CPUIterator<'a> {
    type Item = CPUId;

    fn next(&mut self) -> Option<Self::Item> {
        let ret = self.curr;

        // SAFETY: `nr_cpu_ids` should stay stable (XXX: corner cases?).
        if ret < 0 || ret as u32 >= unsafe { bindings::nr_cpu_ids } {
            None
        } else {
            // SAFETY: We rely on the caller of [`CPUIterator::new`] provides
            // a valid pointer of `cpumask`.
            self.curr = unsafe { bindings::cpumask_next(ret, self.mask) as i32 };
            Some(ret)
        }
    }
}

pub fn possible_cpus<'a>() -> CPUIterator<'a> {
    // SAFETY: `__cpu_possible_mask` is fixed at the boot time. And we provide
    // a pointer to it which is valid.
    CPUIterator::new(unsafe { &bindings::__cpu_possible_mask })
}

pub struct CPUOnlineReadLock {}

extern "C" {
    static __cpu_online_mask: core::cell::UnsafeCell<bindings::cpumask>;
}

impl ReadLock for CPUOnlineReadLock {
    type Inner = bindings::cpumask;

    fn read_lock_noguard(&self) {
        unsafe {
            bindings::cpus_read_lock();
        }
    }

    unsafe fn read_unlock(&self) {
        unsafe {
            bindings::cpus_read_unlock();
        }
    }

    fn read_locked_data(&self) -> &core::cell::UnsafeCell<Self::Inner> {
        unsafe { &__cpu_online_mask }
    }
}

impl CPUOnlineReadLock {
    pub fn lock(&self) -> ReadGuard<'_, Self> {
        self.read_lock_noguard();
        unsafe { ReadGuard::new(self) }
    }
}

pub static cpus_read_lock: CPUOnlineReadLock = CPUOnlineReadLock {};

pub fn online_cpus<'a>(g: &'a ReadGuard<'_, CPUOnlineReadLock>) -> CPUIterator<'a> {
    // SAFETY: `__cpu_possible_mask` is fixed at the boot time. And we provide
    // a pointer to it which is valid.

    CPUIterator::new(unsafe { g })
}

use core::task::{Context, Waker, RawWaker, RawWakerVTable};
use core::future::Future;
use alloc::boxed::Box;
use alloc::sync::Arc;
use core::pin::Pin;
use crate::types::PointerWrapper;

fn create_wq_vtable() {
}

#[repr(C)]
pub struct FutureWork {
    work: bindings::work_struct,
    queue: *mut bindings::workqueue_struct,
    f: Box<dyn Future<Output=()>>,
}

/*
impl bindings::work_struct {
    pub fn new() -> Self {
    }
}
*/

unsafe extern "C" fn future_work_func(work: *mut bindings::work_struct) {
    // SAFETY: The caller must ensure `work` is a result of
    // `Arc<FutureWork>::into_pointer`.
    let future_work = unsafe { Pin::<Arc::<FutureWork>>::from_pointer(work as _) };
}

/*
unsafe fn queue_future_on<F>(cpu: i32, *mut binding::workqueue_struct, f: F)
where F: Future<Output=()>
{
}
*/
