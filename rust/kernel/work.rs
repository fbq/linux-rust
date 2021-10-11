// SPDX-License-Identifier: GPL-2.0

//! Wrappers for kernel work_struct and workqueue.
//!
//! This module allows Rust code to create a kernel work which can be submitted to a workqueue to
//! execute.
use crate::{bindings, c_types, str::CStr};

use crate::sync::NeedsLockClass;
use core::cell::UnsafeCell;
use core::ops::FnMut;
use core::pin::Pin;

/// Kernel work items.
///
/// Each [`Work`] represents a small task that can
///
#[repr(C)]
pub struct Work<T: Send> {
    head: UnsafeCell<bindings::work_struct>,
    data: T,
    _pin: core::marker::PhantomPinned, // Work is `!Unpin`
}

pub type WorkOfQueue<'a, T: Send> = Work<(&'a WorkQueue, T)>;

impl<T: Send> Work<T> {
    /// Creates a new `work_struct`.
    ///
    /// # Safety
    ///
    /// This function is marked as `unsafe` because `f` is an `extern "C"`
    /// function, which means `f` can be `unsafe`. The caller of this
    /// function must guarantee that function `f` is safe.
    unsafe fn new(f: unsafe extern "C" fn(*mut bindings::work_struct), data: T) -> Self {
        let mut w = Work {
            head: UnsafeCell::new(bindings::work_struct::default()),
            data,
            _pin: core::marker::PhantomPinned,
        };

        w.head.get_mut().func = Some(f);

        w
    }

    pub fn new_closure(f: T) -> Self
    where
        T: FnMut(),
    {
        unsafe { Work::new(bridge::<T>, f) }
    }

    /// Waits for a work to finish.
    ///
    /// Returns `false` if when the function got called, it found that the work is already at idle.
    /// Returns `true`
    pub fn flush(self: Pin<&Self>) -> bool {
        unsafe { bindings::flush_work(self.head.get()) }
    }

    pub fn cancel(self: Pin<&Self>) -> bool {
        unsafe { bindings::cancel_work_sync(self.head.get()) }
    }
}

impl<T: Send> NeedsLockClass for Work<T> {
    unsafe fn init(self: Pin<&mut Self>, name: &'static CStr, key: *mut bindings::lock_class_key) {
        unsafe {
            bindings::work_struct_init(self.head.get(), name.as_char_ptr(), key);
        }
    }
}

impl<T: Send> Drop for Work<T> {
    fn drop(&mut self) {
        unsafe {
            if !bindings::work_struct_is_uninit(self.head.get()) {
                bindings::cancel_work_sync(self.head.get());
            }
        }
    }
}

extern "C" fn bridge<F: FnMut()+ Send>(ptr: *mut bindings::work_struct) {
    let work = unsafe { &mut *(ptr as *mut Work<F>) };

    (work.data)();
}


pub struct WorkQueue {
    ptr: *mut bindings::workqueue_struct,
}

unsafe impl Sync for WorkQueue { }

pub fn system_wq() -> WorkQueue {
    WorkQueue {
        ptr: unsafe { bindings::system_wq },
    }
}

pub fn system_long_wq() -> WorkQueue {
    WorkQueue {
        ptr: unsafe { bindings::system_long_wq },
    }
}

pub struct WorkRef<'a, T: Send>(Pin<&'a mut Work<T>>, &'a WorkQueue);

impl<'a, T: Send> Drop for WorkRef<'a, T> {
    fn drop(&mut self) {
        self.0.as_ref().cancel();
    }
}

unsafe fn queue_work_on<T: Send>(wq: &WorkQueue, work: Pin<&Work<T>>, cpu: i32) -> bool {
    unsafe { bindings::queue_work_on(cpu, wq.ptr, work.head.get()) }
}

impl<'a, T: Send> WorkRef<'a, T> {
    pub fn queue(&self, cpu: i32) -> bool {
        unsafe {
            queue_work_on(self.1, self.0.as_ref(), cpu)
        }
    }

    pub fn flush(&self) -> bool {
        self.0.as_ref().flush()
    }

    pub fn cancel(&self) -> bool {
        self.0.as_ref().cancel()
    }
}

use core::future::Future;
use crate::sync::Ref;
use crate::error::Result;

impl WorkQueue {
    /// Queues a work on a particular CPU.
    ///
    ///
    pub fn queue_work_on<'a, T: Send>(
        &'a self,
        mut work: Pin<&'a mut Work<T>>,
        cpu: i32,
    ) -> Option<WorkRef<'a, T>> {
        if unsafe { queue_work_on(self, work.as_ref(), cpu) } {
            Some(WorkRef(work, self))
        } else {
            None
        }
    }

    pub fn bound<'a, T: Send>(
        &'a self,
        mut work: Pin<&'a mut Work<T>>,
    ) -> WorkRef<'a, T> {
        WorkRef(work, self)
    }

    pub fn try_new_future<'a, F: Future + Send>(
        &'a self,
        f: F
    ) -> Result<Pin<Ref<WorkOfQueue<'a, F>>>> {
        Ref::try_new(unsafe { Work::new(bridge_future::<F>, (self, f)) }).map(
            |r| { Ref::pinned(r) }
        )
    }
}

use core::task::*;

/*
static FUTUREWORK_VTALBE: RawWakerVTable = RawWakerVTable::new(
    clone,
    wake,
    wake_by_ref,
    drop,
);

unsafe fn clone(data: *const ()) -> RawWaker {
    RawWaker::new(data, &FUTUREWORK_VTALBE)
}

unsafe fn wake(data: *const ()) {
}
*/

extern "C" fn bridge_future<F: Future + Send>(ptr: *mut bindings::work_struct) {
    let mut work = unsafe { Ref::<WorkOfQueue<'_, F>>::from_raw(ptr as *mut _) };
    let wq = work.data.0;
    let future = unsafe { Pin::new_unchecked(&mut work.data.1) };

    // Why Future::poll need a Pin<&mut>???
}
