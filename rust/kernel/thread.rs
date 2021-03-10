// SPDX-License-Identifier: GPL-2.0

//! A kernel thread (kthread).
//!
//! This module allows Rust code to create/wakeup/stop a kernel thread.

use crate::c_types;
use crate::error::{from_kernel_err_ptr, Error, Result};
use crate::str::CStr;
use crate::{bindings, c_str};
use crate::task::{Task, TaskRef};
use crate::types::PointerWrapper;

use alloc::boxed::Box;
use core::ops::FnOnce;

/// Raw kernel threads.
///
/// The threads are created via C-style functions and machine-word sized
/// arguments.
///
/// # Safety
///
/// The creation of [`RawThread`] is unsafe because if a caller provides
/// an incorrect thread function or an incorrect thread argument, the
/// new thread will corrupt memory or do other unsafe behaviors.
pub struct RawThread {
    task: Task,
}

impl RawThread {
    /// Creates a new thread using a C-style function pointer.
    ///
    /// # Safety
    ///
    /// This function actually doesn't dereference `arg` or call `f`, so even if
    /// the users pass incorrect parameters this function won't run into
    /// trouble. But if the users provide incorrect `arg` or `f` the new
    /// thread will corrupt memory or do other unsafe behaviors, so
    /// make it `unsafe`.
    ///
    /// The safety requirements of calling this function are:
    ///
    /// - Make sure `arg` is a proper pointer that points to a valid memory
    ///   location when the new thread begins to run.
    ///
    /// - Make sure `f` is a proper function pointer and `f` handles `arg`
    ///   correctly.
    ///
    /// # Context
    ///
    /// This function might sleep in `kthread_create_on_node` due to the memory
    /// allocation and waiting for the completion, therefore do not call this
    /// in atomic contexts (i.e. preemption-off contexts).
    pub unsafe fn try_new(
        name: &CStr,
        f: unsafe extern "C" fn(*mut c_types::c_void) -> c_types::c_int,
        arg: *mut c_types::c_void,
    ) -> Result<Self> {
        let task_ptr;

        // SAFETY: `kthread_create_on_node` will copy the content of `name`,
        // so we don't need to make the `name` live longer.
        task_ptr = from_kernel_err_ptr(unsafe {
            bindings::kthread_create_on_node(
                Some(f),
                arg,
                bindings::NUMA_NO_NODE,
                c_str!("%s").as_ptr() as _,
                name.as_ptr(),
            )
        })?;

        // SAFETY: `task_ptr` is a valid pointer for a `task_struct` because
        // we've checked with `from_kernel_err_ptr` above.
        let task_ref = unsafe { TaskRef::from_ptr(task_ptr) };

        // Increases the refcount of the task, so that it won't go away if it
        // `do_exit`.
        Ok(RawThread { task: task_ref.clone() })
    }

    /// Wakes up the thread.
    ///
    /// Note that a newly created thread (via [`RawThread::try_new`]) will not
    /// run until a [`RawThread::wake_up`] is called.
    ///
    /// # Context
    ///
    /// This function might sleep, don't call it in atomic contexts.
    pub fn wake_up(&self) {
        // SAFETY: `task.ptr` is a valid pointer to a kernel thread structure,
        // the refcount of which is increased in [`RawThread::try_new`], so it
        // won't point to a freed `task_struct`. And it's not stopped because
        // [`RawThread::stop`] will consume the [`RawThread`].
        unsafe {
            bindings::wake_up_process(self.task.ptr);
        }
    }

    /// Stops the thread.
    ///
    /// - If the thread hasn't been waken up after creation, the thread function
    ///   won't be called, and this function will return `-EINTR`. Note that a
    ///   thread may not be waken up even after [`RawThread::wake_up`] is
    ///   called.
    ///
    /// - Otherwise, waits for the thread function to return or the thread
    ///   `do_exit` itself.
    ///
    /// Consumes the [`RawThread`] so that it's not accessible and return
    /// the exit code of the thread.
    ///
    /// # Context
    ///
    /// This function might sleep, don't call it in atomic contexts.
    pub fn stop(self) -> Result {
        // SAFETY: `task.ptr` is a valid pointer to a kernel thread structure,
        // the refcount of which is increased in `[RawThread::try_new`], so it
        // won't point to a freed `task_struct`. And it's not stopped because
        // `stop` will consume the [`RawThread`].
        let ret = unsafe { bindings::kthread_stop(self.task.ptr) };

        if ret == 0 {
            return Ok(());
        }
        Err(Error::from_kernel_errno(ret))
    }
}

/*
impl Drop for RawThread {
    fn drop(&mut self) {
        // Decreases the refcount of the thread, the thread may still be
        // running after we `drop` the [`RawThread`].
        //
        // SAFETY: At least one refcount is held by [`RawThread::try_new`] and
        // the refcount of `task_struct` is implemented by atomics.
        unsafe {
            rust_helper_put_task_struct(self.task);
        }
    }
}
*/

/// Helper trait to generate a C ABI bridge thread function.
///
/// An `impl` of this trait is passed as the second type parameter of
/// [`Thread::try_new`], and the new thread will call
/// [`ThreadFunctor::func`] if the creation succeeds.
pub trait ThreadFunctor<A: PointerWrapper + Send> {
    /// The thread function.
    fn func(arg: A) -> Result;
}

/// Bridge function from Rust ABI to C.
extern "C" fn bridge<A, F: ThreadFunctor<A>>(data: *mut c_types::c_void) -> i32
where
    A: PointerWrapper + Send,
{
    // SAFETY: `data` is the result of `A::into_pointer`, therefore it's safe
    // to `from_pointer` here.
    let arg = unsafe { A::from_pointer(data) };

    match F::func(arg) {
        Ok(_) => 0,
        Err(e) =>
        // Changes the return value if it's `-ENITR`, in other words, we
        // don't allow a thread function to return `-EINTR`.
        //
        // Rationale: the kernel uses `-EINTR` to indicate that the kernel
        // thread gets stopped before it's able to run (the exit code is
        // set at C side via a special call to `do_exit`). In that case,
        // there is no new thread to own the thread argument, therefore the
        // `stop` functions need to recycle the thread argument. If we allow
        // thread function to return `-EINTR`, `stop` will receive it as
        // the exit code, and we're unable to differ these two cases:
        // 1) stopped before run and 2) returning `-ENITR` from thread
        // function.
        //
        // Note that currently in kernel, no one actually calls `do_exit`
        // with `-EINTR` or returns `-EINTR` from therad function other
        // than the special case mentioned above.
        {
            if e.to_kernel_errno() == -(bindings::EINTR as i32) {
                -(bindings::EINVAL as i32)
            } else {
                e.to_kernel_errno()
            }
        }
    }
}

/// Helper struct for thread that just call its argument as a closure.
///
/// We use double boxing in the implementation, because 1) we need to make sure
/// the thread argument live longer enough for the new thread to use (box #1),
/// and 2) `dyn FnOnce()` is a fat pointer that doesn't fit in `*mut c_void`
/// (box #2).
struct ClosureCallFunctor;

/// Type alias for double boxed closures as thread arguments.
type ClosureArg = Box<Box<dyn FnOnce() -> Result + Send>>;

impl ThreadFunctor<ClosureArg> for ClosureCallFunctor {
    fn func(arg: ClosureArg) -> Result {
        // Just calls it.
        arg()
    }
}

/// A kernel thread handle.
pub struct Thread<A = ClosureArg>
where
    A: PointerWrapper + Send,
{
    /// Raw kernel thread.
    raw: RawThread,

    /// Pointer tor the thread argument.
    arg: *const c_types::c_void,

    /// Marker for the type of thread argument.
    ///
    /// We don't hold the thread argument in [`Thread], so use `*const A`.
    phantom: core::marker::PhantomData<*const A>,
}

impl<A> Thread<A>
where
    A: PointerWrapper + Send,
{
    /// Creates a new thread.
    ///
    /// To use this function, you need to provide a `ThreadFunctor<A>` type,
    /// as the generic type argument for the funciton.
    ///
    /// Note that we have constraint for `arg` as `'static`, this is because
    /// the new thread (which actually uses the `arg`) may outlive the caller
    /// of the function. The new thread may run until the end of the whole
    /// system, hence the `'static` lifetime.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc::boxed::Box;
    /// use core::fmt::Display;
    /// use kernel::thread::{Thread, ThreadFunctor};
    ///
    /// struct SimpleBoxFunc;
    ///
    /// impl<T> ThreadFunctor<Box<T>> for SimpleBoxFunc
    /// where
    ///     T: Send + Display,
    /// {
    ///     // `Box<T>` : [`PointerWrapper`] + [`Send`]
    ///     fn func(b: Box<T>) -> Result {
    ///         pr_info!("I got {}", b);
    ///     }
    /// }
    ///
    /// let boxed = Box::try_new(42)?;
    /// // let boxed: Box<[i32]> = Box::try_new([3, 4, 5])?; // Cannot use a DST as thread argument.
    /// // let doube_box = Box::try_new(boxed)?;             // Unless use double boxing
    ///
    /// let t = Thread::try_new::<SimpleBoxFunc>(c_str!("rust-thread"), boxed)?;
    ///
    /// t.wake_up();
    /// ```
    ///
    /// # Context
    ///
    /// This function might sleep in `kthread_create_on_node` due to the memory
    /// allocation and waiting for the completion, therefore do not call this
    /// in atomic contexts (i.e. preemption-off contexts).
    pub fn try_new<F: ThreadFunctor<A>>(name: &CStr, arg: A) -> Result<Self>
    where
        A: PointerWrapper + Send + 'static,
    {
        let data = arg.into_pointer();

        // SAFETY: `bridge::<A, F>` is a proper function pointer to a C
        // function, and [`PointerWrapper::from_pointer`] will be used in it to
        // consume the raw pointer in the new thread.
        let result = unsafe { RawThread::try_new(name, bridge::<A, F>, data as _) };

        if result.is_err() {
            // Creation fails, we need to consume the raw pointer `data` because
            // there is no new thread to own the underlying object, we should
            // let the current thread own it.
            //
            // SAFETY: We `from_pointer` back what we just `into_pointer`, and
            // since the new thread is not created, so no one touches `data`.
            unsafe {
                A::from_pointer(data);
            }
        }

        result.map(|raw| Thread {
            raw,
            arg: data,
            phantom: core::marker::PhantomData,
        })
    }

    /// Wakes up the thread.
    ///
    /// Note that a newly created thread (e.g. via [`Thread::try_new`]) will not
    /// run until a [`Thread::wake_up`] is called.
    ///
    /// # Context
    ///
    /// This function might sleep, don't call it in atomic contexts.
    pub fn wake_up(&self) {
        self.raw.wake_up()
    }

    /// Stops the thread.
    ///
    /// - If the thread hasn't been waken up after creation, the thread closure
    ///   won't be called, and will return `-EINTR`. Note that a thread may not
    ///   be waken up even after [`Thread::wake_up`] is called.
    ///
    /// - Otherwise, waits for the closure to return or the thread `do_exit`
    ///   itself.
    ///
    /// Consumes the [`Thread`] so that it's not accessible. In case of error,
    /// returns the exit code of the thread.
    ///
    /// # Context
    ///
    /// This function might sleep, don't call it in atomic contexts.
    pub fn stop(self) -> Result {
        let result = self.raw.stop();

        if let Err(e) = result {
            if e.to_kernel_errno() == -(bindings::EINTR as i32) {
                unsafe {
                    A::from_pointer(self.arg);
                }
            }

            return Err(e);
        }

        result
    }
}

/// Spawns a new thread with a closure (similar to [`std::thread::spawn`].
///
/// Note that we have `'static` lifetime constraint for the closure, this
/// is because the new thread may outlive the caller of the function, we
/// need to make sure that any value that the closure captures is valid
/// until the thread exits, and the thread may run until the end of the
/// whole system, hence the `'static` lifetime.
///
/// # Memory Cost
///
/// The implementation of this function currently needs to allocate extra
/// dynamic memory (using [`Box`]), and do double boxing because
/// `Box<dyn FnOnce()>`. These "drawbacks" similarly exist in the
/// implementation of [`std::thread::spawn`]. Only use this when these
/// are acceptable, otherwise try [`Thread::try_new`].
///
/// # Examples
///
/// ```
/// use alloc::boxed::Box;
/// use kernel::thread;
///
/// let mut a = 1;
/// let boxed_slice: Box<[i32]> = Box::try_new([1, 3, 4, 5])?; // Closures can capture DSTs.
///
/// let t = thread::spawn(c_str!("rust-thread"), move || {
///     let b = Box::try_new(42)?;
///
///     for _ in 0..10 {
///         a = a + 1;
///         pr_info!("Hello Rust Thread {}", a + b.as_ref());
///     }
///
///     pr_info!("A Box<[i32]>: ");
///     for i in boxed_slice.iter() {
///         pr_cont!("{} ", i);
///     }
///     pr_info!("");
///     Ok(())
/// })?;
///
/// t.wake_up();
/// ```
///
/// # Context
///
/// This function might sleep in `kthread_create_on_node` due to the memory
/// allocation and waiting for the completion, therefore do not call this
/// in atomic contexts (i.e. preemption-off contexts).
///
/// [`std::thread::spawn`]: https://doc.rust-lang.org/std/thread/fn.spawn.html
pub fn spawn<F>(name: &CStr, f: F) -> Result<Thread>
where
    F: FnOnce() -> Result,
    F: Send + 'static,
{
    // Allocate closure here, because this function maybe returns before
    // the bridged function (the function that uses the closure) get executed.
    let boxed_fn: Box<dyn FnOnce() -> Result + Send> = Box::try_new(f)?;

    // Double boxing here because `dyn FnOnce` is a fat pointer, and we cannot
    // `into_pointer` it to `*mut c_void`, see comments of `ClosureCallFunctor`
    // for more.
    let double_box = Box::try_new(boxed_fn)?;

    Thread::try_new::<ClosureCallFunctor>(name, double_box)
}

/// Tries to give up the CPU and lets another thread run.
///
/// This maps to kernel's `schedule` function, which is similar to
/// [`std::thread::yield_now`].
///
/// # Context
///
/// This function might sleep, don't call in atomic contexts.
///
/// [`std::thread::yield_now`]: https://doc.rust-lang.org/std/thread/fn.yield_now.html
#[doc(alias = "yield_now")]
pub fn schedule() {
    // SAFETY: If we can schedule back from other thread, then this can be
    // treated as a no-op. A special case occurs when a thread sets its state to
    // `TASK_DEAD`, and then `schedule` will not come. Currently we don't have a
    // way to do this safely in Rust, and in the future, we probably still won't
    // allow it.
    unsafe {
        bindings::schedule();
    }
}
