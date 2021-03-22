// SPDX-License-Identifier: GPL-2.0

//! A kernel thread (kthread).
//!
//! This module allows Rust code to create/wakup/stop a kernel thread.

use crate::c_types;
use crate::error::{ptr_to_result, Error, KernelResult};
use crate::{bindings, cstr, CStr};

use alloc::boxed::Box;
use core::ops::FnOnce;

extern "C" {
    #[allow(improper_ctypes)]
    fn rust_helper_get_task_struct(task: *mut bindings::task_struct);
    #[allow(improper_ctypes)]
    fn rust_helper_put_task_struct(task: *mut bindings::task_struct);
}

fn call_as_closure(closure: Box<Box<dyn FnOnce() -> KernelResult<()>>>) -> KernelResult<()> {
    closure()
}

/// Generates a bridge function from Rust to C ABI.
///
/// `func` should be a `fn(arg: arg_type) -> KernelResult<()>` where arg_type
/// is the same size as `*mut c_types::c_void` ([`core::intrinsics::transmute`]
/// checks that at the compile time.
#[macro_export]
macro_rules! bridge {
    ($func:expr) => {{
        unsafe extern "C" fn _func(data: *mut $crate::c_types::c_void) -> $crate::c_types::c_int {
            let arg = core::intrinsics::transmute(data);
            let f: fn(_) -> _ = $func; // Makes sure `$func` is a function pointer

            match f(arg) {
                Ok(()) => 0,
                Err(e) => e.to_kernel_errno(),
            }
        }

        _func
    }};
}

/// Creates a new thread without extra memory allocation.
///
/// This macro tasks a Rust function pointer `$func` and an argument `$arg`,
/// and creates a thread doing `$func($arg)`, the return value of $func is
/// [`KernelError<()>`].
///
/// # Examples
///
/// ```
/// use kernel::thread::{schedule, Thread};
/// use kernel::thread_try_new;
/// use alloc::sync::Arc;
/// use core::sync::atomic::{AtomicUsize, Ordering};
///
/// let arc = Arc::try_new(AtomicUsize::new(0))?;
///
/// let t = thread_try_new!(
///   cstr!("rust-thread"),
///   |x: Arc<AtomicUsize>| -> KernelResult<()> {
///     for _ in 0..10 {
///         x.fetch_add(1, Ordering::Release);
///         println!("x is {}", x.load(Ordering::Relaxed));
///     }
///     Ok(())
///   },
///   arc.clone()
/// )?;
///
/// t.wake_up();
///
/// while arc.load(Ordering::Acquire) != 10 {
///     schedule();
/// }
///
/// println!("main thread: x is {}", arc.load(Ordering::Relaxed));
/// ```
///
/// # Context
///
/// This macro might sleep due to the memory allocation and waiting for
/// the completion in `kthread_create_on_node`. Therefore do not call this
/// in atomic contexts (i.e. preemption-off contexts).
#[macro_export]
macro_rules! thread_try_new {
    ($name:expr, $func:expr, $arg:expr) => {{
        // In case of failure, we need to `transmute` the `$arg` back, `_arg` is
        // used here to inference the type of `$arg`, so that the `transmute`
        // in the failure path knows the type.
        let mut _arg = $arg;

        // TYPE CHECK: `$arg` should be the same as `*mut c_void`, and
        // `transmute` only works if two types are of the same size.
        //
        // SAFETY: In the bridge funciton, the `$arg` is `transmute` back.
        let data = unsafe { core::intrinsics::transmute(_arg) };

        // SAFTEY: a) the bridge function is a valid function pointer, and b)
        // the bridge function `transmute` back what we just `transmute`.
        let result =
            unsafe { $crate::thread::Thread::try_new_c_style($name, $crate::bridge!($func), data) };

        if let Err(e) = result {
            // Creation fails, we need to `transmute` back the `$arg` because
            // there is no new thread to own it, we should let the current
            // thread own it.
            //
            // SAFETY: We `transmute` back waht we just `transmute`, and since
            // the new thread is not created, so no one touches `data`.
            unsafe {
                _arg = core::intrinsics::transmute(data);
            }

            // Uses an unused closure to check whether `$arg` is `Send`.
            let _ = move || { _arg };

            Err(e)
        } else {
            result
        }
    }};
}

/*
pub trait ThreadArg<A: Send> {
    fn from_raw(ptr: *mut c_types::c_void) -> A;
    fn into_raw(arg: A) -> *mut c_types::c_void;
}
pub trait ThreadFunc<A: Send> {
    fn func(arg: A) -> KernelResult<()>;
}

extern "C" fn bridge<A, T: ThreadFunc<A>>(data: *mut c_types::c_void) -> i32
where A : Send
{
    let arg = unsafe { core::intrinsics::transmute(data) };
    
    match T::func(arg) {
        Ok(_) => 0,
        Err(e) => e.to_kernel_errno(),
    }
}
*/

/// Function passed to `kthread_create_on_node` as the thread function pointer.
#[no_mangle]
unsafe extern "C" fn rust_thread_func(data: *mut c_types::c_void) -> c_types::c_int {
    // `Box::from_raw()` to get the ownership of the closure.
    let c = Box::from_raw(data as *mut Box<dyn FnOnce() -> KernelResult<()>>);

    match c() {
        Ok(_) => 0,
        Err(e) => e.to_kernel_errno(),
    }
}

/// A kernel thread handle.
pub struct Thread {
    /// Pointer to the kernel thread.
    task: *mut bindings::task_struct,
}

impl Thread {
    /// Creates a new thread using a C-style function pointer.
    ///
    /// No extra memory allocation for thread creation. Use this when closure
    /// allocation overhead is unacceptable or there is already a C style
    /// thread function. Otherwise, please consider using [`Thread::try_new`].
    ///
    /// # Safety
    ///
    /// This function actually doesn't dereference `arg` or call `f`, so even if
    /// the users pass incorrect parameters this function won't run into
    /// trouble. But if the users provide incorrect `arg` or `f` the new
    /// thread will corrupt memory or do other unsafe behaviors, so
    /// make it `unsafe`. Otherwise, it is [`Thread::wake_up`] that should be
    /// made as `unsafe` because it will trigger the call of the unsafe function
    /// `f`, this is undesirable given that [`Thread::wake_up`] on a
    /// [`Thread::try_new`] created thread is safe.
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
    /// This function might sleep due to the memory allocation and waiting for
    /// completion in `kthread_create_on_node`. Therefore cannot call this
    /// in atomic contexts (i.e. preemption-off contexts).
    pub unsafe fn try_new_c_style(
        name: CStr,
        f: unsafe extern "C" fn(*mut c_types::c_void) -> c_types::c_int,
        arg: *mut c_types::c_void,
    ) -> KernelResult<Self> {
        let task;

        // SAFETY: `kthread_create_on_node` will copy the content of `name`,
        // so we don't need to make the `name` live longer.
        task = ptr_to_result(bindings::kthread_create_on_node(
            Some(f),
            arg,
            bindings::NUMA_NO_NODE,
            cstr!("%s").as_ptr() as _,
            name.as_ptr(),
        ))?;

        // Increases the refcount of the task, so that it won't go away if it `do_exit`.
        //
        // SAFETY: `task` is a proper pointer pointing to a newly created thread.
        rust_helper_get_task_struct(task);

        Ok(Thread { task })
    }

    /*
    pub fn try_new_thread_func<A, T: ThreadFunc<A>>(name: CStr, arg: A) -> KernelResult<Self>
    where A: Send
    {
        let data = unsafe { core::intrinsics::transmute(arg) };

        let result = unsafe { Self::try_new_c_style(name, bridge::<A,T>, data) };

        if let Err(e) = result {
            // Creation fails, we need to `transmute` back the `arg` because
            // there is no new thread to own it, we should let the current
            // thread own it.
            //
            // SAFETY: We `transmute` back waht we just `transmute`, and since
            // the new thread is not created, so no one touches `data`.
            unsafe {
                core::intrinsics::transmute::<_, A>(data);
            }

            Err(e)
        } else {
            result
        }

    }
    */

    /// Creates a new thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use kernel::thread::Thread;
    /// use alloc::boxed::Box;
    ///
    /// let mut a = 1;
    ///
    /// let t = Thread::try_new(
    ///   cstr!("rust-thread"),
    ///   move || {
    ///     let b = Box::try_new(42)?;
    ///
    ///     for _ in 0..10 {
    ///         a = a + 1;
    ///         println!("Hello Rust Thread {}", a + b.as_ref());
    ///     }
    ///     Ok(())
    ///   }
    /// )?;
    ///
    /// t.wake_up();
    /// ```
    ///
    /// # Context
    ///
    /// This function might sleep due to the memory allocation and waiting for
    /// the completion in `kthread_create_on_node`. Therefore do not call this
    /// in atomic contexts (i.e. preemption-off contexts).
    pub fn try_new<F>(name: CStr, f: F) -> KernelResult<Self>
    where
        F: FnOnce() -> KernelResult<()>,
        F: Send + 'static,
    {
        // Allocate closure here, because this function maybe returns before
        // `rust_thread_func` (the function that uses the closure) get executed.
        let boxed_fn: Box<dyn FnOnce() -> KernelResult<()> + 'static> = Box::try_new(f)?;

        // Double boxing here because `dyn FnOnce` is a fat pointer, and we cannot
        // `transmute` it to `*mut c_void`.
        let double_box = Box::try_new(boxed_fn)?;

        thread_try_new!(name, call_as_closure, double_box)
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
        // SAFETY: `task` is a valid pointer to a kernel thread structure, the refcount
        // of which is increased in `try_new*`, so it won't point to a freed
        // `task_struct`. And it's not stopped because `stop` will consume the
        // [`Thread`].
        unsafe {
            bindings::wake_up_process(self.task);
        }
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
    pub fn stop(self) -> KernelResult<()> {
        // SAFETY: `task` is a valid pointer to a kernel thread structure, the
        // refcount of which is increased in `try_new*`, so it won't point to
        // a freed `task_struct`. And it's not stopped because `stop` will
        // consume the [`Thread`].
        let ret = unsafe { bindings::kthread_stop(self.task) };

        if ret == 0 {
            Ok(())
        } else {
            Err(Error::from_kernel_errno(ret))
        }
    }
}

impl Drop for Thread {
    fn drop(&mut self) {
        // Decreases the refcount of the thread, the thread may still be running after
        // we `drop` the `Thread`.
        //
        // SAFETY: At least one refcount is held by `Thread::try_new*` and
        // the refcount of `task_struct` is implemented by atomics.
        unsafe {
            rust_helper_put_task_struct(self.task);
        }
    }
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
    // SAFETY: ...
    // If we can schedule back from other thread, then this can be treated as a
    // no-op. A special case occurs when a thread sets its state to `TASK_DEAD`,
    // and then `schedule` will not come. Currently we don't have a way to do
    // this safely in Rust, and in the future, we probably still won't allow it.
    unsafe {
        bindings::schedule();
    }
}
