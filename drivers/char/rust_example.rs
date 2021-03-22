// SPDX-License-Identifier: GPL-2.0

//! Rust example module

#![no_std]
#![feature(allocator_api, global_asm)]
#![feature(test)]

use alloc::boxed::Box;
use alloc::sync::Arc;
use core::fmt::Debug;
use core::pin::Pin;
use core::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use kernel::prelude::*;
use kernel::{
    chrdev, condvar_init, cstr,
    file_operations::FileOperations,
    miscdev, mutex_init, spinlock_init,
    sync::{CondVar, Mutex, SpinLock},
    thread::{schedule, BoxArg, PrimitiveArg, Thread, ThreadFunc},
    thread_try_new,
};

module! {
    type: RustExample,
    name: b"rust_example",
    author: b"Rust for Linux Contributors",
    description: b"An example kernel module written in Rust",
    license: b"GPL v2",
    params: {
        my_bool: bool {
            default: true,
            permissions: 0,
            description: b"Example of bool",
        },
        my_i32: i32 {
            default: 42,
            permissions: 0o644,
            description: b"Example of i32",
        },
        my_str: str {
            default: b"default str val",
            permissions: 0o644,
            description: b"Example of a string param",
        },
        my_usize: usize {
            default: 42,
            permissions: 0o644,
            description: b"Example of usize",
        },
        my_array: ArrayParam<i32, 3> {
            default: [0, 1],
            permissions: 0,
            description: b"Example of array",
        },
    },
}

struct RustFile;

impl FileOperations for RustFile {
    type Wrapper = Box<Self>;

    kernel::declare_file_operations!();

    fn open() -> KernelResult<Self::Wrapper> {
        println!("rust file was opened!");
        Ok(Box::try_new(Self)?)
    }
}

struct RustExample {
    message: String,
    _chrdev: Pin<Box<chrdev::Registration<2>>>,
    _dev: Pin<Box<miscdev::Registration>>,
}

impl KernelModule for RustExample {
    fn init() -> KernelResult<Self> {
        println!("Rust Example (init)");
        println!("Am I built-in? {}", !cfg!(MODULE));
        {
            let lock = THIS_MODULE.kernel_param_lock();
            println!("Parameters:");
            println!("  my_bool:    {}", my_bool.read());
            println!("  my_i32:     {}", my_i32.read(&lock));
            println!(
                "  my_str:     {}",
                core::str::from_utf8(my_str.read(&lock))?
            );
            println!("  my_usize:   {}", my_usize.read(&lock));
            println!("  my_array:   {:?}", my_array.read());
        }

        // Test mutexes.
        {
            // SAFETY: `init` is called below.
            let data = Pin::from(Box::try_new(unsafe { Mutex::new(0) })?);
            mutex_init!(data.as_ref(), "RustExample::init::data1");
            *data.lock() = 10;
            println!("Value: {}", *data.lock());

            // SAFETY: `init` is called below.
            let cv = Pin::from(Box::try_new(unsafe { CondVar::new() })?);
            condvar_init!(cv.as_ref(), "RustExample::init::cv1");
            {
                let guard = data.lock();
                #[allow(clippy::while_immutable_condition)]
                while *guard != 10 {
                    cv.wait(&guard);
                }
            }
            cv.notify_one();
            cv.notify_all();
            cv.free_waiters();
        }

        // Test spinlocks.
        {
            // SAFETY: `init` is called below.
            let data = Pin::from(Box::try_new(unsafe { SpinLock::new(0) })?);
            spinlock_init!(data.as_ref(), "RustExample::init::data2");
            *data.lock() = 10;
            println!("Value: {}", *data.lock());

            // SAFETY: `init` is called below.
            let cv = Pin::from(Box::try_new(unsafe { CondVar::new() })?);
            condvar_init!(cv.as_ref(), "RustExample::init::cv2");
            {
                let guard = data.lock();
                #[allow(clippy::while_immutable_condition)]
                while *guard != 10 {
                    cv.wait(&guard);
                }
            }
            cv.notify_one();
            cv.notify_all();
            cv.free_waiters();
        }

        // Test threads.
        {
            let mut a = 1;
            // FIXME: use a completion or a barrier.
            let flag = Arc::try_new(AtomicBool::new(false))?;
            let other = flag.clone();

            let t1 = Thread::try_new(cstr!("rust-thread"), move || {
                other.store(true, Ordering::Release);
                let b = Box::try_new(42)?;
                for _ in 0..20 {
                    a += 1;
                    println!("Hello Rust Thread {}", a + b.as_ref());
                }

                Ok(())
            })?;

            t1.wake_up();

            // Waits to observe the thread run.
            while !flag.load(Ordering::Acquire) {
                schedule();
            }

            // `t1` should exit normally.
            t1.stop().expect("Rust thread should exit normally");
        }

        // Test threads (not up for running).
        {
            let mut a = 1;

            let t1 = Thread::try_new(cstr!("rust-thread"), move || {
                let b = Box::try_new(42)?;
                for _ in 0..20 {
                    a += 1;
                    println!("Hello Rust Thread {}", a + b.as_ref());
                }

                Ok(())
            })?;

            // Without `wake_up`, `stop` will cause the thread to exits with `-EINTR`.
            t1.stop().expect_err("Rust thread should exit abnormally");
        }

        // Test threads
        {
            let arc = Arc::try_new(AtomicUsize::new(0))?;

            let t1 = thread_try_new!(
                cstr!("rust-thread"),
                |x: Arc<AtomicUsize>| -> KernelResult<()> {
                    for _ in 0..10 {
                        x.fetch_add(1, Ordering::Release);
                        println!("x is {}", x.load(Ordering::Relaxed));
                    }
                    Ok(())
                },
                arc.clone()
            )?;

            t1.wake_up();

            // Waits to observe the thread run.
            while arc.load(Ordering::Acquire) != 10 {
                schedule();
            }

            println!("main thread: x is {}", arc.load(Ordering::Relaxed));

            // `t1` should exit normally.
            t1.stop().expect("Rust thread should exit abnormally");
        }

        // Test threads (create with ThreadFunc and BoxArg).
        {
            let b = Box::try_new(42)?;

            struct SimpleBoxFunc;

            impl<T> ThreadFunc<Box<T>> for SimpleBoxFunc
            where
                T: Debug + Send,
            {
                type Arg = BoxArg;
                fn func(arg: Box<T>) -> KernelResult<()> {
                    println!("I got {:?}", arg);
                    Ok(())
                }
            }

            let t1 = Thread::try_new_thread_func::<_, SimpleBoxFunc>(cstr!("rust-thread"), b)?;

            t1.wake_up();

            // Don't care the result value.
        }

        // Test threads (create with ThreadFunc and PrimitiveArg).
        {
            struct I32Func;

            impl ThreadFunc<i32> for I32Func {
                type Arg = PrimitiveArg;
                fn func(arg: i32) -> KernelResult<()> {
                    println!("I got i32 {}", arg);
                    Ok(())
                }
            }

            let t1 = Thread::try_new_thread_func::<_, I32Func>(cstr!("rust-thread"), 43)?;

            t1.wake_up();

            // Don't care the result value.
        }

        // Including this large variable on the stack will trigger
        // stack probing on the supported archs.
        // This will verify that stack probing does not lead to
        // any errors if we need to link `__rust_probestack`.
        let x: [u64; 514] = core::hint::black_box([5; 514]);
        println!("Large array has length: {}", x.len());

        let mut chrdev_reg =
            chrdev::Registration::new_pinned(cstr!("rust_chrdev"), 0, &THIS_MODULE)?;
        // Register the same kind of device twice, we're just demonstrating
        // that you can use multiple minors. There are two minors in this case
        // because its type is `chrdev::Registration<2>`
        chrdev_reg.as_mut().register::<RustFile>()?;
        chrdev_reg.as_mut().register::<RustFile>()?;

        Ok(RustExample {
            message: "on the heap!".to_owned(),
            _dev: miscdev::Registration::new_pinned::<RustFile>(cstr!("rust_miscdev"), None)?,
            _chrdev: chrdev_reg,
        })
    }
}

impl Drop for RustExample {
    fn drop(&mut self) {
        println!("My message is {}", self.message);
        println!("Rust Example (exit)");
    }
}
