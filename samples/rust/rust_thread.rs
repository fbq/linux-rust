// SPDX-License-Identifier: GPL-2.0

//! Rust thread APIs sample

#![no_std]
#![feature(allocator_api, global_asm)]

use alloc::boxed::Box;
use alloc::sync::Arc;
use core::fmt::Display;
use core::sync::atomic::{AtomicBool, Ordering};
use kernel::prelude::*;
use kernel::{
    c_str, pr_cont,
    thread::{schedule, spawn, Thread, ThreadFunctor},
};

module! {
    type: RustThread,
    name: b"rust_thread",
    author: b"Rust for Linux Contributors",
    description: b"Rust thread APIs sample",
    license: b"GPL v2",
    params: {
    },
}

struct RustThread;

impl KernelModule for RustThread {
    fn init() -> Result<Self> {
        pr_info!("Rust thread APIs sample (init)");

        // Test threads (using `try_new` for a `ThreadFunctor<Box<T>>`).
        {
            let boxed_i = Box::try_new(42)?;
            let boxed_str = Box::try_new("hello")?;

            struct SimpleBoxFunctor;

            impl<T> ThreadFunctor<Box<T>> for SimpleBoxFunctor
            where
                T: Send + Display,
            {
                fn func(arg: Box<T>) -> Result {
                    pr_info!("I got {}", arg);
                    Ok(())
                }
            }

            let t1 = Thread::try_new::<SimpleBoxFunctor>(c_str!("rust-boxed_i"), boxed_i)?;

            t1.wake_up();

            let t2 = Thread::try_new::<SimpleBoxFunctor>(c_str!("rust-boxed_str"), boxed_str)?;

            t2.wake_up();
        }

        // Test threads (using `try_new` for a `ThreadFunctor<i32>`).
        {
            struct I32Functor;

            impl ThreadFunctor<i32> for I32Functor {
                fn func(arg: i32) -> Result {
                    pr_info!("I got i32 {}", arg);
                    Ok(())
                }
            }

            let t1 = Thread::try_new::<I32Functor>(c_str!("rust-i32"), 43)?;

            t1.wake_up();
        }

        // Test threads.
        {
            let mut a = 1;
            // FIXME: use a completion or a barrier.
            let flag = Arc::try_new(AtomicBool::new(false))?;
            let other = flag.clone();
            let boxed_slice: Box<[i32]> = Box::try_new([1, 3, 4, 5])?;

            let t1 = spawn(c_str!("rust-closure"), move || {
                other.store(true, Ordering::Release);
                let b = Box::try_new(42)?;
                for _ in 0..20 {
                    a += 1;
                    pr_info!("Hello Rust Thread {}", a + b.as_ref());
                }
                pr_info!("A Box<[i32]>: ");
                for i in boxed_slice.iter() {
                    pr_cont!("{} ", i);
                }
                pr_info!("");

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

            let t1 = spawn(c_str!("rust-closure"), move || {
                let b = Box::try_new(42)?;
                for _ in 0..20 {
                    a += 1;
                    pr_info!("Hello Rust Thread {}", a + b.as_ref());
                }

                Ok(())
            })?;

            // Without `wake_up`, `stop` will cause the thread to exits with `-EINTR`.
            t1.stop().expect_err("Rust thread should exit abnormally");
        }

        Ok(RustThread)
    }
}

impl Drop for RustThread {
    fn drop(&mut self) {
        pr_info!("Rust thread APIs sample (exit)");
    }
}
