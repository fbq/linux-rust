// SPDX-License-Identifier: GPL-2.0

//! Rust workqueue APIs sample

#![no_std]
#![feature(allocator_api, global_asm)]

use alloc::boxed::Box;
use core::pin::Pin;
use core::sync::atomic::{AtomicUsize, Ordering};
use kernel::prelude::*;
use kernel::{
    init_with_lockdep, pr_info,
    work::{system_long_wq, system_wq, Work},
};

module! {
    type: RustWork,
    name: b"rust_work",
    author: b"Rust for Linux Contributors",
    description: b"Rust workqueue APIs sample",
    license: b"GPL v2",
    params: {
    },
}

struct RustWork;

impl KernelModule for RustWork {
    fn init() -> Result<Self> {
        pr_info!("Rust workqueue APIs sample (init)");

        // Test workqueue.
        {
            let a = AtomicUsize::new(0);

            let hello_work = Box::<Work<_>>::try_new(Work::new_closure(|| {
                pr_info!("hello, work {}", a.fetch_add(1, Ordering::Relaxed));
            }))
            .unwrap();

            let mut hello_work2 = Work::new_closure(|| {
                pr_info!("hello, work {}", a.fetch_add(1, Ordering::Relaxed));
            });

            let mut p = Pin::from(hello_work);
            let mut p2 = unsafe { Pin::new_unchecked(&mut hello_work2) };

            init_with_lockdep!(p.as_mut(), "simple work");
            init_with_lockdep!(p2.as_mut(), "simple work");

            let wq = system_wq();
            let c = wq.bound(p.as_mut());

            for i in 0..10 {
                pr_info!("queue {} time", i);
                wq.queue_work_on(p2.as_mut(), 1).unwrap();
                c.queue(0);

                if i % 2 == 0 {
                    c.flush();
                } else {
                    c.cancel();
                }
            }
            pr_info!("queue last work");
            //system_wq().queue_work_on(p.as_ref(), 0);

            pr_info!("value at last {}", a.load(Ordering::Relaxed));
        }

        // scary stories
        /*
        {
            let mut a = 0;

            let mut work = Work::new_closure(|| {

                for i in 0..100000 {
                    let b = unsafe { core::ptr::read_volatile(&mut a as *mut _) };
                    kernel::thread::schedule();
                    unsafe {
                        core::ptr::write_volatile(&mut a as *mut _, b + 1);
                    }
                }

                pr_info!("a is {}", a);
            });

            let mut p = unsafe { Pin::new_unchecked(&mut work) };

            init_with_lockdep!(p.as_mut(), "work");

            system_long_wq().queue_work_on(p.as_ref(), 2i32);

            while !system_wq().queue_work_on(p.as_ref(), 1i32) { }
            pr_info!("second work queued");

            p.as_ref().flush();
        }
        */

        Ok(RustWork)
    }
}

impl Drop for RustWork {
    fn drop(&mut self) {
        pr_info!("Rust workqueue APIs sample (exit)");
    }
}
