// SPDX-License-Identifier: GPL-2.0

//! Self test cases for Rust.

use kernel::prelude::*;
// Keep the `use` for a test in its test function. Module-level `use`s are only for the test
// framework.

module! {
    type: RustSelftests,
    name: "rust_selftests",
    author: "Rust for Linux Contributors",
    description: "Self test cases for Rust",
    license: "GPL",
}

struct RustSelftests;

/// A summary of testing.
///
/// A test can
///
/// * pass (successfully), or
/// * fail (without hitting any error), or
/// * hit an error (interrupted).
///
/// This is the type that differentiates the first two (pass and fail) cases.
///
/// When a test hits an error, the test function should skip and return the error. Note that this
/// doesn't mean the test fails, for example if the system doesn't have enough memory for
/// testing, the test function may return an `Err(ENOMEM)` and skip.
#[allow(dead_code)]
enum TestSummary {
    Pass,
    Fail,
}

use TestSummary::Fail;
use TestSummary::Pass;

macro_rules! do_tests {
    ($($name:ident),*) => {
        let mut total = 0;
        let mut pass = 0;
        let mut fail = 0;

        $({
            total += 1;

            match $name() {
                Ok(Pass) => {
                    pass += 1;
                    pr_info!("{} passed!", stringify!($name));
                },
                Ok(Fail) => {
                    fail += 1;
                    pr_info!("{} failed!", stringify!($name));
                },
                Err(err) => {
                    pr_info!("{} hit error {:?}", stringify!($name), err);
                }
            }
        })*

        pr_info!("{} tests run, {} passed, {} failed, {} hit errors\n",
                 total, pass, fail, total - pass - fail);

        if total == pass {
            pr_info!("All tests passed. Congratulations!\n");
        }
    }
}

fn test_thread() -> Result<TestSummary> {
    use core::sync::atomic::{AtomicBool, Ordering};
    use kernel::sync::Arc;
    use kernel::thread::Thread;
    use kernel::time::{
        jiffies_later,
        timer::{FnTimer, Next, Timeout},
    };
    use kernel::{c_str, timer_init};

    // Tells whether the thread is already starting.
    let start = Arc::try_new(AtomicBool::new(false))?;
    let start_in_thread = start.clone();

    let t = Thread::try_new(c_str!("hello"), move || {
        start_in_thread.store(true, Ordering::Relaxed);

        let mut local = 0;
        let flag = AtomicBool::new(false);
        let t = unsafe {
            FnTimer::new(|| {
                local += 1;

                pr_info!("local is {local}");

                // Notifies the thread after 10 times
                if local == 10 {
                    flag.store(true, Ordering::Relaxed);
                }

                Ok(Next::Again(1000))
            })
        };

        let pt = unsafe { core::pin::Pin::new_unchecked(&t) };

        timer_init!(pt, 0, "rust timer");
        pt.raw_timer().schedule_at(jiffies_later(0));

        while !flag.load(Ordering::Relaxed) {
            kernel::thread::schedule();
        }

        Ok(())
    })?;

    t.task().wake_up();

    while !start.load(Ordering::Relaxed) {
        kernel::thread::schedule();
    }

    t.stop().map(|_| Pass)
}

impl kernel::Module for RustSelftests {
    fn init(_module: &'static ThisModule) -> Result<Self> {
        pr_info!("Rust self tests (init)\n");

        do_tests! {
            test_thread
        };

        Ok(RustSelftests)
    }
}

impl Drop for RustSelftests {
    fn drop(&mut self) {
        pr_info!("Rust self tests (exit)\n");
    }
}
