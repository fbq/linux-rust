// SPDX-License-Identifier: GPL-2.0

//! Self test cases for Rust.

use kernel::prelude::*;
// Keep the `use` for a test in its test function. Module-level `use`s are only for the test
// framework.

module! {
    type: RustSelftests,
    name: b"rust_selftests",
    author: b"Rust for Linux Contributors",
    description: b"Self test cases for Rust",
    license: b"GPL",
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

/// An example of test.
#[allow(dead_code)]
fn test_example() -> Result<TestSummary> {
    // `use` declarations for the test can be put here, e.g. `use foo::bar;`.

    // Always pass.
    Ok(Pass)
}

fn test_timer() -> Result<TestSummary> {
    use kernel::time::{
        jiffies_later, jiffies_now,
        timer::{LongTimer, Next, Timer},
    };
    use kernel::timer_init;

    use core::sync::atomic::{AtomicBool, Ordering};

    let a = AtomicBool::new(false);

    let mut timer1 = unsafe {
        Timer::new(|| {
            pr_info!("Oneshot timer");
            a.store(true, Ordering::Release);
            Ok(())
        })
    };

    let mut counter = 0;
    let mut timer2 = unsafe {
        LongTimer::new(|| {
            pr_info!("long timer {}", counter);
            counter += 1;
            if counter == 10 {
                Ok(Next::Done)
            } else {
                Ok(Next::Again(10))
            }
        })
    };

    let mut heart_beat = 0;
    let mut timer_ref = Pin::from(Box::try_new(unsafe {
        LongTimer::new(move || {
            pr_info!("heart beat {} times", heart_beat);
            heart_beat += 1;
            Ok(Next::Again(10))
        })
    })?);

    timer_init!(unsafe { Pin::new_unchecked(&mut timer1) }, 0, "Oneshot");
    timer_init!(unsafe { Pin::new_unchecked(&mut timer2) }, 0, "Long");
    timer_init!(timer_ref.as_mut(), 0, "Boxed");

    pr_info!("schedule a timer\n");
    timer1.schedule(jiffies_later(1000));
    timer2.schedule(jiffies_now());
    timer_ref.schedule(jiffies_now());

    while !a.load(Ordering::Acquire) {
        core::hint::spin_loop();
    }

    Ok(Pass)
}

fn test_delay() -> Result<TestSummary> {
    use kernel::kasync::executor::workqueue::Executor;
    use kernel::spawn_task;
    use kernel::time::{jiffies_now, timer::Delay};
    use kernel::workqueue;

    let handle = Executor::try_new(workqueue::system())?;
    spawn_task!(handle.executor(), async move {
        pr_info!("Start delay {}\n", jiffies_now());
        Delay::try_new(1000).unwrap().await;
        pr_info!("After delay {}\n", jiffies_now());
    })?;

    handle.detach();

    Ok(Pass)
}

impl kernel::Module for RustSelftests {
    fn init(_name: &'static CStr, _module: &'static ThisModule) -> Result<Self> {
        pr_info!("Rust self tests (init)\n");

        do_tests! {
            test_timer,
            test_delay
        };

        Ok(RustSelftests)
    }
}

impl Drop for RustSelftests {
    fn drop(&mut self) {
        pr_info!("Rust self tests (exit)\n");
    }
}
