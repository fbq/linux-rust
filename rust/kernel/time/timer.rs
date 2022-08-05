//! Timers
//!
//! This module allows Rust code to use the coarse-gained kernel timers (jiffies based).
//!
//! C header: [`include/linux/timer.h`](../../../../include/linux/timer.h)

use alloc::boxed::Box;

use core::{
    marker::PhantomPinned,
    ops::Deref,
    pin::Pin,
    sync::atomic::{AtomicBool, Ordering},
};

use crate::{
    bindings::timer_list, c_str, container_of, pr_err, str::CStr, sync::LockClassKey, Opaque,
    Result,
};

use super::*;

/// A raw timer.
///
/// A direct mapping to [`timer_list`].
pub struct RawTimer {
    opaque: Opaque<timer_list>,

    /// [`RawTimer`] is !Unpin, since [`timer_list`] contains self-referential pointers.
    _p: PhantomPinned,
}

impl RawTimer {
    /// Creates a [`RawTimer`].
    ///
    /// # Safety
    ///
    /// The caller must call [`RawTimer::init`] before using the timer.
    unsafe fn new() -> Self {
        RawTimer {
            opaque: Opaque::uninit(),
            _p: PhantomPinned,
        }
    }

    /// Initialises a [`RawTimer`].
    ///
    /// # Safety
    ///
    /// The caller must ensure `func` is a safe function.
    unsafe fn init(
        self: Pin<&mut Self>,
        func: unsafe extern "C" fn(arg1: *mut timer_list),
        flags: u32,
        name: &'static CStr,
        key: &'static LockClassKey,
    ) {
        // SAFTEFY: `pin.opaque.get()` is a valid pointer to a [`timer_list`], and `func` is a
        // safe function per the safety guarantee of this function.
        // safe function.
        unsafe {
            bindings::init_timer_key(
                self.opaque.get(),
                Some(func),
                flags,
                name.as_char_ptr(),
                key.get(),
            );
        }
    }

    /// Schedules a timer.
    ///
    /// Interior mutability is provided by `mod_timer()`. It's safe to call even inside a timer
    /// callback.
    pub fn schedule(&self, expires: Jiffies) {
        // SAFETY: `self.opaque.get()` is a valid pointer to a [`timer_list`] and it's already
        // initialized per the safe guarantee of [`RawTimer::new`].
        unsafe {
            bindings::mod_timer(self.opaque.get(), expires);
        }
    }

    /// Cancels a scheduled timer.
    ///
    /// Callers should guarantee that the timer will eventually stop re-schedule itself, otherwise
    /// it's not guaranteed that this function will return.
    ///
    /// This function will wait until the timer callback finishes.
    pub fn cancel(&self) -> bool {
        // SAFETY: `self.opaque.get()` is a valid pointer to a [`timer_list`] and it's already
        // initialized per the safe guarantee of `init`.
        (unsafe { bindings::del_timer_sync(self.opaque.get()) }) != 0
    }
}

// SAFETY: A `timer_list` can be transferred between threads.
unsafe impl Send for RawTimer {}

/// Initializes a timer.
///
/// It automatically defines a new lockdep lock for the timer.
#[macro_export]
macro_rules! timer_init {
    ($timer:expr, $flags:expr, $name:expr) => {{
        static CLASS: $crate::sync::LockClassKey = $crate::sync::LockClassKey::new();

        $timer.init($flags, $crate::c_str!($name), &CLASS);
    }};
}

/// A timer.
///
/// # Safety
///
/// A [`Timer`] must first be initialized with a call to [`Timer::init`]
///
/// # Examples
///
/// ```
/// # use kernel::Timer;
///
pub struct Timer<F>
where
    F: Sync,
    F: FnMut() -> Result,
{
    head: RawTimer,

    /// The timer callback.
    callback: F,
}

impl<F> Timer<F>
where
    F: Sync,
    F: FnMut() -> Result,
{
    /// Creates a [`Timer`].
    ///
    /// # Safety
    ///
    /// The caller must call [`Timer::init`] before using the timer.
    pub unsafe fn new(f: F) -> Self {
        Timer {
            // SAFTEFY: Guaranteed by safety requirement of [`Timer::new`].
            head: unsafe { RawTimer::new() },
            callback: f,
        }
    }

    /// Initialises a [`Timer`].
    pub fn init(self: Pin<&mut Self>, flags: u32, name: &'static CStr, key: &'static LockClassKey) {
        // SAFETY: `pin_head` is only used to initialize, it won't be moved.
        let pin_head = unsafe { self.map_unchecked_mut(|p| &mut p.head) };

        // SAFETY: [`Self::bridge`] is a safe function per "SAFETY:" comments in it.
        unsafe { pin_head.init(Self::bridge, flags, name, key) };
    }

    unsafe extern "C" fn bridge(ptr: *mut bindings::timer_list) {
        // SAFETY: Kernel's timer framework guarantees that `ptr` is the address of the `head` for
        // a [`Timer`], therefore `container_of!` gives the correct address of the [`Timer`], and
        // since `drop` of [`Timer`] waits for this timer function to finish, the pointer is valid.
        let timer = unsafe { &mut *(container_of!(ptr, Timer::<F>, head) as *mut Timer<F>) };

        if let Err(err) = (timer.callback)() {
            pr_err!(
                "timer function failed with {}",
                err.name().unwrap_or(c_str!("Unknown"))
            );
        }
    }
}

impl<F> Deref for Timer<F>
where
    F: Sync,
    F: FnMut() -> Result,
{
    type Target = RawTimer;

    fn deref(&self) -> &Self::Target {
        &self.head
    }
}

impl<F> Drop for Timer<F>
where
    F: Sync,
    F: FnMut() -> Result,
{
    fn drop(&mut self) {
        // Since [`Timer`] won't re-schedule itself, then [`RawTimer::cancel`] guarantees to wait
        // until the timer function finishes, so it's safe to drop the callback in [`Timer`].
        self.cancel();
    }
}

/// Next action of repeatable timers.
pub enum Next {
    /// No more next step.
    Done,
    /// Schedules a timer to trigger later.
    Again(Jiffies),
}

/// A timer that may reschedule itself.
pub struct LongTimer<F>
where
    F: Sync,
    F: FnMut() -> Result<Next>,
{
    head: RawTimer,

    /// Marks the stop state of the repeatable timer.
    stop: AtomicBool,

    /// The timer callback.
    callback: F,
}

impl<F> LongTimer<F>
where
    F: Sync,
    F: FnMut() -> Result<Next>,
{
    /// Creates a [`Timer`].
    ///
    /// # Safety
    ///
    /// The caller must call [`LongTimer::init`] before using the timer.
    pub unsafe fn new(f: F) -> Self {
        LongTimer {
            // SAFTEFY: Guaranteed by safety requirement of [`LongTimer::new`].
            head: unsafe { RawTimer::new() },
            callback: f,
            stop: AtomicBool::new(false),
        }
    }

    /// Initialises a [`Timer`].
    pub fn init(self: Pin<&mut Self>, flags: u32, name: &'static CStr, key: &'static LockClassKey) {
        // SAFETY: `pin_head` is only used to initialize, it won't be moved.
        let pin_head = unsafe { self.map_unchecked_mut(|p| &mut p.head) };

        // SAFETY: [`Self::bridge`] is a safe function per "SAFETY:" comments in it.
        unsafe { pin_head.init(Self::bridge, flags, name, key) };
    }

    extern "C" fn bridge(ptr: *mut bindings::timer_list) {
        // SAFETY: Kernel's timer framework guarantees that `ptr` is the address of the `head` for
        // a [`LongTimer`], therefore `container_of!` gives the correct address of the
        // [`LongTimer`], and since `drop` of [`LongTimer`] waits for this timer function to finish,
        // the pointer is valid.
        let timer =
            unsafe { &mut *(container_of!(ptr, LongTimer::<F>, head) as *mut LongTimer<F>) };

        // Skips if the stop state is marked.
        if timer.stop.load(Ordering::Relaxed) {
            return;
        }

        let next = (timer.callback)();

        match next {
            Ok(Next::Again(duration)) => {
                timer.schedule(jiffies_later(duration));
            }
            Err(err) => {
                pr_err!(
                    "timer function failed with {}",
                    err.name().unwrap_or(c_str!("Unknown"))
                );
            }
            _ => {}
        }
    }
}

impl<F> Drop for LongTimer<F>
where
    F: Sync,
    F: FnMut() -> Result<Next>,
{
    fn drop(&mut self) {
        // By setting `self.stop` to true, the timer will eventually stop re-scheduling itself.
        // Therefore [`RawTimer::cancel`] will be guaranteed to return once the timer is no longer
        // running or pending.
        self.stop.store(true, Ordering::Relaxed);
        self.cancel();
    }
}

impl<F> Deref for LongTimer<F>
where
    F: Sync,
    F: FnMut() -> Result<Next>,
{
    type Target = RawTimer;

    fn deref(&self) -> &Self::Target {
        &self.head
    }
}

use crate::spinlock_init;
use crate::sync::{Ref, SpinLock, UniqueRef};
use core::future::Future;
use core::task::{Context, Poll, Waker};

/// A delay [`Future`].
pub struct Delay {
    expires: Jiffies,
    scheduled: bool,
    waker: Ref<SpinLock<Option<Waker>>>,
    timer: Timer<Box<dyn FnMut() -> Result + Sync + Send>>,
}

impl Delay {
    /// Creates a [`Delay`].
    pub fn try_new(duration: Jiffies) -> Result<Self> {
        // SAFETY: The [`SpinLock`] will get initialized later.
        let mut waker = Pin::from(UniqueRef::try_new(unsafe { SpinLock::new(None) })?);

        spinlock_init!(waker.as_mut(), "Delay");

        let waker: Ref<_> = waker.into();

        let waker_timer = waker.clone();

        Ok(Delay {
            expires: jiffies_later(duration),
            scheduled: false,
            waker,
            // SAFETY: `timer` will be initialized the first time [`Delay`] gets `poll`ed.
            timer: unsafe {
                Timer::new(Box::try_new(move || {
                    if let Some(waker) = waker_timer.lock_irqdisable().take() {
                        waker.wake();
                    }

                    Ok(())
                })?)
            },
        })
    }
}

impl Future for Delay {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let expires = self.as_ref().expires;

        if jiffies_expired(expires) {
            Poll::Ready(())
        } else {
            let waker = cx.waker().clone();

            let old_waker = self.as_ref().waker.lock_irqdisable().replace(waker);

            if self.as_ref().scheduled {
                // A timer is already scheduled. Only the timer will `take` the `waker`,
                // so we know the timer is running (or has run) if `waker` is `None`.
                if old_waker.is_none() {
                    Poll::Ready(())
                } else {
                    Poll::Pending
                }
            } else {
                // Need to schedule the timer.

                // Set the `scheduled` first.
                // SAFETY: Only modifies the `scheduled`, won't move it.
                *(unsafe { self.as_mut().map_unchecked_mut(|d| &mut d.scheduled) }.get_mut()) =
                    true;

                timer_init!(
                    // SAFETY: Only initializes the `Timer`, won't move it.
                    unsafe { self.as_mut().map_unchecked_mut(|d| { &mut d.timer }) },
                    0,
                    "delay future"
                );

                if jiffies_expired(expires) {
                    // Checks again.
                    Poll::Ready(())
                } else {
                    self.as_ref().timer.schedule(expires);
                    Poll::Pending
                }
            }
        }
    }
}
