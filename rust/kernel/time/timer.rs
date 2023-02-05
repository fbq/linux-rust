//! Timers
//!
//! This module allows Rust code to use the coarse-gained kernel timers (jiffies based).
//!
//! C header: [`include/linux/timer.h`](../../../../include/linux/timer.h)

use core::{marker::PhantomPinned, pin::Pin};

use crate::container_of;
use crate::{bindings::timer_list, prelude::*, str::CStr, sync::LockClassKey, types::Opaque};

use super::*;

/// A raw timer.
#[repr(transparent)]
pub struct RawTimer {
    opaque: Opaque<timer_list>,

    /// [`RawTimer`] is `!Unpin`, since [`timer_list`] contains self-referential pointers.
    _p: PhantomPinned,
}

/// Timeout trait.
///
/// # Safety
///
/// This trait is unsafe because this trait implies there is a [`RawTimer`] inside the struct,
/// and if it's armed, it may be called at any time and may access the struct. Therefore the `drop`
/// function of an `impl Timeout` needs to make sure the [`RawTimer`] is shutdown before freeing
/// other members, otherwise it's UAF.
pub unsafe trait Timeout: Sized {
    /// Called with time is up.
    ///
    /// # Safety
    ///
    /// This can only be called inside [`RawTimer::bridge`], otherwise there may be a data race.
    ///
    /// # Implementation
    ///
    /// * `timeout` can only access the outer type.
    /// * `timeout` cannot operate on the [`RawTimer`].
    /// * `timeout` should be locally safe.
    unsafe fn timeout(_: *mut RawTimer) -> Result<Next>;

    /// Gets the pinned reference to the inner [`RawTimer`].
    fn raw_timer(self: Pin<&Self>) -> Pin<&RawTimer>;

    /// Initialises the [`RawTimer`] inside.
    ///
    /// XXX: this probably goes way with pin-init.
    fn init_timer(self: Pin<&Self>, flags: u32, name: &'static CStr, key: &'static LockClassKey) {
        self.raw_timer().init::<Self>(flags, name, key);
    }
}

impl RawTimer {
    /// Creates a [`RawTimer`].
    ///
    /// # Safety
    ///
    /// The caller must call [`RawTimer::init`] before using the timer.
    pub unsafe fn new() -> Self {
        RawTimer {
            opaque: Opaque::uninit(),
            _p: PhantomPinned,
        }
    }

    extern "C" fn bridge<T: Timeout>(ptr: *mut bindings::timer_list) {
        let ptr = ptr.cast::<RawTimer>();

        // SAFETY: Inside [`Timer::bridge`], it's safe.
        let next = unsafe { T::timeout(ptr) };

        // SAFTEFY: See the `expire_timers` function at C side, `ptr` points to this very same
        // [`RawTimer`] object (transparent to a `timer_list`), therefore `ptr` is valid.
        let timer = unsafe { &*ptr };

        match next {
            Ok(Next::Again(duration)) => {
                timer.schedule_at(jiffies_later(duration));
            }
            Err(_err) => {
                todo!("need Error::name()");
            }
            _ => {}
        }
    }

    /// Initialises a [`RawTimer`].
    fn init<T: Timeout>(
        self: Pin<&Self>,
        flags: u32,
        name: &'static CStr,
        key: &'static LockClassKey,
    ) {
        // SAFTEFY: `self.opaque.get()` is a valid pointer to a [`timer_list`], and
        // `Self::bridge::<T>` is a safe function.
        unsafe {
            bindings::init_timer_key(
                self.opaque.get(),
                Some(Self::bridge::<T>),
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
    pub fn schedule_at(&self, expires: Jiffies) {
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
    /// This function will wait until the timer callback finishes. Return `true` is the timer was
    /// pending and got deactivated.
    pub fn cancel(&self) -> bool {
        // SAFETY: `self.opaque.get()` is a valid pointer to a [`timer_list`] and it's already
        // initialized per the safe guarantee of `init`.
        (unsafe { bindings::timer_delete_sync(self.opaque.get()) }) != 0
    }

    /// Shutdowns a scheduled timer.
    ///
    /// This function will wait until the timer callback finishes, and also make any future
    /// schedule of the timer no-ops.
    pub fn shutdown(&self) {
        // SAFETY: `self.opaque.get()` is a valid pointer to a [`timer_list`] and it's already
        // initialized per the safe guarantee of `init`.
        unsafe {
            bindings::timer_shutdown_sync(self.opaque.get());
        }
    }
}

impl Drop for RawTimer {
    fn drop(&mut self) {
        self.shutdown();
    }
}

// SAFETY: A `timer_list` can be transferred between threads.
unsafe impl Send for RawTimer {}

/// Next action of the timer.
pub enum Next {
    /// No more next step.
    Done,
    /// Schedules a timer to trigger later.
    Again(Jiffies),
}

/// A simple closure timer.
pub struct FnTimer<F>
where
    F: Sync, // SYNC: `F` may be called on other CPU.
    F: FnMut() -> Result<Next>,
{
    raw: RawTimer,
    f: F,
}

impl<F> FnTimer<F>
where
    F: Sync,
    F: FnMut() -> Result<Next>,
{
    /// Creates a [`FnTimer`].
    ///
    /// # Safety
    ///
    /// The caller must call [`FnTimer::init_timer`] before using the timer.
    pub unsafe fn new(f: F) -> Self {
        Self {
            // SAFTEFY: Guaranteed by safety requirement of [`FnTimer::new`].
            raw: unsafe { RawTimer::new() },
            f,
        }
    }
}

// SAFETY: [`FnTimer::drop`] shutdown the [`RawTimer`] first.
unsafe impl<F> Timeout for FnTimer<F>
where
    F: Sync,
    F: FnMut() -> Result<Next>,
{
    fn raw_timer(self: Pin<&Self>) -> Pin<&RawTimer> {
        // SAFETY: `self` is pinned, therefore its field should always be pinned.
        unsafe { self.map_unchecked(|f| &f.raw) }
    }

    unsafe fn timeout(ptr: *mut RawTimer) -> Result<Next> {
        let obj = container_of!(ptr, Self, raw) as *mut Self;

        // IPML & SAFETY: Per safety guarantee of `timeout`, it's only called inside a timer bridge
        // function, and `ptr` is a pointer to [`Self::raw`], therefore `obj` is a vaild pointer
        // to [`Self`]. [`FnTimer`] is pinned before `init_timer`, so no risk of being moved. No
        // other way to access [`FnTimer::f`], so no data race. And [`FnTimer::drop`] needs to wait
        // for the ongoing timer to finish, so no UAF. Hence it safe to dereference as mut here.
        unsafe { ((*obj).f)() }
    }
}

impl<F> Drop for FnTimer<F>
where
    F: Sync,
    F: FnMut() -> Result<Next>,
{
    fn drop(&mut self) {
        // SAFETY: `self` is going to drop, no one will move `self`.
        let pin = unsafe { Pin::new_unchecked(&*self) };

        pin.raw_timer().shutdown();
    }
}
