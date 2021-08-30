// SPDX-License-Identifier: GPL-2.0

//! A generic lock guard and trait.
//!
//! This module contains a lock guard that can be used with any locking primitive that implements
//! the ([`Lock`]) trait. It also contains the definition of the trait, which can be leveraged by
//! other constructs to work on generic locking primitives.

/// Allows mutual exclusion primitives that implement the [`Lock`] trait to automatically unlock
/// when a guard goes out of scope. It also provides a safe and convenient way to access the data
/// protected by the lock.
#[must_use = "the lock unlocks immediately when the guard is unused"]
pub struct Guard<'a, L: Lock + ?Sized> {
    pub(crate) lock: &'a L,
    pub(crate) context: L::GuardContext,
}

// SAFETY: `Guard` is sync when the data protected by the lock is also sync. This is more
// conservative than the default compiler implementation; more details can be found on
// https://github.com/rust-lang/rust/issues/41622 -- it refers to `MutexGuard` from the standard
// library.
unsafe impl<L> Sync for Guard<'_, L>
where
    L: Lock + ?Sized,
    L::Inner: Sync,
{
}

impl<L: Lock + ?Sized> core::ops::Deref for Guard<'_, L> {
    type Target = L::Inner;

    fn deref(&self) -> &Self::Target {
        // SAFETY: The caller owns the lock, so it is safe to deref the protected data.
        unsafe { &*self.lock.locked_data().get() }
    }
}

impl<L: Lock + ?Sized> core::ops::DerefMut for Guard<'_, L> {
    fn deref_mut(&mut self) -> &mut L::Inner {
        // SAFETY: The caller owns the lock, so it is safe to deref the protected data.
        unsafe { &mut *self.lock.locked_data().get() }
    }
}

impl<L: Lock + ?Sized> Drop for Guard<'_, L> {
    fn drop(&mut self) {
        // SAFETY: The caller owns the lock, so it is safe to unlock it.
        unsafe { self.lock.unlock(&mut self.context) };
    }
}

impl<'a, L: Lock + ?Sized> Guard<'a, L> {
    /// Constructs a new lock guard.
    ///
    /// # Safety
    ///
    /// The caller must ensure that it owns the lock.
    pub(crate) unsafe fn new(lock: &'a L, context: L::GuardContext) -> Self {
        Self { lock, context }
    }
}

/// A generic mutual exclusion primitive.
///
/// [`Guard`] is written such that any mutual exclusion primitive that can implement this trait can
/// also benefit from having an automatic way to unlock itself.
pub trait Lock {
    /// The type of the data protected by the lock.
    type Inner: ?Sized;

    /// The type of context, if any, that needs to be stored in the guard.
    type GuardContext;

    /// Acquires the lock, making the caller its owner.
    fn lock_noguard(&self) -> Self::GuardContext;

    /// Releases the lock, giving up ownership of the lock.
    ///
    /// # Safety
    ///
    /// It must only be called by the current owner of the lock.
    unsafe fn unlock(&self, context: &mut Self::GuardContext);

    /// Returns the data protected by the lock.
    fn locked_data(&self) -> &core::cell::UnsafeCell<Self::Inner>;
}

/// Allows mutual exclusion primitives that implement the [`ReadLock`] trait to
/// automatically unlock when a guard goes out of scope. It also provides a
/// safe and convenient way to access the data protected by the lock.
#[must_use = "the lock unlocks immediately when the guard is unused"]
pub struct ReadGuard<'a, L: ReadLock + ?Sized> {
    pub(crate) lock: &'a L,
}

// SAFETY: `Guard` is sync when the data protected by the lock is also sync. This is more
// conservative than the default compiler implementation; more details can be found on
// https://github.com/rust-lang/rust/issues/41622 -- it refers to `MutexGuard` from the standard
// library.
unsafe impl<L> Sync for ReadGuard<'_, L>
where
    L: ReadLock + ?Sized,
    L::Inner: Sync,
{
}

impl<L: ReadLock + ?Sized> core::ops::Deref for ReadGuard<'_, L> {
    type Target = L::Inner;

    fn deref(&self) -> &Self::Target {
        // SAFETY: The caller owns the lock, so it is safe to deref the protected data.
        unsafe { &*self.lock.read_locked_data().get() }
    }
}

impl<L: ReadLock + ?Sized> Drop for ReadGuard<'_, L> {
    fn drop(&mut self) {
        // SAFETY: The caller owns the lock, so it is safe to unlock it.
        unsafe { self.lock.read_unlock() };
    }
}

pub trait ReadLock {
    /// The type of the data protected by the lock.
    type Inner;

    /// Acquires the lock, making the caller its owner.
    fn read_lock_noguard(&self);

    /// Releases the lock, giving up ownership of the lock.
    ///
    /// # Safety
    ///
    /// It must only be called by the current owner of the lock.
    unsafe fn read_unlock(&self);

    /// Returns the data protected by the lock.
    fn read_locked_data(&self) -> &core::cell::UnsafeCell<Self::Inner>;
}

impl<'a, L: ReadLock + ?Sized> ReadGuard<'a, L> {
    /// Constructs a new read lock guard.
    ///
    /// # Safety
    ///
    /// The caller must ensure that it owns the lock.
    pub(crate) unsafe fn new(lock: &'a L) -> Self {
        Self { lock }
    }
}

pub trait PreemptionDisable: Lock {}

pub trait IrqDisable: Lock {}

pub trait BHDisable: Lock {}
