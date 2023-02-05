// SPDX-License-Identifier: GPL-2.0

use crate::{bindings, types::Opaque};

/// Represents a lockdep class. It's a wrapper around C's `lock_class_key`.
#[repr(transparent)]
pub struct LockClassKey(Opaque<bindings::lock_class_key>);

// SAFETY: This is a wrapper around a lock class key, so it is safe to use references to it from
// any thread.
unsafe impl Sync for LockClassKey {}

impl LockClassKey {
    /// Creates a new lock class key.
    pub const fn new() -> Self {
        Self(Opaque::uninit())
    }

    #[allow(dead_code)]
    pub(crate) fn get(&self) -> *mut bindings::lock_class_key {
        self.0.get().cast()
    }
}
