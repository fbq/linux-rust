// SPDX-License-Identifier: GPL-2.0

//! Per-CPU data handling.

use crate::bindings;

/// A handle to alloc/access/free percpu variables.
pub struct PerCPU<T> {
    ptr: *const T,
}

impl<T> PerCPU<T> {
    fn try_new(data: T) -> KernelResult<PerCPU>
    where
        T: Copy,
    {
        let size = core::mem::sizeof::<T>();

        let ptr = bindings::__alloc_percpu(size, size) as *const T;
    }
}
