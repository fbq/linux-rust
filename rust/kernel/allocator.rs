// SPDX-License-Identifier: GPL-2.0

//! Allocator support.

use core::alloc::{GlobalAlloc, Layout};

use crate::bindings;

struct KernelAllocator;

#[repr(transparent)]
struct AllocHeader(*const core::ffi::c_void);

const HEADER_SIZE: usize = core::mem::size_of::<AllocHeader>();

fn slab_minalign() -> usize {
    // SAFETY: Just querying the minimal alignment of SLAB, always safe to call.
    unsafe { bindings::arch_slab_minalign() as usize }
}

/// # Safety
///
/// Same as the requirement for [`Layout::from_size_align`]:
///
/// * `align` must be not zero,
/// * `align` must be a power of two,
/// * `size`, when rounded up to the nearest multiple of align, must not overflow isize (i.e., the
/// rounded value must be less than or equal to `isize::MAX`).
#[allow(dead_code)]
unsafe fn alloc(size: usize, align: usize, flags: bindings::gfp_t) -> *mut u8 {
    let min_align = slab_minalign();

    // Since `align` is always a power of two, optimize for cases when `size` <= `align`.
    let size = core::cmp::max(size, align);

    if size.is_power_of_two() || align <= min_align {
        // Case #1:
        //
        // `size` is 2^k or `align` <= `slab_minalign()`, slab provides the necessary alignment
        // guarantee.
        unsafe { bindings::krealloc(core::ptr::null_mut(), size, flags) as *mut u8 }
    } else {
        // Makes sure header accesses are aligned. In theory, this could increases the alignment
        // of the allocated objects, however, the minimal alignment of slab is usually the size of
        // a pointer (which is also the size of `AllocHeader`), so we have `align` >= `header_size`
        // here for most cases.
        let align = core::cmp::max(align, HEADER_SIZE);

        // Allocates (size + align + header_size - min_align) bytes, see below.
        let res = unsafe {
            bindings::krealloc(
                core::ptr::null_mut(),
                size + align + HEADER_SIZE - min_align,
                flags)};

        if res.is_null() {
            return res as *mut u8;
        }

        // Makes sure there is room for the header.
        let ptr_val = (res as usize).wrapping_add(HEADER_SIZE);

        // Set the `ptr` to `(ptr + align - min_align) & !(align-1)`, this is
        //
        // 1. aligned to `align`,
        // 2. <= `(ptr + align - min_align)`, which means enough room (>= `size`) for the object,
        let ptr_val = ptr_val.wrapping_add(align - min_align) & !(align.wrapping_sub(1));

        // `ptr_val` is aligned to `align` therefore aligned for [`AllocHeader`].
        let header_ptr = (ptr_val - HEADER_SIZE) as *mut AllocHeader;

        // Stores the real allocation address.
        //
        // SAFETY: `header_ptr` is properly aligned and points to the memory from the above
        // allocation.
        unsafe { (*header_ptr).0 = res; }

        return ptr_val as *mut u8;
    }
}

/// # Safety
///
/// * `ptr` must denote a block of memory allocated by `alloc`.
/// * `size` and `align` must be the same when `ptr` was allocated.
#[allow(dead_code)]
unsafe fn dealloc(ptr: *mut u8, size: usize, align: usize) {
    let min_align = slab_minalign();

    // Since `align` is always a power of two, optimize for cases when `size` <= `align`.
    let size = core::cmp::max(size, align);

    if size.is_power_of_two() || align <= min_align {
        // Case #1:
        //
        // `size` is 2^k or `align` <= `slab_minalign()`, slab provides the necessary alignment
        // guarantee.
        unsafe { bindings::kfree(ptr as *const core::ffi::c_void); }
    } else {
        if ptr.is_null() {
            return;
        }

        let header_ptr = (ptr as usize).wrapping_sub(HEADER_SIZE) as *mut AllocHeader;

        // SAFETY: Per the safety requirement of the function, `header_ptr` must be properly aligned
        // and points to the `AllocHeader`.
        let res = unsafe { (*header_ptr).0 };

        // SAFETY: Per the safety requirement of the function, the header was set up when `alloc` is
        // called, therefore `res` points to the whole memory block allocated by `krealloc`, so it's
        // safe to free it by `kfree`.
        unsafe { bindings::kfree(res); }
    }
}

unsafe impl GlobalAlloc for KernelAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe { bindings::krealloc(core::ptr::null(), layout.size(), bindings::GFP_KERNEL) as *mut u8 }
//        unsafe { alloc(layout.size(), layout.align(), bindings::GFP_KERNEL) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        unsafe {
            bindings::kfree(ptr as *const core::ffi::c_void);
           // dealloc(ptr, layout.size(), layout.align());
        }
    }
}

#[global_allocator]
static ALLOCATOR: KernelAllocator = KernelAllocator;

// `rustc` only generates these for some crate types. Even then, we would need
// to extract the object file that has them from the archive. For the moment,
// let's generate them ourselves instead.
//
// Note that `#[no_mangle]` implies exported too, nowadays.
#[no_mangle]
fn __rust_alloc(size: usize, _align: usize) -> *mut u8 {
    unsafe { bindings::krealloc(core::ptr::null(), size, bindings::GFP_KERNEL) as *mut u8 }
}

#[no_mangle]
fn __rust_dealloc(ptr: *mut u8, _size: usize, _align: usize) {
    unsafe { bindings::kfree(ptr as *const core::ffi::c_void) };
}

#[no_mangle]
fn __rust_realloc(ptr: *mut u8, _old_size: usize, _align: usize, new_size: usize) -> *mut u8 {
    unsafe {
        bindings::krealloc(
            ptr as *const core::ffi::c_void,
            new_size,
            bindings::GFP_KERNEL,
        ) as *mut u8
    }
}

#[no_mangle]
fn __rust_alloc_zeroed(size: usize, _align: usize) -> *mut u8 {
    unsafe {
        bindings::krealloc(
            core::ptr::null(),
            size,
            bindings::GFP_KERNEL | bindings::__GFP_ZERO,
        ) as *mut u8
    }
}
