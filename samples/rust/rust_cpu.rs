// SPDX-License-Identifier: GPL-2.0

//! Rust CPU-related operations sample

#![no_std]
#![feature(allocator_api, global_asm)]

use kernel::cpu::{cpus_read_lock, online_cpus, possible_cpus};
use kernel::prelude::*;

module! {
    type: RustCPU,
    name: b"rust_cpu",
    author: b"Rust for Linux Contributors",
    description: b"Rust CPU-related operations sample",
    license: b"GPL v2",
    params: {
    },
}

struct RustCPU;

impl KernelModule for RustCPU {
    fn init() -> Result<Self> {
        pr_info!("Rust thread APIs sample (init)");

        // Test cpumask iterations.
        {
            for i in possible_cpus() {
                pr_info!("CPU {} is possible.", i);
            }

            let c = cpus_read_lock.lock();

            for i in online_cpus(&c) {
                pr_info!("CPU {} is online.", i);
            }
        }

        Ok(RustCPU)
    }
}

impl Drop for RustCPU {
    fn drop(&mut self) {
        pr_info!("Rust thread APIs sample (exit)");
    }
}
