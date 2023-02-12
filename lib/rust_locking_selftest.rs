// SPDX-License-Identifier: GPL-2.0

//! Selftests for Rust locking APIs.

use kernel::prelude::*;
const __LOG_PREFIX: &[u8] = b"locking selftest\0";

/// Entry point for tests.
#[no_mangle]
pub extern "C" fn rust_locking_test() {
    pr_info!("Selftests for Rust locking APIs");
}
