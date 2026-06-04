//! Runtime-owned `Process` layout constants for generated code.
//!
//! Keep this module narrow: compiled code may only import offsets that are
//! intentionally part of the runtime/codegen ABI.

use crate::process::Process;
use std::mem::offset_of;

pub const PROCESS_REDUCTIONS_REMAINING_OFFSET: i32 = offset_of!(Process, reductions_remaining) as i32;
pub const PROCESS_YIELD_REASONS_OFFSET: i32 = offset_of!(Process, yield_reasons) as i32;

#[cfg(test)]
#[path = "process_abi_test.rs"]
mod process_abi_test;
