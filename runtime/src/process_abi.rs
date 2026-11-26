//! Runtime-owned `Process` layout constants for generated code.
//!
//! Keep this module narrow: compiled code may only import offsets that are
//! intentionally part of the runtime/codegen ABI.

use crate::handler_stack::{HANDLER_STACK_END_OFFSET, HANDLER_STACK_TOP_OFFSET};
use crate::process::Process;
use std::mem::offset_of;

pub const PROCESS_REDUCTIONS_REMAINING_OFFSET: i32 = offset_of!(Process, reductions_remaining) as i32;
pub const PROCESS_YIELD_REASONS_OFFSET: i32 = offset_of!(Process, yield_reasons) as i32;
/// `Process::unwinding`: nonzero when the process failed or a raise delivered a
/// handler, so code that called something that may raise must return.
pub const PROCESS_UNWINDING_OFFSET: i32 = offset_of!(Process, unwinding) as i32;

/// `Process::heap`; add a `heap::INLINE_ALLOC_LAYOUT` field offset to reach a
/// heap field that inline allocation updates.
pub const PROCESS_HEAP_OFFSET: i32 = offset_of!(Process, heap) as i32;

/// `Heap::binaries_shared`, which compiled code adds to when it marks a binary
/// shared without a runtime call.
pub const PROCESS_BINARIES_SHARED_OFFSET: i32 =
    (offset_of!(Process, heap) + offset_of!(crate::heap::Heap, binaries_shared)) as i32;

/// The handler stack's `top` and `end`, which a compiled `try` reads and
/// writes to push and pop its handler record without a runtime call.
pub const PROCESS_HANDLER_TOP_OFFSET: i32 = (offset_of!(Process, handlers) + HANDLER_STACK_TOP_OFFSET) as i32;
pub const PROCESS_HANDLER_END_OFFSET: i32 = (offset_of!(Process, handlers) + HANDLER_STACK_END_OFFSET) as i32;

/// `Process::atom_key_hashes`: the address of the word that holds where the
/// atom key hashes begin, one word per atom id.
pub const PROCESS_ATOM_KEY_HASHES_OFFSET: i32 = offset_of!(Process, atom_key_hashes) as i32;
#[cfg(test)]
#[path = "process_abi_test.rs"]
mod process_abi_test;
