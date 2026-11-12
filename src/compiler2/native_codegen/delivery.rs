//! Small helpers over compiler2-native ABI facts.
//!
//! Shape and repr decisions are made by compiler2's transport plan. Native
//! codegen asks scalar questions of the already-published lane vectors.

use super::{ArgRepr, arg_repr_from_compiler2};
use crate::compiler2::{AbiValueRepr, NativeBody, NativeEntryAbi};
use crate::ir_codegen::CodegenError;

pub(crate) fn continuation_entry_extra_count(body: &NativeBody) -> usize {
    match body.entry_abi {
        NativeEntryAbi::Direct => 1,
        NativeEntryAbi::Continuation { extra_params } => extra_params,
    }
}

pub(crate) fn arg_reprs_from_compiler2(reprs: &[AbiValueRepr]) -> Vec<ArgRepr> {
    reprs.iter().copied().map(arg_repr_from_compiler2).collect()
}

/// The repr of the one word a root body hands the halt continuation.
///
/// The halt continuation is declared `(value, self)`, so a root can only
/// deliver a single word. The transport layer makes the root's return a
/// one-word boundary, which leaves nothing for this to guess: a body whose
/// return is any other number of lanes was not planned as a root. A root that
/// never returns delivers nothing, so the kind it names is never reached.
pub(crate) fn native_return_halt_repr(body: &NativeBody, name: &str, diverges: bool) -> Result<ArgRepr, CodegenError> {
    match body.return_reprs.as_slice() {
        [] if diverges => Ok(ArgRepr::ValueRef),
        [repr] => Ok(arg_repr_from_compiler2(*repr)),
        reprs => Err(CodegenError::new(format!(
            "a root body delivers one word to the halt continuation, but `{name}` returns {} lanes",
            reprs.len()
        ))),
    }
}
