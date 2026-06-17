//! Small helpers over compiler2-native ABI facts.
//!
//! Shape and repr decisions are made by compiler2's transport plan. Native
//! codegen asks scalar questions of the already-published lane vectors.

use super::{ArgRepr, arg_repr_from_compiler2};
use crate::compiler2::{AbiValueRepr, NativeBody, NativeEntryAbi};

pub(crate) fn continuation_entry_extra_count(body: &NativeBody) -> usize {
    match body.entry_abi {
        NativeEntryAbi::Direct => 1,
        NativeEntryAbi::Continuation { extra_params } => extra_params,
    }
}

pub(crate) fn arg_reprs_from_compiler2(reprs: &[AbiValueRepr]) -> Vec<ArgRepr> {
    reprs.iter().copied().map(arg_repr_from_compiler2).collect()
}

pub(crate) fn single_scalar_return_repr(
    diverges: bool,
    reprs: &[ArgRepr],
    tuple_arity: Option<usize>,
) -> Option<ArgRepr> {
    if diverges || tuple_arity.is_some() {
        return None;
    }
    match reprs {
        [repr] => Some(*repr),
        _ => None,
    }
}

pub(crate) fn native_return_halt_repr(body: &NativeBody) -> ArgRepr {
    match body.return_reprs.as_slice() {
        [repr] if body.return_tuple_arity.is_none() => arg_repr_from_compiler2(*repr),
        _ => ArgRepr::ValueRef,
    }
}
