//! Codegen view of compiler2-native return and continuation ABI facts.

use super::{ArgRepr, arg_repr_from_compiler2};
use crate::compiler2::{NativeBody, NativeEntryAbi, ReturnAbi};

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) enum DeliveredShape {
    Never,
    Omitted,
    Value(ArgRepr),
    TupleFields(Box<[ArgRepr]>),
}

#[derive(Clone, Copy)]
pub(crate) struct NativeDemandAbi<'a> {
    body: &'a NativeBody,
}

impl<'a> NativeDemandAbi<'a> {
    pub(crate) fn new(body: &'a NativeBody) -> Self {
        Self { body }
    }

    pub(crate) fn tuple_field_arity(self) -> Option<usize> {
        match &self.body.return_abi {
            ReturnAbi::TupleFields(fields) => Some(fields.len()),
            ReturnAbi::Never | ReturnAbi::Value(_) => None,
        }
    }

    pub(crate) fn delivers_value_lane(self) -> bool {
        matches!(self.returned_shape(), DeliveredShape::Value(_))
    }

    pub(crate) fn returned_delivers_value_lane(self) -> bool {
        self.delivers_value_lane()
    }

    pub(crate) fn returned_shape(self) -> DeliveredShape {
        delivered_shape_from_return_abi(&self.body.return_abi)
    }

    pub(crate) fn continuation_entry_extras(self) -> usize {
        match self.body.entry_abi {
            NativeEntryAbi::Direct => 1,
            NativeEntryAbi::Continuation { extra_params } => extra_params,
        }
    }
}

pub(crate) fn delivered_shape_from_return_abi(return_abi: &ReturnAbi) -> DeliveredShape {
    match return_abi {
        ReturnAbi::Never => DeliveredShape::Never,
        ReturnAbi::Value(repr) => DeliveredShape::Value(arg_repr_from_compiler2(*repr)),
        ReturnAbi::TupleFields(fields) => DeliveredShape::TupleFields(
            fields
                .iter()
                .copied()
                .map(arg_repr_from_compiler2)
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        ),
    }
}
