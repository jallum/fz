//! Codegen view of compiler2-native return and continuation ABI facts.

use super::{ArgRepr, arg_repr_from_compiler2};
use crate::compiler2::{NativeBody, NativeEntryAbi};

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
        match self.body.return_lane_reprs.len() {
            0 | 1 => None,
            arity => Some(arity),
        }
    }

    pub(crate) fn delivers_value_lane(self) -> bool {
        matches!(self.returned_shape(), DeliveredShape::Value(_))
    }

    pub(crate) fn returned_delivers_value_lane(self) -> bool {
        self.delivers_value_lane()
    }

    pub(crate) fn returned_shape(self) -> DeliveredShape {
        if matches!(self.body.return_abi, crate::compiler2::ReturnAbi::Never) {
            return DeliveredShape::Never;
        }
        match self.body.return_lane_reprs.as_slice() {
            [] => DeliveredShape::Omitted,
            [repr] => DeliveredShape::Value(arg_repr_from_compiler2(*repr)),
            reprs => DeliveredShape::TupleFields(
                reprs
                    .iter()
                    .copied()
                    .map(arg_repr_from_compiler2)
                    .collect::<Vec<_>>()
                    .into_boxed_slice(),
            ),
        }
    }

    pub(crate) fn continuation_entry_extras(self) -> usize {
        match self.body.entry_abi {
            NativeEntryAbi::Direct => 1,
            NativeEntryAbi::Continuation { extra_params } => extra_params,
        }
    }
}
