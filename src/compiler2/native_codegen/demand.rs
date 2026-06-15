//! Codegen view of compiler2-native return and continuation ABI facts.

use super::{ArgRepr, arg_repr_from_compiler2};
use crate::compiler2::{NativeBody, NativeEntryAbi, TrashReturnAbi, TrashRuntimeValueLayout};

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) enum TrashDeliveredShape {
    Never,
    Omitted,
    Value(ArgRepr),
    TupleFields(Box<[ArgRepr]>),
}

#[derive(Clone, Copy)]
pub(crate) struct TrashNativeDemandAbi<'a> {
    body: &'a NativeBody,
}

impl<'a> TrashNativeDemandAbi<'a> {
    pub(crate) fn new(body: &'a NativeBody) -> Self {
        Self { body }
    }

    /// Tuple-field return delivery is a pure transport question -- it never
    /// depends on divergence -- so it reads the settled return layout directly.
    /// A returned direct callable is reconstructed by its consumer, not
    /// destructured into tuple fields, so it is not a tuple-field delivery.
    pub(crate) fn tuple_field_arity(self) -> Option<usize> {
        match &self.body.return_layout {
            TrashRuntimeValueLayout::TupleFields { fields } => Some(fields.len()),
            TrashRuntimeValueLayout::Omitted
            | TrashRuntimeValueLayout::Value { .. }
            | TrashRuntimeValueLayout::DirectCallable { .. } => None,
        }
    }

    pub(crate) fn continuation_entry_extras(self) -> usize {
        match self.body.entry_abi {
            NativeEntryAbi::Direct => 1,
            NativeEntryAbi::Continuation { extra_params } => extra_params,
        }
    }
}

/// Settles the delivered return shape of one body. Divergence is the type fact
/// `is_empty(return_ty)`; everything else flattens from the settled transport
/// layout. This is the single place return shape is decided, run where types
/// are available, so codegen consumes it without re-deriving anything.
pub(crate) fn trash_delivered_shape_from_layout(
    diverges: bool,
    layout: &TrashRuntimeValueLayout,
) -> TrashDeliveredShape {
    if diverges {
        return TrashDeliveredShape::Never;
    }
    match layout {
        TrashRuntimeValueLayout::Omitted => TrashDeliveredShape::Omitted,
        TrashRuntimeValueLayout::Value { repr, .. } => TrashDeliveredShape::Value(arg_repr_from_compiler2(*repr)),
        TrashRuntimeValueLayout::TupleFields { .. } => TrashDeliveredShape::TupleFields(arg_reprs_boxed(layout)),
        TrashRuntimeValueLayout::DirectCallable { capture_lanes, .. } => match capture_lanes.len() {
            0 => TrashDeliveredShape::Omitted,
            1 => TrashDeliveredShape::Value(arg_repr_from_compiler2(capture_lanes[0].repr)),
            _ => TrashDeliveredShape::TupleFields(arg_reprs_boxed(layout)),
        },
    }
}

fn arg_reprs_boxed(layout: &TrashRuntimeValueLayout) -> Box<[ArgRepr]> {
    layout
        .abi_reprs()
        .into_iter()
        .map(arg_repr_from_compiler2)
        .collect::<Vec<_>>()
        .into_boxed_slice()
}

/// Projects a true-boundary return ABI to its delivered shape. Boundary ABIs
/// remain scalar/tuple publication facts, so this stays narrow.
pub(crate) fn trash_delivered_shape_from_return_abi(return_abi: &TrashReturnAbi) -> TrashDeliveredShape {
    match return_abi {
        TrashReturnAbi::Never => TrashDeliveredShape::Never,
        TrashReturnAbi::Value(repr) => TrashDeliveredShape::Value(arg_repr_from_compiler2(*repr)),
        TrashReturnAbi::TupleFields(fields) => TrashDeliveredShape::TupleFields(
            fields
                .iter()
                .copied()
                .map(arg_repr_from_compiler2)
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        ),
    }
}
