//! Codegen view of planner-selected return-demand ABI facts.

use crate::ir_planner::fn_types::{ReturnDemand, SpecKey};
use crate::types::Ty;

#[derive(Clone, Copy)]
pub(crate) struct DemandAbi<'a> {
    demand: &'a ReturnDemand,
}

impl<'a> DemandAbi<'a> {
    pub(crate) fn new(spec_key: &'a SpecKey) -> Self {
        Self {
            demand: &spec_key.demand,
        }
    }

    pub(crate) fn tuple_field_arity(self) -> Option<usize> {
        self.demand.tuple_field_arity()
    }

    pub(crate) fn has_list_tail_context(self) -> bool {
        self.demand.list_tail_ty().is_some()
    }

    pub(crate) fn has_list_tail_native_param(self, is_native: bool, is_cont_fn: bool) -> bool {
        is_native && !is_cont_fn && self.has_list_tail_context()
    }

    pub(crate) fn carries_list_tail_capture(self) -> bool {
        self.tuple_field_arity().is_some() && self.has_list_tail_context()
    }

    pub(crate) fn delivers_list_tail_return(self) -> bool {
        self.tuple_field_arity().is_none() && self.has_list_tail_context()
    }

    pub(crate) fn continuation_extras(self, fallback: Option<usize>) -> usize {
        self.tuple_field_arity().or(fallback).unwrap_or(1)
    }
}
