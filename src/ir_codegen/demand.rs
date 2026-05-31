//! Codegen view of planner-selected return-demand ABI facts.

use super::ArgRepr;
use crate::ir_planner::fn_types::{ReturnDemand, SpecKey};

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

    #[cfg(test)]
    pub(crate) fn from_demand(demand: &'a ReturnDemand) -> Self {
        Self { demand }
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

    pub(crate) fn returned_tuple_field_arity(self, is_cont_fn: bool) -> Option<usize> {
        if is_cont_fn {
            None
        } else {
            self.tuple_field_arity()
        }
    }

    pub(crate) fn returned_delivers_list_tail_return(self, is_cont_fn: bool) -> bool {
        if is_cont_fn && self.tuple_field_arity().is_some() {
            self.has_list_tail_context()
        } else {
            self.delivers_list_tail_return()
        }
    }

    pub(crate) fn delivered_value_repr(self) -> Option<ArgRepr> {
        if self.tuple_field_arity().is_some() {
            None
        } else {
            Some(ArgRepr::ValueRef)
        }
    }

    pub(crate) fn returned_value_repr(self, is_cont_fn: bool) -> Option<ArgRepr> {
        if is_cont_fn && self.tuple_field_arity().is_some() {
            Some(ArgRepr::ValueRef)
        } else {
            self.delivered_value_repr()
        }
    }

    pub(crate) fn continuation_extras(self, fallback: Option<usize>) -> usize {
        self.tuple_field_arity().or(fallback).unwrap_or(1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Types;

    #[test]
    fn value_demand_delivers_boxed_value_ref() {
        let demand = ReturnDemand::value();
        let abi = DemandAbi::from_demand(&demand);
        assert_eq!(abi.delivered_value_repr(), Some(ArgRepr::ValueRef));
    }

    #[test]
    fn list_tail_demand_still_delivers_a_boxed_value_lane() {
        let mut t = crate::types::ConcreteTypes;
        let int = t.int();
        let demand = ReturnDemand::list_tail(t.list(int));
        let abi = DemandAbi::from_demand(&demand);
        assert_eq!(abi.delivered_value_repr(), Some(ArgRepr::ValueRef));
    }

    #[test]
    fn tuple_field_demand_has_no_single_value_lane() {
        let demand = ReturnDemand::tuple_fields(2);
        let abi = DemandAbi::from_demand(&demand);
        assert_eq!(abi.delivered_value_repr(), None);
    }

    #[test]
    fn tuple_field_list_tail_demand_has_no_single_value_lane() {
        let mut t = crate::types::ConcreteTypes;
        let int = t.int();
        let demand = ReturnDemand::tuple_fields_list_tail(2, t.list(int));
        let abi = DemandAbi::from_demand(&demand);
        assert_eq!(abi.delivered_value_repr(), None);
    }

    #[test]
    fn continuation_outer_return_collapses_tuple_fields_back_to_boxed_value() {
        let demand = ReturnDemand::tuple_fields(2);
        let abi = DemandAbi::from_demand(&demand);
        assert_eq!(abi.returned_value_repr(true), Some(ArgRepr::ValueRef));
    }

    #[test]
    fn continuation_outer_return_preserves_list_tail_when_tuple_fields_carried_it() {
        let mut t = crate::types::ConcreteTypes;
        let int = t.int();
        let demand = ReturnDemand::tuple_fields_list_tail(2, t.list(int));
        let abi = DemandAbi::from_demand(&demand);
        assert!(abi.returned_delivers_list_tail_return(true));
        assert_eq!(abi.returned_tuple_field_arity(true), None);
    }
}
