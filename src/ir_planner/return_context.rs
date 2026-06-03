use super::fn_types::{FnEffects, ReturnDemand, SpecKey};
use crate::callsite_walk::ContSource;
use crate::fz_ir::{Cont, FnId, Module, Var};
use crate::types::{Ty, Types};
use std::collections::HashMap;

pub(crate) fn direct_call_return_plan<T: Types<Ty = Ty>>(
    _t: &mut T,
    _m: &Module,
    _fn_effects: &FnEffects,
    _caller_spec_key: &SpecKey,
    _env: &HashMap<Var, Ty>,
    _callee: FnId,
    _args: &[Var],
    _continuation: &Cont,
) -> ReturnDemand {
    ReturnDemand::value()
}

pub(crate) fn tail_call_return_plan(
    _m: &Module,
    _caller_spec_key: &SpecKey,
    _callee: FnId,
    _args: &[Var],
) -> ReturnDemand {
    ReturnDemand::value()
}

pub(crate) fn continuation_return_demand(
    _m: &Module,
    _caller_spec_key: &SpecKey,
    _cont: &Cont,
    _source: &ContSource,
) -> ReturnDemand {
    ReturnDemand::value()
}
