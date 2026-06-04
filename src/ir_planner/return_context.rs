//! Return-demand grant: decide the delivery *shape* a call edge may use, from
//! the cached per-fn `ReturnCapabilities` (no per-callsite body re-walking) and
//! the call's structural context. The planner grants only a shape; codegen
//! marries that shape with the IR and physical capabilities to produce operands.
//!
//! TupleFields delivery (this layer): a destructuring continuation can receive
//! its producer's tuple as separate fields, skipping the struct box, when the
//! producer returns an n-tuple on every path and the continuation projects
//! exactly those n fields. The same shape is forwarded through tail-recursive
//! producers so the field delivery survives the whole chain.

use super::fn_types::{FnEffects, ReturnCapabilities, ReturnDemand, SpecKey};
use crate::callsite_walk::ContSource;
use crate::fz_ir::{Cont, FnId, Module, Var};
use crate::types::{Ty, Types};
use std::collections::HashMap;

/// Grant `tuple_fields(n)` on the edge that feeds `cont_fn` from `producer` when
/// the producer returns an `n`-tuple on every path and `cont_fn` destructures
/// its result purely into those `n` fields. The arities must agree; otherwise
/// the value is delivered whole.
fn tuple_fields_demand(caps: &ReturnCapabilities, producer: FnId, cont_fn: FnId) -> ReturnDemand {
    let producer_arity = caps.get(&producer).and_then(|c| c.returns_tuple_of_arity);
    let destructure_arity = caps.get(&cont_fn).and_then(|c| c.destructures_slot0_into_arity);
    match (producer_arity, destructure_arity) {
        (Some(n), Some(m)) if n == m => ReturnDemand::tuple_fields(n),
        _ => ReturnDemand::value(),
    }
}

pub(crate) fn direct_call_return_plan<T: Types<Ty = Ty>>(
    _t: &mut T,
    _m: &Module,
    _fn_effects: &FnEffects,
    return_capabilities: &ReturnCapabilities,
    _caller_spec_key: &SpecKey,
    _env: &HashMap<Var, Ty>,
    callee: FnId,
    _args: &[Var],
    continuation: &Cont,
) -> ReturnDemand {
    tuple_fields_demand(return_capabilities, callee, continuation.fn_id)
}

pub(crate) fn tail_call_return_plan(
    return_capabilities: &ReturnCapabilities,
    caller_spec_key: &SpecKey,
    callee: FnId,
    _args: &[Var],
) -> ReturnDemand {
    // Forward the caller's tuple-fields delivery to a callee that is itself a
    // tuple returner of the same arity, so the field shape survives the whole
    // tail-recursive chain (e.g. partition → its clause helpers → partition).
    match caller_spec_key.demand.tuple_field_arity() {
        Some(n) if return_capabilities.get(&callee).and_then(|c| c.returns_tuple_of_arity) == Some(n) => {
            ReturnDemand::tuple_fields(n)
        }
        _ => ReturnDemand::value(),
    }
}

pub(crate) fn continuation_return_demand(
    _m: &Module,
    _caller_spec_key: &SpecKey,
    return_capabilities: &ReturnCapabilities,
    cont: &Cont,
    source: &ContSource,
) -> ReturnDemand {
    // The continuation receives its slot-0 input as fields exactly when its
    // producing direct call delivers them — the dual of `direct_call_return_plan`
    // on the same edge.
    match source {
        ContSource::Call { callee, .. } => tuple_fields_demand(return_capabilities, *callee, cont.fn_id),
        ContSource::CallClosure { .. } => ReturnDemand::value(),
    }
}
