use std::collections::HashMap;

use super::runtime_demand::{CallableFlowBuilder, propagate_steps_reverse};
use crate::compiler2::body::{LoweredBody, LoweredStep, ValueId};
use crate::compiler2::executable_facts::ExecutableFacts;
use crate::compiler2::identity::{ActivationKey, ExecutableKey, ExecutableNeed, FunctionId, RootId};
use crate::compiler2::jobs::runtime_demand::{RuntimeDemandFormulaSnapshot, RuntimeDemandOwnInput};
use crate::compiler2::semantic::{
    ActivationAnalysis, EntryReachability, ExecutableRuntimeDemand, RuntimeDemand, RuntimeDemandTypeInputs, ShapeDemand,
};
use crate::compiler2::types::Types;

/// A field-demand vector is a prefix, and a prefix can be longer than the
/// tuple in front of it: one value's type spans several arities, and a clause
/// that reads three fields states three whether or not this construction has
/// them. Fitting it to the construction is what `ShapeDemand::field_prefix`
/// does -- the entries that name a field are distributed, the surplus names no
/// field here and drops. Widening the whole tuple to `Whole` because the
/// vector was long would make every item needed, including the one the
/// consumer explicitly ignored.
#[test]
fn an_over_long_field_demand_reads_the_fields_the_tuple_has() {
    let types = Types::new();
    let tuple = ValueId::from_u32(0);
    let first = ValueId::from_u32(1);
    let second = ValueId::from_u32(2);
    let steps = vec![LoweredStep::Tuple {
        value: tuple,
        items: vec![
            crate::fz_ir::OwnershipUse::share(first),
            crate::fz_ir::OwnershipUse::share(second),
        ],
    }];

    let demanded = propagate_tuple_step_demand(
        &types,
        &steps,
        tuple,
        RuntimeDemand::tuple_fields(vec![
            RuntimeDemand::whole(),
            RuntimeDemand::ignore(),
            RuntimeDemand::whole(),
        ]),
    );

    assert_eq!(
        demanded.get(&first).map(|demand| demand.shape.clone()),
        Some(ShapeDemand::Whole),
        "field 0 is named and needed",
    );
    assert_eq!(
        demanded.get(&second),
        None,
        "field 1 is named and ignored: the third entry describes a tuple this one is not",
    );
}

/// Run the reverse demand walk over `steps` with one live demand on `value`,
/// and answer with the demands it leaves on the values behind it.
fn propagate_tuple_step_demand(
    types: &Types,
    steps: &[LoweredStep],
    value: ValueId,
    demand: RuntimeDemand,
) -> HashMap<ValueId, RuntimeDemand> {
    let mut types_for_key = Types::new();
    let any = types_for_key.any();
    let function = FunctionId::from_coordinate(1);
    let member = ExecutableKey {
        activation: ActivationKey::from_inputs(RootId::for_test(0), function, &[], &mut types_for_key),
        need: ExecutableNeed::Value,
    };
    let facts = ExecutableFacts {
        analysis: ActivationAnalysis {
            input_rows: Vec::new(),
            entry_reachability: EntryReachability::new(Vec::new(), false),
            reachable_entries: Vec::new(),
            callsites: Vec::new(),
            value_types: HashMap::new(),
        },
        body: LoweredBody::clauses(Vec::new(), Vec::new(), Vec::new()),
        entry_dispatch: None,
        callsites: HashMap::new(),
        callsite_needs: HashMap::new(),
        delivered_value_joins: HashMap::new(),
        callsite_return_origins: HashMap::new(),
        value_origins: HashMap::new(),
        callable_origins: HashMap::new(),
        return_origins: Box::new([]),
        demand_types: RuntimeDemandTypeInputs::new(any),
        callable_activation_inputs: Vec::new(),
    };
    let projections = HashMap::new();
    let facts = facts.runtime_demand_facts(&projections);
    let snapshot = RuntimeDemandFormulaSnapshot::new(
        member,
        RuntimeDemandOwnInput {
            return_demand: RuntimeDemand::ignore(),
            input_demands: Vec::new(),
        },
        &HashMap::new(),
    );

    let mut live = HashMap::from([(value, demand)]);
    let mut out = ExecutableRuntimeDemand::default();
    propagate_steps_reverse(
        types,
        steps,
        &mut live,
        &facts,
        &snapshot,
        &mut out,
        &mut CallableFlowBuilder::default(),
    );
    out.value_demands
}
