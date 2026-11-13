use std::collections::HashMap;

use crate::compiler2::ValueMap;

use super::super::runtime_demand::{CallableFlowBuilder, propagate_steps_reverse};
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

#[test]
fn formula_snapshot_takes_peer_input_vectors_without_copying_them() {
    let mut types = Types::new();
    let any = types.any();
    let member = ExecutableKey {
        activation: ActivationKey::from_inputs(RootId::for_test(0), FunctionId::from_coordinate(0), &[], &mut types),
        need: ExecutableNeed::Value,
    };
    let peer = ExecutableKey {
        activation: ActivationKey::from_inputs(RootId::for_test(0), FunctionId::from_coordinate(1), &[any], &mut types),
        need: ExecutableNeed::Value,
    };
    let inputs = vec![RuntimeDemand::whole()];
    let input_buffer = inputs.as_ptr();
    let peer_inputs = HashMap::from([(peer.clone(), inputs)]);

    let snapshot = RuntimeDemandFormulaSnapshot::new(
        member,
        RuntimeDemandOwnInput {
            return_demand: RuntimeDemand::ignore(),
            input_demands: Vec::new(),
        },
        peer_inputs,
    );

    assert_eq!(
        snapshot
            .target_inputs
            .get(&peer)
            .expect("peer inputs are retained")
            .as_ptr(),
        input_buffer,
        "the snapshot owns the peer input allocation; it must not clone an immutable vector"
    );
}

/// Run the reverse demand walk over `steps` with one live demand on `value`,
/// and answer with the demands it leaves on the values behind it.
fn propagate_tuple_step_demand(
    types: &Types,
    steps: &[LoweredStep],
    value: ValueId,
    demand: RuntimeDemand,
) -> ValueMap<RuntimeDemand> {
    let mut types_for_key = Types::new();
    let any = types_for_key.any();
    let function = FunctionId::from_coordinate(1);
    let member = ExecutableKey {
        activation: ActivationKey::from_inputs(RootId::for_test(0), function, &[], &mut types_for_key),
        need: ExecutableNeed::Value,
    };
    let facts = ExecutableFacts {
        analysis: ActivationAnalysis {
            trimmed: Default::default(),
            input_rows: Vec::new(),
            entry_reachability: EntryReachability::new(Vec::new()),
            reachable_entries: Vec::new(),
            callsites: Vec::new(),
            value_types: ValueMap::new(),
        },
        body: LoweredBody::clauses(Vec::new(), Vec::new(), Vec::new()),
        extern_wire: None,
        entry_dispatch: None,
        callsite_dispatch_demand: HashMap::new(),
        callsites: HashMap::new(),
        callsite_needs: HashMap::new(),
        delivered_value_joins: HashMap::new(),
        callsite_return_origins: HashMap::new(),
        value_origins: ValueMap::new(),
        callable_origins: ValueMap::new(),
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
        HashMap::new(),
    );

    let mut live = ValueMap::from([(value, demand)]);
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

/// A call that chooses between two destinations by looking at its second
/// argument alone must hold that argument, wherever it sits, and has no
/// reason to hold the first: what the choice reads comes from the call's own
/// dispatch plan, not from the position of the argument.
#[test]
fn a_call_between_destinations_asks_for_exactly_the_arguments_its_choice_reads() {
    use crate::compiler2::body::{CallArg, CallInputMode, CallSiteId};
    use crate::compiler2::executable_facts::callsite_dispatch_demands;
    use crate::compiler2::semantic::{CallSiteSummary, CallTargetSummary, RuntimeDemandTypeProjection, SelectedCallee};
    use std::rc::Rc;

    let mut types = Types::new();
    let (any, int, atom, float) = (types.any(), types.int(), types.atom(), types.float());
    let target = |function: u32, second: crate::compiler2::types::Ty| CallTargetSummary {
        callee: SelectedCallee::Function(FunctionId::from_coordinate(function)),
        surface_inputs: vec![int, second],
        activation: None,
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };
    let callsite = CallSiteId::from_u32(0);
    let summaries = HashMap::from([(
        callsite,
        CallSiteSummary {
            targets: vec![target(1, int), target(2, atom)],
            return_ty: None,
        },
    )]);
    let dispatch_demand = callsite_dispatch_demands(&mut types, &summaries);

    let (first, second) = (ValueId::from_u32(0), ValueId::from_u32(1));
    let args = [first, second].map(|value| CallArg {
        value,
        ascription: None,
        ownership: crate::fz_ir::OwnershipMode::Share,
    });
    let value_types = ValueMap::from([(first, int), (second, float)]);
    let projection = |ty, dispatch| {
        (
            ty,
            Rc::new(RuntimeDemandTypeProjection {
                boundary: RuntimeDemand::ignore(),
                dispatch,
                callable_value_demand: None,
            }),
        )
    };
    let projections = HashMap::from([
        projection(int, RuntimeDemand::ignore()),
        projection(atom, RuntimeDemand::ignore()),
        projection(float, RuntimeDemand::whole()),
        projection(any, RuntimeDemand::ignore()),
    ]);
    let executable = ExecutableKey {
        activation: ActivationKey::from_inputs(RootId::for_test(0), FunctionId::from_coordinate(0), &[], &mut types),
        need: ExecutableNeed::Value,
    };
    let facts = ExecutableFacts {
        analysis: ActivationAnalysis {
            trimmed: Default::default(),
            input_rows: Vec::new(),
            entry_reachability: EntryReachability::new(Vec::new()),
            reachable_entries: Vec::new(),
            callsites: Vec::new(),
            value_types,
        },
        body: LoweredBody::clauses(Vec::new(), Vec::new(), Vec::new()),
        extern_wire: None,
        entry_dispatch: None,
        callsite_dispatch_demand: dispatch_demand,
        callsites: summaries,
        callsite_needs: HashMap::new(),
        delivered_value_joins: HashMap::new(),
        callsite_return_origins: HashMap::new(),
        value_origins: ValueMap::new(),
        callable_origins: ValueMap::new(),
        return_origins: Box::new([]),
        demand_types: RuntimeDemandTypeInputs::new(any),
        callable_activation_inputs: Vec::new(),
    };
    let facts = facts.runtime_demand_facts(&projections);
    let snapshot = RuntimeDemandFormulaSnapshot::new(
        executable.clone(),
        RuntimeDemandOwnInput {
            return_demand: RuntimeDemand::ignore(),
            input_demands: Vec::new(),
        },
        HashMap::new(),
    );

    let demands = super::arg_demands_for_summary(
        &types,
        &executable,
        callsite,
        &args,
        CallInputMode::Direct,
        &facts,
        &snapshot,
        &mut CallableFlowBuilder::default(),
    );

    assert_eq!(
        demands,
        vec![RuntimeDemand::ignore(), RuntimeDemand::whole()],
        "the choice reads the second argument only"
    );
}

#[cfg(test)]
mod tests {
    use super::super::*;
    use crate::compiler2::body::ControlEntryOrigin;
    use crate::compiler2::types::Types;
    use crate::source::Span;

    #[test]
    fn first_class_capture_retention_joins_available_exact_targets_without_guessing_missing_inputs() {
        use crate::compiler2::identity::{ActivationKey, RootId};
        use crate::compiler2::semantic::{ActivationAnalysis, EntryReachability, RuntimeDemandTypeInputs};

        let mut types = Types::new();
        let (any, int, atom) = (types.any(), types.int(), types.atom());
        let function = FunctionId::from_coordinate(1);
        let root = RootId::for_test(0);
        let target = |input, types: &mut Types| ExecutableKey {
            activation: ActivationKey::from_inputs(root, function, &[any, input], types),
            need: ExecutableNeed::Value,
        };
        let int_target = target(int, &mut types);
        let atom_target = target(atom, &mut types);
        let int_surface = CallableSurface::new(vec![int], &mut types);
        let atom_surface = CallableSurface::new(vec![atom], &mut types);
        let facts = ExecutableFacts {
            analysis: ActivationAnalysis {
                trimmed: Default::default(),
                input_rows: Vec::new(),
                entry_reachability: EntryReachability::new(Vec::new()),
                reachable_entries: Vec::new(),
                callsites: Vec::new(),
                value_types: ValueMap::new(),
            },
            body: LoweredBody::clauses(Vec::new(), Vec::new(), Vec::new()).with_value_count(2),
            extern_wire: None,
            entry_dispatch: None,
            callsite_dispatch_demand: HashMap::new(),
            callsites: HashMap::new(),
            callsite_needs: HashMap::new(),
            delivered_value_joins: HashMap::new(),
            callsite_return_origins: HashMap::new(),
            value_origins: ValueMap::new(),
            callable_origins: ValueMap::new(),
            return_origins: Box::new([]),
            demand_types: RuntimeDemandTypeInputs::new(any),
            callable_activation_inputs: Vec::new(),
        };
        let projections = HashMap::new();
        let facts = facts.runtime_demand_facts(&projections);
        let value = ValueId::from_u32(0);
        let capture = ValueId::from_u32(1);
        let mut inputs = RuntimeDemandFormulaSnapshot {
            member: int_target.clone(),
            own: RuntimeDemandOwnInput {
                return_demand: RuntimeDemand::ignore(),
                input_demands: Vec::new(),
            },
            target_inputs: HashMap::new(),
            construction_targets: HashMap::from([
                ((value, int_surface.clone()), int_target.clone()),
                ((value, atom_surface.clone()), atom_target.clone()),
            ]),
        };
        let derive = |inputs: &RuntimeDemandFormulaSnapshot| {
            let mut live = ValueMap::new();
            let mut out = ExecutableRuntimeDemand::default();
            propagate_lambda_capture_demands(
                &types,
                value,
                function,
                &[capture],
                RuntimeDemand::callable(CallableDemand::escaped()),
                &facts,
                inputs,
                &mut live,
                &mut out,
                &mut CallableFlowBuilder::new(),
            );
            out.value_demands
        };
        assert!(
            derive(&inputs).is_empty(),
            "missing target inputs are unknown, not a Whole escape"
        );
        let capture_demand = |surface: CallableSurface| {
            RuntimeDemand::callable(CallableDemand {
                resolved: BTreeSet::from([surface]),
                ..CallableDemand::default()
            })
        };
        inputs
            .target_inputs
            .insert(int_target, vec![capture_demand(int_surface.clone())]);
        let partial = derive(&inputs);
        let retained = partial
            .get(&capture)
            .expect("one available target can publish retention");
        assert_eq!(retained.shape, ShapeDemand::Whole);
        assert_eq!(retained.callable.resolved, BTreeSet::from([int_surface.clone()]));
        inputs
            .target_inputs
            .insert(atom_target, vec![capture_demand(atom_surface.clone())]);
        let complete = derive(&inputs);
        assert_eq!(complete[&capture].shape, ShapeDemand::Whole);
        assert_eq!(
            complete[&capture].callable.resolved,
            BTreeSet::from([int_surface, atom_surface])
        );
    }

    #[test]
    fn lowered_call_kind_is_preserved_in_transport_origins() {
        let direct_callsite = CallSiteId::from_u32(0);
        let closure_callsite = CallSiteId::from_u32(1);
        let direct_value = ValueId::from_u32(0);
        let closure_value = ValueId::from_u32(1);
        let entry = |tail| LoweredEntry {
            span: Span::DUMMY,
            origin: ControlEntryOrigin::Clause,
            params: Vec::new(),
            captures: Vec::new(),
            physical_captures: Vec::new(),
            physical_params: Vec::new(),
            steps: Vec::new(),
            tail,
        };
        let body = LoweredBody::clauses(
            Vec::new(),
            vec![
                entry(LoweredTail::DirectCall {
                    value: direct_value,
                    callsite: direct_callsite,
                    callee: FunctionId::from_coordinate(0),
                    args: Vec::new(),
                    dest: ControlDestination::Return,
                }),
                entry(LoweredTail::ClosureCall {
                    value: closure_value,
                    callsite: closure_callsite,
                    callee: ValueId::from_u32(2),
                    args: Vec::new(),
                    dest: ControlDestination::Return,
                }),
            ],
            Vec::new(),
        );

        let callsite_origins = collect_callsite_return_origins(&body);
        let value_origins = collect_value_origins(&body, &callsite_origins);

        assert_eq!(
            value_origins.get(&direct_value),
            Some(&TransportOrigin::CallsiteReturn(direct_callsite))
        );
        assert_eq!(
            value_origins.get(&closure_value),
            Some(&TransportOrigin::ClosureCallReturn {
                callsite: closure_callsite,
                callee: ValueId::from_u32(2),
            })
        );
    }
}
