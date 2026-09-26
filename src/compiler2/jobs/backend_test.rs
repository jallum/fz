use super::*;
use crate::compiler2::FunctionId;
use crate::compiler2::artifact::BackendValueLayout;
use crate::compiler2::identity::ExecutableNeed;
use crate::compiler2::pull::TransportCarrier;
use crate::compiler2::transport::{ActivationSymbol, ExecutableSymbol, LaneId, ShapeDescr};
use std::collections::BTreeMap;

#[test]
fn named_function_construction_uses_the_materialized_value_layout() {
    let mut world = World::new();
    let function = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "dead_named_ref", 0);
    let key = ExecutableKey {
        activation: ActivationKey::from_inputs(RootId::for_test(0), function, &[], world.types_mut()),
        need: ExecutableNeed::Value,
    };
    let nothing = world.intern_shape(ShapeDescr::Nothing);
    let ty = world.types_mut().int();
    let value = ValueId::from_u32(0);
    let mut executable = BackendExecutable::for_test(key, ty, nothing);
    let abi = Rc::make_mut(&mut executable.abi);
    abi.value_layouts.insert(
        value,
        BackendValueLayout {
            structural: nothing,
            carrier: TransportCarrier::Absent,
            tys: Box::default(),
            reprs: Box::default(),
        },
    );
    assert!(
        abi.transport.value_positions.is_empty(),
        "the materialized value table is sufficient without a second shape derivation"
    );
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let mut lowerer = BackendLowerer::new(
        &mut world,
        &tel,
        RootId::for_test(0),
        &abi.value_layouts,
        HashMap::new(),
        HashMap::new(),
    );
    let lowered = lowerer
        .lower_step(&LoweredStep::FunctionRef { value, function })
        .unwrap();
    assert!(
        matches!(lowered, BackendStep::Omitted { value: omitted } if omitted == value),
        "a named FunctionRef settled to Nothing must not execute a construction"
    );
}

#[test]
fn resolve_return_flow_rejects_divergence_contradictions() {
    let mut world = World::new();
    let ty = world.types_mut().int();
    let shape = world.intern_shape(ShapeDescr::Nothing);
    let position = TransportPosition::ExecutableReturn {
        executable: ExecutableSymbol {
            activation: ActivationSymbol {
                function: FunctionId::from_coordinate(1),
                arrow: ty,
                input: Box::default(),
            },
            need: ExecutableNeed::Value,
        },
    };
    let layout = |diverges| BackendReturnLayout {
        layout: BackendValueLayout {
            structural: shape,
            carrier: TransportCarrier::Absent,
            tys: Box::default(),
            reprs: Box::default(),
        },
        diverges,
    };

    let returning = HashMap::from([(position.clone(), layout(false))]);
    assert!(
        resolve_return_flow(
            &CallReturnFlow::NoReturn {
                local_source: Some(position.clone()),
            },
            &returning,
        )
        .is_err()
    );

    let divergent = HashMap::from([(position.clone(), layout(true))]);
    assert!(
        resolve_return_flow(
            &CallReturnFlow::Deliver {
                source: position.clone(),
                resume: position,
                entry: ControlEntryId::from_u32(0),
            },
            &divergent,
        )
        .is_err()
    );
}

/// FIX-1 of the fz-kdt.155 re-refutation: the seam tripwire's REFUSING
/// half must have a witness: removing the calling-convention invariant
/// shipped green through every gate (the fz-kdt.157 pattern).
/// A hand-built program with one Absent wrapper and one boxed closure
/// call delivering a lane is the mismatch `a_mixed` hits when the
/// producer half is reverted; agreement (ValueRef wrapper) must pass.
#[test]
fn the_seam_tripwire_refuses_a_lane_mismatch_and_passes_agreement() {
    use crate::compiler2::artifact::{
        BackendBody, BackendCallArg, BackendCallableReturn, BackendConstructionWrapper, BackendEntry,
        BackendEntryOrigin, BackendProgram, BackendReturnFlow, BackendTail,
    };
    use crate::compiler2::body::ControlDestination;
    use crate::compiler2::transport::CallableId;
    use crate::compiler2::{CallSiteId, ControlEntryId, ValueId};
    use crate::telemetry::ConfiguredTelemetry;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let shape = world.intern_shape(ShapeDescr::Nothing);
    let value_layout = |carrier, reprs: Vec<AbiValueRepr>| BackendValueLayout {
        structural: shape,
        carrier,
        tys: Box::default(),
        reprs: reprs.into_boxed_slice(),
    };
    let callee = ValueId::from_u32(1);
    let program = |return_form| {
        let key = ExecutableKey {
            activation: ActivationKey {
                root: RootId::for_test(0),
                function: FunctionId::from_coordinate(0),
                arrow: int,
            },
            need: ExecutableNeed::Value,
        };
        let mut executable = BackendExecutable::for_test(key.clone(), int, shape);
        Rc::make_mut(&mut executable.abi).value_layouts.insert(
            callee,
            value_layout(
                TransportCarrier::ValueRef(LaneId::for_test(0)),
                vec![AbiValueRepr::ValueRef],
            ),
        );
        executable.body = BackendBody::Clauses {
            clauses: Vec::new(),
            generated: Vec::new(),
            entries: vec![BackendEntry {
                span: Span::DUMMY,
                origin: BackendEntryOrigin::Clause,
                params: Vec::new(),
                captures: Vec::new(),
                physical_captures: Vec::new(),
                physical_params: Vec::new(),
                steps: Vec::new(),
                tail: BackendTail::ClosureCall {
                    value: ValueId::from_u32(2),
                    callsite: CallSiteId::from_u32(0),
                    callee,
                    edge: crate::compiler2::artifact::ClosureCallEdge::Seam,
                    args: vec![BackendCallArg {
                        value: ValueId::from_u32(3),
                        ownership: crate::fz_ir::OwnershipMode::Share,
                    }],
                    dest: ControlDestination::Return,
                    return_flow: Some(BackendReturnFlow::Deliver {
                        source: Box::new(BackendReturnLayout {
                            layout: value_layout(
                                TransportCarrier::ValueRef(LaneId::for_test(0)),
                                vec![AbiValueRepr::ValueRef],
                            ),
                            diverges: false,
                        }),
                        entry: ControlEntryId::from_u32(0),
                    }),
                },
            }],
        };
        let identity = TransportPosition::Value {
            executable: executable.abi.transport.executable.clone(),
            value: callee,
        };
        let wrapper = Rc::new(BackendConstructionWrapper {
            denotation: executable.key.activation.function.denotation(),
            source_origin: std::sync::Arc::new(fz_runtime::function_denotation::FunctionDenotation::named(
                None,
                "test".into(),
                0,
            )),
            identity,
            callable: CallableId::for_test(0),
            captures: Box::default(),
            call_arity: 1,
            return_form,
            members: Box::default(),
            selection: None,
        });
        executable.construction_wrappers = vec![Rc::clone(&wrapper)].into_boxed_slice();
        executable.boxed_apply_requirements =
            super::super::super::backend_program::boxed_contract::BoxedApplyRequirement::for_body(
                &executable.body,
                &executable.abi,
            );
        BackendProgram::new(
            key,
            Vec::new(),
            BTreeMap::new(),
            vec![Rc::new(executable)],
            Vec::new(),
            world.types(),
        )
    };

    assert!(
        program(BackendCallableReturn::Absent)
            .validate_boxed_contract(&tel, RootId::for_test(0))
            .is_err(),
        "a boxed call delivering one lane must refuse an Absent wrapper it can reach"
    );
    assert!(
        program(BackendCallableReturn::ValueRef)
            .validate_boxed_contract(&tel, RootId::for_test(0))
            .is_ok(),
        "agreement at one lane must pass"
    );
}
