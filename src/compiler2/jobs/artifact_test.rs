use super::*;
use crate::compiler2::semantic::{
    CallSiteResolution, CallSiteSummary, CallTargetSummary, EntryReachability, SelectedCallee,
};
use crate::compiler2::transport::{LaneId, TransportCarrier};
use crate::compiler2::{ActivationKey, FunctionId};
use crate::fz_ir::{ExternAbi, ExternTy};
use crate::telemetry::ConfiguredTelemetry;
use crate::type_expr::ResolvedSpecDecl;

#[test]
fn generic_extern_effects_do_not_depend_on_privileged_symbol_spellings() {
    let mut world = World::new();
    let nil = world.types_mut().nil();
    let extern_body = |symbol: &str| LoweredBody::Extern {
        signature: super::super::super::body::LoweredExtern {
            abi: ExternAbi::C,
            symbol: symbol.to_string(),
            params: Vec::new(),
            variadic: false,
            ret: crate::fz_ir::ExternReturn::Scalar(ExternTy::Unit),
            return_ty: nil,
            semantic_contract: ResolvedSpecDecl {
                params: Vec::new(),
                result: nil,
                constraints: HashMap::new(),
            },
        },
    };
    let expected_local = EffectSummary {
        observable: true,
        ..EffectSummary::default()
    };
    let expected_transitive = EffectSummary {
        allocates: true,
        observable: true,
        ..EffectSummary::default()
    };

    for symbol in [
        "ordinary_foreign_function",
        "fz_process_heap_alloc_stats",
        "fz_send",
        "fz_spawn",
    ] {
        let local = local_effects(&extern_body(symbol), &HashMap::new());
        assert_eq!(local, expected_local, "`{symbol}` must use generic extern effects");

        let mut caller = EffectSummary {
            allocates: true,
            ..EffectSummary::default()
        };
        caller.union_with(local);
        assert_eq!(
            caller, expected_transitive,
            "callers must not acquire an effect from `{symbol}` by spelling"
        );
    }
}

#[test]
fn carrier_provenance_forces_value_ref_for_a_raw_capable_lane() {
    let mut world = World::new();
    let int = world.types_mut().int();
    let lane = world.intern_lane(super::super::super::transport::LaneDescr {
        ty: int,
        class: super::super::super::transport::TransportClass::Value,
    });
    let shape = world.intern_shape(ShapeDescr::Lane(lane));
    let structural = abi_layout_contract(&mut world, TransportLayout::structural(shape));
    let carrier = abi_layout_contract(
        &mut world,
        TransportLayout {
            structural: shape,
            carrier: TransportCarrier::ValueRef(lane),
        },
    );

    assert_eq!(structural, vec![(int, AbiValueRepr::RawInt)]);
    assert_eq!(carrier, vec![(int, AbiValueRepr::ValueRef)]);
}

#[test]
fn sort_transport_positions_orders_one_partition_by_structural_discriminants() {
    // Each MaterializedExecutableTransport field vector holds ONE variant
    // of ONE executable by construction (positions are gathered from the
    // per-symbol index and partitioned by variant), so packaging order is
    // decided purely by the variant-local structural discriminants --
    // here CallArg's (callsite, semantic_index) -- independent of
    // arrival order and of any interned-type identity.
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(None, "def main(x), do: x".to_string());
    let root = world.submit_root(None, "main".to_string(), 1, ExecutableNeed::Value);
    let function = world.root_entry(root).function;
    let int = world.types_mut().int();
    let symbol = ExecutableSymbol {
        activation: ActivationSymbol {
            function,
            arrow: int,
            input: vec![int].into_boxed_slice(),
        },
        need: ExecutableNeed::Value,
    };
    let call_arg = |callsite: u32, semantic_index: usize| TransportPosition::CallArg {
        executable: symbol.clone(),
        callsite: CallSiteId::from_u32(callsite),
        semantic_index,
    };

    let mut positions = vec![call_arg(1, 1), call_arg(1, 0), call_arg(0, 1)];
    sort_transport_positions(&mut positions, world.types());

    assert_eq!(positions, vec![call_arg(0, 1), call_arg(1, 0), call_arg(1, 1)]);
}

fn fake_call_executable(world: &mut World, root: u32, function: u32, inputs: &[Ty]) -> ExecutableKey {
    let activation = ActivationKey::from_inputs(
        RootId::for_test(root),
        FunctionId::from_coordinate(function),
        inputs,
        world.types_mut(),
    );
    ExecutableKey {
        activation,
        need: ExecutableNeed::Value,
    }
}

#[test]
fn return_payload_is_owned_only_by_its_caller() {
    let mut world = World::new();
    let caller = fake_call_executable(&mut world, 10, 11, &[]);
    let callee = fake_call_executable(&mut world, 10, 12, &[]);
    let caller_symbol = transport_executable_symbol(&caller, world.types());
    let callee_symbol = transport_executable_symbol(&callee, world.types());
    let callsite = CallSiteId::from_u32(7);

    let positions = return_flow_transport_positions(
        &caller_symbol,
        callsite,
        &ControlDestination::Return,
        [callee_symbol.clone()],
    );

    assert!(positions.contains(&TransportPosition::ReturnPayload {
        executable: caller_symbol,
        callsite,
    }));
    assert!(positions.contains(&TransportPosition::ExecutableReturn {
        executable: callee_symbol.clone(),
    }));
    assert!(!positions.contains(&TransportPosition::ReturnPayload {
        executable: callee_symbol,
        callsite,
    }));
}

#[test]
fn local_no_return_flow_carries_exact_return_endpoint() {
    let mut world = World::new();
    let callee = fake_call_executable(&mut world, 100, 102, &[]);
    let target = CallTarget::Local(callee.clone());
    let flow = exact_no_return_flow(&world, &target);

    assert_eq!(
        flow,
        CallReturnFlow::NoReturn {
            local_source: Some(TransportPosition::ExecutableReturn {
                executable: transport_executable_symbol(&callee, world.types()),
            }),
        }
    );
}

/// What static target evidence stands behind the closure callsite under
/// test -- the axis that decides how the edge is lowered.
#[derive(Clone, Copy)]
enum ClosureCallEvidence {
    /// Two settled targets, each with a return type.
    AmbiguousReturning,
    /// Two settled targets, none of which returns.
    AmbiguousNonReturning,
    /// No summary at all. This is the standing state for a callable that
    /// arrived from outside the analysed world -- a mailbox message -- and
    /// no later evidence will ever name a target for it (fz-kdt.130).
    Unnamed,
}

impl ClosureCallEvidence {
    fn summary_targets_return(self) -> bool {
        matches!(self, Self::AmbiguousReturning)
    }

    /// Whether the callsite's semantic result carries a value. An unnamed
    /// callee still produces one: only its *targets* are unknown.
    fn call_returns(self) -> bool {
        !matches!(self, Self::AmbiguousNonReturning)
    }
}

fn try_materialize_closure_edge(
    evidence: ClosureCallEvidence,
    carrier: TransportCarrier,
) -> (World, Result<MaterializedCallEdge, FatalError>) {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let caller = fake_call_executable(&mut world, 300, 301, &[]);
    let callsite = CallSiteId::from_u32(7);
    let key = CallSiteKey {
        activation: caller.activation.clone(),
        callsite,
    };
    let targets_return = evidence.summary_targets_return();
    if !matches!(evidence, ClosureCallEvidence::Unnamed) {
        world.define_callsite_summary(
            key,
            CallSiteResolution::Resolved(CallSiteSummary {
                targets: [302, 303]
                    .into_iter()
                    .map(|function| CallTargetSummary {
                        callee: SelectedCallee::Function(FunctionId::from_coordinate(function)),
                        surface_inputs: vec![int],
                        activation: None,
                        activation_inputs: None,
                        extern_params: None,
                        return_ty: targets_return.then_some(int),
                    })
                    .collect(),
                return_ty: targets_return.then_some(int),
            }),
        );
    }
    let call_returns = evidence.call_returns();
    let result_value = ValueId::from_u32(2);
    let analysis = ActivationAnalysis {
        input_rows: Vec::new(),
        entry_reachability: EntryReachability::new(Vec::new(), false),
        reachable_entries: Vec::new(),
        callsites: Vec::new(),
        value_types: call_returns.then_some((result_value, int)).into_iter().collect(),
    };
    let positions = if call_returns {
        let caller_symbol = transport_executable_symbol(&caller, world.types());
        let caller_return = TransportPosition::ExecutableReturn {
            executable: caller_symbol.clone(),
        };
        let payload = TransportPosition::ReturnPayload {
            executable: caller_symbol,
            callsite,
        };
        let shape = world.intern_shape(ShapeDescr::Nothing);
        vec![
            (caller_return, TransportLayout::structural(shape)),
            (
                payload,
                TransportLayout {
                    structural: shape,
                    carrier: TransportCarrier::ValueRef(LaneId::for_test(0)),
                },
            ),
        ]
    } else {
        Vec::new()
    };
    let transport_plan = ArtifactTransportLookup { positions: &positions };
    let callee_layout = TransportLayout {
        structural: world.intern_shape(ShapeDescr::Nothing),
        carrier,
    };
    let summaries = world
        .callsite_summary(&CallSiteKey {
            activation: caller.activation.clone(),
            callsite,
        })
        .cloned()
        .map(|summary| HashMap::from([(callsite, summary)]))
        .unwrap_or_default();
    let edge = materialize_closure_call_edge(
        &mut world,
        &tel,
        RootId::for_test(300),
        &transport_plan,
        &caller,
        &analysis,
        &summaries,
        callee_layout,
        ExecutableNeed::Value,
        callsite,
        result_value,
        &ControlDestination::Return,
        &[],
        &HashMap::new(),
    );
    (world, edge)
}

fn materialize_closure_edge(evidence: ClosureCallEvidence) -> (World, MaterializedCallEdge) {
    let (world, edge) = try_materialize_closure_edge(evidence, TransportCarrier::ValueRef(LaneId::for_test(0)));
    (world, edge.expect("materialization should not fail"))
}

#[test]
fn materialize_closure_call_edge_routes_ambiguous_multi_target_through_indirect() {
    let (_world, edge) = materialize_closure_edge(ClosureCallEvidence::AmbiguousReturning);
    let CallEdge::Indirect(CallReturnFlow::Continue {
        source,
        payload,
        caller_return,
    }) = edge.target()
    else {
        panic!("returning multi-target closure call should carry indirect return flow")
    };
    assert_eq!(source, payload);
    assert_ne!(source, caller_return);
}

#[test]
fn materialize_closure_call_edge_routes_settled_empty_multi_target_without_a_result_value() {
    let (world, edge) = materialize_closure_edge(ClosureCallEvidence::AmbiguousNonReturning);
    assert!(world.types().is_empty(&edge.return_ty()));
    assert_eq!(
        edge.target(),
        &CallEdge::Indirect(CallReturnFlow::NoReturn { local_source: None })
    );
}

/// fz-kdt.130. A callable that arrived through the mailbox names no target
/// and never will, but it is a real value the boxed-apply wrapper can call.
/// Reading "no targets" as the empty type made this a `NoReturn` edge, and
/// native lowering turns `NoReturn` into a tail call -- which silently drops
/// everything the caller meant to do after the call. The carrier decides.
#[test]
fn materialize_closure_call_edge_calls_an_unnamed_callable_and_comes_back() {
    let (world, edge) = materialize_closure_edge(ClosureCallEvidence::Unnamed);
    assert!(!world.types().is_empty(&edge.return_ty()));
    assert!(
        matches!(edge.target(), CallEdge::Indirect(CallReturnFlow::Continue { .. })),
        "an unnamed callable behind a runtime carrier must return to its caller, got {:?}",
        edge.target()
    );
}

/// The other side of that line: with no carrier AND no evidence there is
/// nothing to call, so the dead-call lowering still stands (fz-f98.18).
#[test]
fn materialize_closure_call_edge_keeps_the_dead_call_when_nothing_can_be_called() {
    let (world, edge) = try_materialize_closure_edge(ClosureCallEvidence::Unnamed, TransportCarrier::Absent);
    let edge = edge.expect("materialization should not fail");
    assert!(world.types().is_empty(&edge.return_ty()));
    assert_eq!(
        edge.target(),
        &CallEdge::Indirect(CallReturnFlow::NoReturn { local_source: None })
    );
}
