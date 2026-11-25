use super::*;
use crate::compiler2::semantic::{
    CallSiteResolution, CallSiteSummary, CallTargetSummary, EntryReachability, SelectedCallee,
};
use crate::compiler2::transport::{LaneId, TransportCarrier};
use crate::compiler2::{ActivationKey, FunctionId};
use crate::fz_ir::{ExternAbi, ExternTy};
use crate::telemetry::ConfiguredTelemetry;

#[test]
fn generic_extern_effects_do_not_depend_on_privileged_symbol_spellings() {
    let extern_wire = |symbol: &str| super::super::super::body::LoweredExtern {
        abi: ExternAbi::C,
        symbol: symbol.to_string(),
        params: Vec::new(),
        variadic: false,
        ret: crate::fz_ir::ExternReturn::Scalar(ExternTy::Unit),
    };
    let empty_body = LoweredBody::clauses(Vec::new(), Vec::new(), Vec::new());
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
        "fz_system_alloc_stats",
        "fz_send",
        "fz_spawn",
    ] {
        let local = local_effects(&empty_body, Some(&extern_wire(symbol)), &HashMap::default());
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
    let caller_symbol = ExecutableSymbol::new(&caller);
    let callee_symbol = ExecutableSymbol::new(&callee);
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
    let flow = exact_no_return_flow(&target);

    assert_eq!(
        flow,
        CallReturnFlow::NoReturn {
            local_source: Some(TransportPosition::ExecutableReturn {
                executable: ExecutableSymbol::new(&callee),
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
                last_resort: None,
                targets: [302, 303]
                    .into_iter()
                    .map(|function| CallTargetSummary {
                        selector: None,
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
        trimmed: Default::default(),
        input_rows: Vec::new(),
        entry_reachability: EntryReachability::new(Vec::new()),
        reachable_entries: Vec::new(),
        callsites: Vec::new(),
        value_types: call_returns.then_some((result_value, int)).into_iter().collect(),
    };
    let positions = if call_returns {
        let caller_symbol = ExecutableSymbol::new(&caller);
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
    let transport_plan = positions.into_iter().collect::<TransportLayouts>();
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
        .map(|summary| HashMap::from_iter([(callsite, summary)]))
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
        &LoweredBody::clauses(Vec::new(), Vec::new(), Vec::new()),
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

/// Pruning leaves holes in a body's call-site numbers; the pruned body answers
/// `None` for the call site it dropped and the right arguments for the rest.
#[test]
fn a_pruned_body_answers_only_for_the_call_sites_it_kept() {
    use crate::compiler2::body::{CallArg, CallSiteId, ControlEntryId, ControlEntryOrigin, LoweredClause, ValueId};
    use crate::fz_ir::OwnershipMode;
    let entry = |tail| LoweredEntry {
        span: crate::source::Span::DUMMY,
        origin: ControlEntryOrigin::Clause,
        params: Vec::new(),
        captures: Vec::new(),
        capture_owners: Vec::new(),
        physical_captures: Vec::new(),
        physical_params: Vec::new(),
        steps: Vec::new(),
        tail,
    };
    let call = |callsite: u32, arg: u32| LoweredTail::DirectCall {
        value: ValueId::from_u32(10 + callsite),
        callsite: CallSiteId::from_u32(callsite),
        callee: DirectCallee::Function(FunctionId::from_coordinate(0)),
        args: vec![CallArg {
            value: ValueId::from_u32(arg),
            ascription: None,
            ownership: OwnershipMode::Share,
        }],
        dest: ControlDestination::Return,
    };
    let (root, dropped, kept) = (
        ControlEntryId::from_u32(0),
        ControlEntryId::from_u32(1),
        ControlEntryId::from_u32(2),
    );
    let body = LoweredBody::clauses(
        vec![LoweredClause {
            span: crate::source::Span::DUMMY,
            params: Vec::new(),
            arguments: Box::default(),
            entry: root,
        }],
        vec![
            entry(LoweredTail::If {
                cond: ValueId::from_u32(0),
                then_entry: dropped,
                else_entry: kept,
            }),
            entry(call(0, 1)),
            entry(call(1, 2)),
        ],
        Vec::new(),
    );

    let pruned = prune_lowered_body(&body, &[0], &[root, kept]).body;

    assert_eq!(pruned.call_args(CallSiteId::from_u32(0)), None);
    assert_eq!(pruned.call_input_mode(CallSiteId::from_u32(0)), None);
    let args = pruned.call_args(CallSiteId::from_u32(1)).expect("the kept call site");
    assert_eq!(args.len(), 1);
    assert_eq!(args[0].value, ValueId::from_u32(2));
}

/// A receive outcome and a rescue handler are filled by the runtime, so each
/// parameter has a layout in the executable's ABI and the layout is one lane.
#[test]
fn every_parameter_a_receive_or_a_raise_hands_has_a_one_lane_layout() {
    use crate::compiler2::artifact::{BackendBody, BackendEntryOrigin};
    use crate::compiler2::{CodeSubmission, Compiler2, RootSubmission};

    const SOURCE: &str = r#"
def main() do
  send(self(), {:ok, 1})
  got = receive do
    {:ok, v} -> v
  end
  safe = try do
    raise "boom"
  rescue
    _ -> 0
  end
  got + safe
end
"#;
    let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some("handed_parameters.fz".into()),
        text: SOURCE.into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler.run_root_interp(root).expect("the program runs");
    let program = compiler.retained_backend_program(root);

    let (mut outcomes, mut handlers) = (0, 0);
    for executable in program.executables() {
        let BackendBody::Clauses { entries, .. } = &executable.body else {
            continue;
        };
        for entry in entries {
            let seen = match entry.origin {
                BackendEntryOrigin::ReceiveOutcome => &mut outcomes,
                BackendEntryOrigin::Handler => &mut handlers,
                BackendEntryOrigin::Clause
                | BackendEntryOrigin::Branch
                | BackendEntryOrigin::DeliveredResume { .. } => continue,
            };
            for param in &entry.params {
                let layout = executable
                    .abi
                    .value_layouts
                    .get(param)
                    .unwrap_or_else(|| panic!("parameter {param:?} of a {:?} entry has no layout", entry.origin));
                assert_eq!(
                    layout.reprs.len(),
                    1,
                    "parameter {param:?} of a {:?} entry is handed whole, in one lane",
                    entry.origin
                );
                *seen += 1;
            }
        }
    }
    assert!(
        outcomes > 0 && handlers > 0,
        "the program has both: {outcomes} receive, {handlers} handler parameters"
    );
}

/// The lanes of every parameter a case arm is handed, in the order the arms
/// are met, for a program whose only `case` is the one under test.
fn case_arm_parameter_lanes(arm_body: &str) -> Vec<usize> {
    use crate::compiler2::artifact::{BackendBody, BackendEntryOrigin};
    use crate::compiler2::{CodeSubmission, Compiler2, RootSubmission};

    let source = format!(
        "def pick(b) do\n  case b do\n    <<c, rest :: binary>> -> {arm_body}\n    <<>> -> 0\n  end\nend\n\
         def main(), do: pick(\"abc\")\n"
    );
    let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some("case_arm_parameters.fz".into()),
        text: source,
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler.run_root_interp(root).expect("the program runs");
    let program = compiler.retained_backend_program(root);
    let mut lanes = Vec::new();
    for executable in program.executables() {
        let BackendBody::Clauses { entries, .. } = &executable.body else {
            continue;
        };
        for entry in entries
            .iter()
            .filter(|entry| entry.origin == BackendEntryOrigin::Branch)
        {
            lanes.extend(
                entry
                    .params
                    .iter()
                    .map(|param| executable.abi.value_layouts[param].reprs.len()),
            );
        }
    }
    lanes
}

/// A rest an arm only walks arrives as a cursor of two lanes, so nothing is
/// built for it.
#[test]
fn a_case_arm_parameter_the_arm_only_walks_is_a_cursor() {
    assert_eq!(case_arm_parameter_lanes("pick(rest) + c"), [1, 2]);
}

/// A rest an arm returns is asked for whole, so it arrives in one lane.
#[test]
fn a_case_arm_parameter_the_arm_returns_is_one_lane() {
    assert_eq!(case_arm_parameter_lanes("{c, rest}"), [1, 1]);
}

/// A rest an arm never reads is not a parameter of the arm at all.
#[test]
fn a_case_arm_is_not_handed_a_rest_nothing_reads() {
    assert_eq!(case_arm_parameter_lanes("c"), [1]);
}
