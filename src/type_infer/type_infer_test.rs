use super::{Info, TypeInferOutcome, TypeInferReturnState, TypeInferStatus, infer_from_entry, solve_from_entry};
use crate::fz_ir::{Const, DeadBranch, EmitSlot, FnBuilder, FnId, Module, ModuleBuilder, Prim, Term};
use crate::telemetry::{ConfiguredTelemetry, Event, Handler, Value};
use crate::test_support::{
    entry_main_fn_id as main_id, linked_runtime_module, linked_runtime_module_unplanned, lower_frontend_module as lower,
};
use crate::types::{CallableValueKind, ClosureTarget, ClosureTypes, DefaultTypes, Ty, Types};
use std::cell::RefCell;
use std::rc::Rc;

fn linked_fixture(src: &str) -> Module {
    let tel = ConfiguredTelemetry::new();
    linked_runtime_module(src, &tel)
}

fn linked_unplanned_fixture(src: &str) -> Module {
    let mut t = crate::types::new();
    let tel = ConfiguredTelemetry::new();
    linked_runtime_module_unplanned(&mut t, src, &tel)
}

/// Test boundary helper for one activation's return type. The production API
/// returns activation facts; these focused tests need the entry activation's
/// boundary-erased `Ty` directly.
fn infer_return<T: Types<Ty = Ty> + ClosureTypes>(t: &mut T, module: &Module, fn_id: FnId, input_tys: &[Ty]) -> Ty {
    let (solver, key) = solve_from_entry(t, module, fn_id, input_tys);
    match solver.activations.get(&key).map(|activation| activation.ret.clone()) {
        Some(Info::Known(value)) => value.ty,
        _ => t.any(),
    }
}

/// Test helper for closure-call shape: applying a closure activates its body
/// with captures prepended to explicit call arguments.
fn closure_apply_contract<T: Types<Ty = Ty> + ClosureTypes>(
    t: &T,
    closure_ty: &Ty,
    arg_tys: &[Ty],
) -> Option<(FnId, Vec<Ty>)> {
    let info = t.closure_lit_parts(closure_ty)?;
    let mut inputs = info.captures;
    inputs.extend_from_slice(arg_tys);
    Some((FnId(info.target.0), inputs))
}

fn callable_kind<T: Types<Ty = Ty> + ClosureTypes>(t: &T, callable_ty: &Ty) -> Option<CallableValueKind> {
    t.closure_lit_parts(callable_ty).map(|info| info.kind)
}

#[derive(Clone, Debug, Default)]
struct TypeInferFacts {
    fn_returns: Vec<FnReturnFact>,
    activations: Vec<ActivationFact>,
    activation_edges: Vec<ActivationEdgeFact>,
    dead_arms: Vec<DeadArmFact>,
    diagnostics: Vec<DiagnosticFact>,
    dispatch_masks: Vec<DispatchMaskFact>,
}

impl TypeInferFacts {
    fn return_for_fn_named(&self, fn_name: &str) -> Ty {
        let matches: Vec<_> = self
            .fn_returns
            .iter()
            .filter(|fact| fact.fn_name == fn_name && fact.state == "known")
            .collect();
        assert_eq!(
            matches.len(),
            1,
            "expected one known fn_return event for {fn_name}, got {matches:?}"
        );
        matches[0]
            .return_ty
            .clone()
            .expect("known fn_return carries return_ty_data")
    }

    fn unsettled_fn_names(&self) -> Vec<String> {
        let mut names: Vec<_> = self
            .activations
            .iter()
            .filter(|fact| fact.state == "pending" || fact.state == "unknown")
            .map(|fact| fact.fn_name.clone())
            .collect();
        names.sort();
        names.dedup();
        names
    }

    fn has_invalid_operator_for(&self, fn_suffix: &str, op: &str) -> bool {
        self.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "type/invalid-operator"
                && diagnostic.op.as_deref() == Some(op)
                && diagnostic
                    .fn_name
                    .as_deref()
                    .is_some_and(|name| name.ends_with(fn_suffix))
        })
    }
}

#[derive(Clone, Debug)]
struct FnReturnFact {
    fn_name: String,
    state: String,
    return_ty: Option<Ty>,
}

#[derive(Clone, Debug)]
struct ActivationFact {
    activation_id: u64,
    fn_id: FnId,
    fn_name: String,
    input_count: usize,
    state: String,
    return_ty: Option<Ty>,
}

#[derive(Clone, Debug)]
struct ActivationEdgeFact {
    caller_activation_id: u64,
    caller_fn_id: FnId,
    caller_fn_name: String,
    callee_activation_id: u64,
    callee_fn_id: FnId,
    callee_fn_name: String,
    callsite_slot: String,
    callsite_span_start: u64,
    callsite_span_end: u64,
}

#[derive(Clone, Debug)]
struct DeadArmFact {
    activation_id: u64,
    fn_name: String,
    block: u64,
    branch: String,
}

#[derive(Clone, Debug)]
struct DiagnosticFact {
    code: String,
    op: Option<String>,
    fn_name: Option<String>,
}

#[derive(Clone, Debug)]
struct DispatchMaskFact {
    fn_name: String,
    arity: usize,
    dispatch_slots: Vec<usize>,
}

#[derive(Clone)]
struct TypeInferCapture(Rc<RefCell<TypeInferFacts>>);

impl TypeInferCapture {
    fn new() -> Self {
        Self(Rc::new(RefCell::new(TypeInferFacts::default())))
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(self.clone())
    }

    fn snapshot(&self) -> TypeInferFacts {
        self.0.borrow().clone()
    }
}

impl Handler for TypeInferCapture {
    fn handle(&self, ev: &Event<'_, '_, '_>) {
        let mut facts = self.0.borrow_mut();
        match ev.name {
            ["fz", "type_infer", "fn_return"] => {
                if let (Some(fn_name), Some(state)) =
                    (event_metadata_str(ev, "fn_name"), event_metadata_str(ev, "state"))
                {
                    facts.fn_returns.push(FnReturnFact {
                        fn_name,
                        state,
                        return_ty: event_metadata_ty(ev, "return_ty_data"),
                    });
                }
            }
            ["fz", "type_infer", "activation"] => {
                if let (Some(activation_id), Some(fn_name), Some(fn_id), Some(input_count), Some(state)) = (
                    event_metadata_u64(ev, "activation_id"),
                    event_metadata_str(ev, "fn_name"),
                    event_metadata_u64(ev, "fn_id"),
                    event_metadata_u64(ev, "input_count"),
                    event_metadata_str(ev, "state"),
                ) {
                    facts.activations.push(ActivationFact {
                        activation_id,
                        fn_id: FnId(fn_id as u32),
                        fn_name,
                        input_count: input_count as usize,
                        state,
                        return_ty: event_metadata_ty(ev, "return_ty_data"),
                    });
                }
            }
            ["fz", "type_infer", "activation_edge"] => {
                if let (
                    Some(caller_activation_id),
                    Some(caller_fn_name),
                    Some(caller_fn_id),
                    Some(callee_activation_id),
                    Some(callee_fn_name),
                    Some(callee_fn_id),
                    Some(callsite_slot),
                    Some(callsite_span_start),
                    Some(callsite_span_end),
                ) = (
                    event_metadata_u64(ev, "caller_activation_id"),
                    event_metadata_str(ev, "caller_fn_name"),
                    event_metadata_u64(ev, "caller_fn_id"),
                    event_metadata_u64(ev, "callee_activation_id"),
                    event_metadata_str(ev, "callee_fn_name"),
                    event_metadata_u64(ev, "callee_fn_id"),
                    event_metadata_str(ev, "callsite_slot"),
                    event_metadata_u64(ev, "callsite_span_start"),
                    event_metadata_u64(ev, "callsite_span_end"),
                ) {
                    facts.activation_edges.push(ActivationEdgeFact {
                        caller_activation_id,
                        caller_fn_id: FnId(caller_fn_id as u32),
                        caller_fn_name,
                        callee_activation_id,
                        callee_fn_id: FnId(callee_fn_id as u32),
                        callee_fn_name,
                        callsite_slot,
                        callsite_span_start,
                        callsite_span_end,
                    });
                }
            }
            ["fz", "type_infer", "diagnostic"] => {
                if let Some(code) = event_metadata_str(ev, "code") {
                    facts.diagnostics.push(DiagnosticFact {
                        code,
                        op: event_metadata_str(ev, "op"),
                        fn_name: event_metadata_str(ev, "fn_name"),
                    });
                }
            }
            ["fz", "type_infer", "dispatch_mask"] => {
                if let (Some(fn_name), Some(arity)) =
                    (event_metadata_str(ev, "fn_name"), event_metadata_u64(ev, "arity"))
                {
                    let dispatch_slots = match ev.metadata.get("dispatch_slots") {
                        Some(Value::StrSeq(v)) => v.iter().filter_map(|s| s.parse().ok()).collect(),
                        _ => Vec::new(),
                    };
                    facts.dispatch_masks.push(DispatchMaskFact {
                        fn_name,
                        arity: arity as usize,
                        dispatch_slots,
                    });
                }
            }
            ["fz", "type_infer", "dead_arm"] => {
                if let (Some(activation_id), Some(fn_name), Some(block), Some(branch)) = (
                    event_metadata_u64(ev, "activation_id"),
                    event_metadata_str(ev, "fn_name"),
                    event_metadata_u64(ev, "block"),
                    event_metadata_str(ev, "branch"),
                ) {
                    facts.dead_arms.push(DeadArmFact {
                        activation_id,
                        fn_name,
                        block,
                        branch,
                    });
                }
            }
            _ => {}
        }
    }
}

struct TelemetryReport {
    outcome: TypeInferOutcome,
    facts: TypeInferFacts,
}

impl TelemetryReport {
    fn unsettled_fn_names(&self) -> Vec<String> {
        self.facts.unsettled_fn_names()
    }
}

fn infer_report_via_main(t: &mut DefaultTypes, module: &Module) -> TelemetryReport {
    let tel = ConfiguredTelemetry::new();
    let cap = TypeInferCapture::new();
    tel.attach(&["fz", "type_infer"], cap.handler());
    let outcome = infer_from_entry(t, module, main_id(module), &[], &tel);
    TelemetryReport {
        outcome,
        facts: cap.snapshot(),
    }
}

fn infer_fn_via_main(module: &Module, fn_name: &str) -> Ty {
    let mut t = crate::types::new();
    let report = infer_report_via_main(&mut t, module);
    report.facts.return_for_fn_named(fn_name)
}

fn infer_entry_return_via_main(module: &Module) -> Ty {
    let mut t = crate::types::new();
    infer_return(&mut t, module, main_id(module), &[])
}

/// fz-y6w.2 — the dispatch-subject mask is the precision boundary for
/// activation convergence. `partition(p, list, lo, hi)` selects clauses on
/// the list (`[]` vs `[h|t]`) and on the pivot guard (`h < p`), but never on
/// the `lo`/`hi` accumulators — so those slots are convergeable and the mask
/// must mark only the pivot and list slots as dispatch subjects.
#[test]
fn partition_dispatch_mask_excludes_accumulators() {
    let module = linked_fixture(include_str!("../../fixtures/quicksort/input.fz"));
    let partition = module
        .fn_by_name("partition")
        .expect("quicksort fixture defines partition");
    assert_eq!(
        partition.dispatch_subject_slots(),
        vec![true, true, false, false],
        "pivot (0) and matched list (1) drive dispatch; lo (2) and hi (3) accumulators do not"
    );
}

/// fz-y6w.2 — the same fact, observed on the production path: the solver
/// computes the mask per activated fn and surfaces it as telemetry. T3
/// reads this mask to fold the accumulator slots together.
#[test]
fn partition_dispatch_mask_is_emitted() {
    let module = linked_fixture(include_str!("../../fixtures/quicksort/input.fz"));
    let mut t = crate::types::new();
    let report = infer_report_via_main(&mut t, &module);
    let partition = report
        .facts
        .dispatch_masks
        .iter()
        .find(|fact| fact.fn_name == "partition")
        .expect("partition activates, so its dispatch mask is emitted");
    assert_eq!(partition.arity, 4);
    assert_eq!(
        partition.dispatch_slots,
        vec![0, 1],
        "only the pivot and matched-list slots drive dispatch"
    );
}

fn event_metadata_str(ev: &Event<'_, '_, '_>, key: &str) -> Option<String> {
    match ev.metadata.get(key)? {
        Value::Str(value) => Some(value.to_string()),
        _ => None,
    }
}

fn event_metadata_ty(ev: &Event<'_, '_, '_>, key: &str) -> Option<Ty> {
    ev.metadata.get(key)?.downcast_ref::<Ty>().cloned()
}

fn event_metadata_u64(ev: &Event<'_, '_, '_>, key: &str) -> Option<u64> {
    match ev.metadata.get(key)? {
        Value::U64(value) => Some(*value),
        _ => None,
    }
}

fn emit_slot_name(slot: EmitSlot) -> &'static str {
    match slot {
        EmitSlot::Direct => "direct",
        EmitSlot::Cont => "cont",
        EmitSlot::ClosureCall => "closure_call",
        EmitSlot::CallableBoundary => "callable_boundary",
    }
}

fn return_state_name(state: &TypeInferReturnState) -> &'static str {
    match state {
        TypeInferReturnState::Pending => "pending",
        TypeInferReturnState::Unknown => "unknown",
        TypeInferReturnState::NoReturn => "no_return",
        TypeInferReturnState::Known(_) => "known",
    }
}

/// At the fixpoint of a supported program, every reached function has a known
/// return or no return. A surviving pending/unknown return means a dependency
/// never settled or a live construct is still unmodeled.
#[test]
fn fixpoint_leaves_no_reached_fn_unknown() {
    for (name, src) in [
        ("add", include_str!("fixtures/add.fz")),
        ("fold_tail", include_str!("fixtures/fold_tail.fz")),
        ("fold_nontail", include_str!("fixtures/fold_nontail.fz")),
        ("fold_capture_int", include_str!("fixtures/fold_capture_int.fz")),
        ("fold_capture_closure", include_str!("fixtures/fold_capture_closure.fz")),
        ("fold_state_machine", include_str!("fixtures/fold_state_machine.fz")),
    ] {
        let module = lower(src);
        let mut t = crate::types::new();
        let report = infer_report_via_main(&mut t, &module);
        assert_eq!(report.outcome.status, TypeInferStatus::Complete);
        let unsettled = report.unsettled_fn_names();
        assert!(
            unsettled.is_empty(),
            "{name}: reached fns left Pending/Unknown at fixpoint: {unsettled:?}"
        );
    }
}

#[test]
fn runtime_graph_enum_ops_settle_to_int() {
    let cases = [
        ("list lambda", "Enum.reduce", include_str!("fixtures/enum_reduce.fz")),
        (
            "named-fn ref",
            "Enum.reduce",
            include_str!("fixtures/enum_reduce_named_ref_ok.fz"),
        ),
        ("count", "Enum.count", include_str!("fixtures/enum_count.fz")),
        (
            "range reduce",
            "Enum.reduce",
            include_str!("fixtures/enum_reduce_range.fz"),
        ),
    ];
    let mut t = crate::types::new();
    let int = t.int();
    for (label, entry, src) in cases {
        let module = linked_fixture(src);
        let ret = infer_fn_via_main(&module, entry);
        assert!(
            t.is_equivalent(&ret, &int),
            "{label}: {entry} should settle to int, got {ret:?}"
        );
    }
}

#[test]
fn enum_reduce_operator_refs_settle_through_kernel_specs() {
    let module = linked_fixture(include_str!("fixtures/enum_reduce_operator_ref.fz"));
    let mut t = crate::types::new();
    let int = t.int();
    let expected = t.tuple(&[int.clone(), int]);
    let report = infer_report_via_main(&mut t, &module);

    assert_eq!(report.outcome.status, TypeInferStatus::Complete);
    let ret = report.facts.return_for_fn_named("main");
    assert!(
        t.is_equivalent(&ret, &expected),
        "qualified and bare operator refs should both settle to int, got {ret:?}"
    );
}

#[test]
fn enum_reduce_erased_list_operator_ref_preserves_concrete_caller_witness() {
    let module = linked_fixture(include_str!("fixtures/enum_reduce_erased_list_operator_ref.fz"));
    let mut t = crate::types::new();
    let int = t.int();
    let non_empty_ints = t.non_empty_list(int.clone());
    let report = infer_report_via_main(&mut t, &module);

    assert_eq!(report.outcome.status, TypeInferStatus::Complete);
    let main_ret = report.facts.return_for_fn_named("main");
    assert!(
        t.is_equivalent(&main_ret, &int),
        "erased list surface type should still settle main to int from the concrete caller witness, got {main_ret:?}"
    );

    let test_ret = report.facts.return_for_fn_named("test");
    assert!(
        t.is_equivalent(&test_ret, &int),
        "test/1 should settle to int despite the broad declared surface type, got {test_ret:?}"
    );

    let test_fact = report
        .outcome
        .activations
        .iter()
        .find(|fact| {
            module.fn_by_id(fact.fn_id).name == "test"
                && fact.input_tys.len() == 1
                && matches!(
                    &fact.return_state,
                    TypeInferReturnState::Known(ret) if t.is_equivalent(ret, &int)
                )
        })
        .unwrap_or_else(|| {
            panic!(
                "test/1 should have a known int activation from the concrete caller witness; got {:?}",
                report
                    .outcome
                    .activations
                    .iter()
                    .filter(|fact| module.fn_by_id(fact.fn_id).name == "test")
                    .collect::<Vec<_>>()
            )
        });
    assert!(
        t.is_subtype(&test_fact.input_tys[0], &non_empty_ints),
        "test/1 activation should keep the concrete nonempty list(int) caller witness, got {:?}",
        test_fact.input_tys
    );
}

#[test]
fn mixed_enum_take_calls_preserve_list_and_range_activations() {
    let module = linked_fixture(
        r#"
fn main() do
  xs = [1, 2, 3, 4, 5]
  range = 1..5
  dbg(Enum.take(xs, 3))
  dbg(Enum.take(xs, 0))
  dbg(Enum.take(xs, 9))
  dbg(Enum.take(xs, -2))
  dbg(Enum.take(range, -2))
end
"#,
    );
    let mut t = crate::types::new();
    let report = infer_report_via_main(&mut t, &module);
    let range = t.opaque_of("impl-target::Range");
    let int = t.int();
    let list_int = t.list(int);

    let take_facts = report
        .facts
        .activations
        .iter()
        .filter(|fact| fact.fn_name == "Enum.take")
        .collect::<Vec<_>>();
    assert!(
        take_facts
            .iter()
            .any(|fact| { fact.return_ty.as_ref().is_some_and(|ret| t.is_subtype(ret, &list_int)) }),
        "mixed Enum.take calls should infer a successful list-returning activation: {take_facts:?}"
    );
    assert!(
        report.outcome.activations.iter().any(|fact| {
            module.fn_by_id(fact.fn_id).name == "Enum.take"
                && fact.input_tys.first().is_some_and(|ty| t.is_equivalent(ty, &range))
        }),
        "mixed Enum.take calls should activate the range call path: {:?}",
        report.outcome.activations
    );
}

#[test]
fn receive_clause_body_keeps_typed_capture_and_settles_caller_return() {
    let module = linked_fixture(include_str!("fixtures/receive_cont_capture.fz"));
    let mut t = crate::types::new();
    let int = t.int();
    let any = t.any();
    let parent_ret = t.tuple(&[int.clone(), any.clone()]);
    let main_ret = t.tuple(std::slice::from_ref(&parent_ret));
    let report = infer_report_via_main(&mut t, &module);

    assert_eq!(
        report.outcome.status,
        TypeInferStatus::Complete,
        "catch-all selective receive should infer through its clause body instead of leaving the activation graph unresolved: activations={:?}",
        report
            .outcome
            .activations
            .iter()
            .map(|fact| (
                module.fn_by_id(fact.fn_id).name.as_str(),
                fact.input_tys.clone(),
                &fact.return_state
            ))
            .collect::<Vec<_>>()
    );

    let parent_fact = report
        .outcome
        .activations
        .iter()
        .find(|fact| {
            module.fn_by_id(fact.fn_id).name == "parent"
                && fact.input_tys.len() == 1
                && matches!(
                    &fact.return_state,
                    TypeInferReturnState::Known(ret) if t.is_equivalent(ret, &parent_ret)
                )
        })
        .unwrap_or_else(|| {
            panic!(
                "parent/1 should settle to {{int, any}} from the typed capture threaded through the receive clause body; got {:?}",
                report
                    .outcome
                    .activations
                    .iter()
                    .filter(|fact| module.fn_by_id(fact.fn_id).name == "parent")
                    .collect::<Vec<_>>()
            )
        });

    let main_fact = report
        .outcome
        .activations
        .iter()
        .find(|fact| {
            module.fn_by_id(fact.fn_id).name == "main"
                && fact.input_tys.is_empty()
                && matches!(
                    &fact.return_state,
                    TypeInferReturnState::Known(ret) if t.is_equivalent(ret, &main_ret)
                )
        })
        .unwrap_or_else(|| {
            panic!(
                "main/0 should receive the known parent/1 return through its continuation, got {:?}",
                report
                    .outcome
                    .activations
                    .iter()
                    .filter(|fact| module.fn_by_id(fact.fn_id).name == "main")
                    .collect::<Vec<_>>()
            )
        });

    assert!(
        report.outcome.edges.iter().any(|edge| {
            edge.caller_activation_id == parent_fact.activation_id
                && edge.callsite.callsite.slot == EmitSlot::Cont
                && module.fn_by_id(edge.callee_fn_id).name == "rx_clause_0_body"
        }),
        "parent/1 should expose a Cont activation edge into the selective-receive clause body; edges={:?}",
        report
            .outcome
            .edges
            .iter()
            .map(|edge| (
                module.fn_by_id(edge.caller_fn_id).name.as_str(),
                module.fn_by_id(edge.callee_fn_id).name.as_str(),
                edge.callsite.callsite.slot
            ))
            .collect::<Vec<_>>()
    );

    assert!(
        report.outcome.edges.iter().any(|edge| {
            edge.caller_activation_id == main_fact.activation_id
                && edge.callsite.callsite.slot == EmitSlot::Cont
                && module.fn_by_id(edge.callee_fn_id).name.starts_with("k_")
        }),
        "main/0 should keep the direct-call continuation that receives parent/1's return; edges={:?}",
        report
            .outcome
            .edges
            .iter()
            .map(|edge| (
                module.fn_by_id(edge.caller_fn_id).name.as_str(),
                module.fn_by_id(edge.callee_fn_id).name.as_str(),
                edge.callsite.callsite.slot
            ))
            .collect::<Vec<_>>()
    );
}

#[test]
fn linked_runtime_spawn_receive_converges_through_extern_return_contract() {
    let module = linked_fixture(include_str!("fixtures/spawn_receive_capture.fz"));
    let mut t = crate::types::new();
    let any = t.any();
    let report = infer_report_via_main(&mut t, &module);
    let unsettled = report.unsettled_fn_names();
    let unsettled_bodies = unsettled
        .iter()
        .map(|name| {
            let body = module
                .fns
                .iter()
                .find(|f| f.name == *name)
                .map(|f| format!("{f}"))
                .unwrap_or_else(|| "<missing>".to_string());
            (name.clone(), body)
        })
        .collect::<Vec<_>>();

    assert_eq!(
        report.outcome.status,
        TypeInferStatus::Complete,
        "linked runtime graph should still infer parent/1 through spawn + receive after pre-plan rewrites: unsettled={unsettled:?}; unsettled_bodies={unsettled_bodies:?}; activations={:?}; edges={:?}; parent=\n{}\nmain=\n{}",
        report
            .outcome
            .activations
            .iter()
            .map(|fact| (
                module.fn_by_id(fact.fn_id).name.as_str(),
                fact.input_tys.clone(),
                &fact.return_state
            ))
            .collect::<Vec<_>>(),
        report
            .outcome
            .edges
            .iter()
            .map(|edge| (
                module.fn_by_id(edge.caller_fn_id).name.as_str(),
                module.fn_by_id(edge.callee_fn_id).name.as_str(),
                edge.callsite.callsite.slot
            ))
            .collect::<Vec<_>>(),
        module
            .fns
            .iter()
            .find(|f| f.name == "parent")
            .map(|f| format!("{f}"))
            .unwrap_or_else(|| "<missing parent>".to_string()),
        module
            .fns
            .iter()
            .find(|f| f.name == "main")
            .map(|f| format!("{f}"))
            .unwrap_or_else(|| "<missing main>".to_string())
    );

    let parent_fact = report
        .outcome
        .activations
        .iter()
        .find(|fact| {
            module.fn_by_id(fact.fn_id).name == "parent"
                && fact.input_tys.len() == 1
                && fact.input_tys.first().is_some_and(|ty| t.is_integer(ty))
                && matches!(
                    &fact.return_state,
                    TypeInferReturnState::Known(ret) if t.is_equivalent(ret, &any)
                )
        })
        .unwrap_or_else(|| {
            panic!(
                "parent/1 should settle to a known opaque receive result on the linked runtime graph, got {:?}",
                report
                    .outcome
                    .activations
                    .iter()
                    .filter(|fact| module.fn_by_id(fact.fn_id).name == "parent")
                    .collect::<Vec<_>>()
            )
        });

    assert!(
        report.outcome.edges.iter().any(|edge| {
            edge.caller_activation_id == parent_fact.activation_id
                && edge.callsite.callsite.slot == EmitSlot::Direct
                && module.fn_by_id(edge.callee_fn_id).name == "Kernel.spawn"
        }),
        "parent/1 should still call Kernel.spawn/1 on the linked runtime graph; edges={:?}",
        report
            .outcome
            .edges
            .iter()
            .map(|edge| (
                module.fn_by_id(edge.caller_fn_id).name.as_str(),
                module.fn_by_id(edge.callee_fn_id).name.as_str(),
                edge.callsite.callsite.slot
            ))
            .collect::<Vec<_>>()
    );

    assert!(
        report.outcome.edges.iter().any(|edge| {
            edge.caller_activation_id == parent_fact.activation_id
                && edge.callsite.callsite.slot == EmitSlot::Cont
                && module.fn_by_id(edge.callee_fn_id).name.starts_with("k_")
        }),
        "parent/1 should keep the post-spawn continuation carrier alive after pre-plan rewrites; edges={:?}",
        report
            .outcome
            .edges
            .iter()
            .map(|edge| (
                module.fn_by_id(edge.caller_fn_id).name.as_str(),
                module.fn_by_id(edge.callee_fn_id).name.as_str(),
                edge.callsite.callsite.slot
            ))
            .collect::<Vec<_>>()
    );

    assert!(
        report.outcome.edges.iter().any(|edge| {
            edge.callsite.callsite.slot == EmitSlot::Cont
                && module.fn_by_id(edge.callee_fn_id).name == "rx_clause_0_body"
        }),
        "linked runtime graph should keep the selective-receive clause-body edge alive after pre-plan rewrites; edges={:?}",
        report
            .outcome
            .edges
            .iter()
            .map(|edge| (
                module.fn_by_id(edge.caller_fn_id).name.as_str(),
                module.fn_by_id(edge.callee_fn_id).name.as_str(),
                edge.callsite.callsite.slot
            ))
            .collect::<Vec<_>>()
    );
}

#[test]
fn linked_runtime_plain_spawn_surfaces_callable_boundary_to_child() {
    let module = linked_fixture(include_str!("fixtures/spawn_plain.fz"));
    let mut t = crate::types::new();
    let nil = t.nil();
    let report = infer_report_via_main(&mut t, &module);

    assert_eq!(
        report.outcome.status,
        TypeInferStatus::Complete,
        "plain spawn should settle through the linked runtime graph: activations={:?}; edges={:?}",
        report
            .outcome
            .activations
            .iter()
            .map(|fact| (
                module.fn_by_id(fact.fn_id).name.as_str(),
                fact.input_tys.clone(),
                &fact.return_state
            ))
            .collect::<Vec<_>>(),
        report
            .outcome
            .edges
            .iter()
            .map(|edge| (
                module.fn_by_id(edge.caller_fn_id).name.as_str(),
                module.fn_by_id(edge.callee_fn_id).name.as_str(),
                edge.callsite.callsite.slot
            ))
            .collect::<Vec<_>>()
    );

    let child_fact = report
        .outcome
        .activations
        .iter()
        .find(|fact| {
            module.fn_by_id(fact.fn_id).name == "child"
                && fact.input_tys.is_empty()
                && matches!(
                    &fact.return_state,
                    TypeInferReturnState::Known(ret) if t.is_equivalent(ret, &nil)
                )
        })
        .unwrap_or_else(|| {
            panic!(
                "plain spawn should activate child/0 with known nil return, got {:?}",
                report
                    .outcome
                    .activations
                    .iter()
                    .filter(|fact| module.fn_by_id(fact.fn_id).name == "child")
                    .collect::<Vec<_>>()
            )
        });

    assert!(
        report.outcome.edges.iter().any(|edge| {
            module.fn_by_id(edge.caller_fn_id).name == "Kernel.spawn"
                && edge.callee_activation_id == child_fact.activation_id
                && edge.callsite.callsite.slot == EmitSlot::CallableBoundary
        }),
        "plain spawn should surface a callable-boundary edge from Kernel.spawn/1 to child/0; edges={:?}",
        report
            .outcome
            .edges
            .iter()
            .map(|edge| (
                module.fn_by_id(edge.caller_fn_id).name.as_str(),
                module.fn_by_id(edge.callee_fn_id).name.as_str(),
                edge.callsite.callsite.slot
            ))
            .collect::<Vec<_>>()
    );
}

#[test]
fn string_literal_argument_types_as_str_t() {
    let module = lower("fn id(x), do: x\nfn main(), do: id(\"hi\")");
    let mut t = crate::types::new();
    let str_t = t.str_t();
    let report = infer_report_via_main(&mut t, &module);

    assert_eq!(
        report.outcome.status,
        TypeInferStatus::Complete,
        "string-literal call should settle through const bitstring typing: activations={:?}; edges={:?}",
        report
            .outcome
            .activations
            .iter()
            .map(|fact| (
                module.fn_by_id(fact.fn_id).name.as_str(),
                fact.input_tys.clone(),
                &fact.return_state
            ))
            .collect::<Vec<_>>(),
        report
            .outcome
            .edges
            .iter()
            .map(|edge| (
                module.fn_by_id(edge.caller_fn_id).name.as_str(),
                module.fn_by_id(edge.callee_fn_id).name.as_str(),
                edge.callsite.callsite.slot
            ))
            .collect::<Vec<_>>()
    );

    let id_return = report.facts.return_for_fn_named("id");
    assert!(
        t.is_equivalent(&id_return, &str_t),
        "string literal should flow through direct calls as str_t(); got {}",
        t.display(&id_return)
    );
}

#[test]
fn enum_reduce_runtime_graph_settles() {
    let module = linked_fixture(include_str!("fixtures/enum_reduce.fz"));
    let mut t = crate::types::new();
    let int = t.int();

    let reduce_ret = infer_fn_via_main(&module, "Enum.reduce");
    assert!(
        t.is_equivalent(&reduce_ret, &int),
        "Enum.reduce([1,2,3],0,+) should settle to int, got {reduce_ret:?}"
    );

    let done = {
        let a = t.atom_lit("done");
        let i = t.int();
        t.tuple(&[a, i])
    };
    let list_reduce_ret = infer_fn_via_main(&module, "Enumerable.List.reduce");
    assert!(
        t.is_equivalent(&list_reduce_ret, &done),
        "Enumerable.List.reduce should settle to {{:done,int}} for an int-returning reducer, got {list_reduce_ret:?}"
    );
}

#[test]
fn outcome_exposes_activation_facts_as_production_data() {
    let module = linked_fixture(include_str!("fixtures/enum_reduce.fz"));
    let mut t = crate::types::new();
    let int = t.int();
    let report = infer_report_via_main(&mut t, &module);

    assert_eq!(report.outcome.status, TypeInferStatus::Complete);
    assert_eq!(
        report.outcome.activations.len(),
        report.facts.activations.len(),
        "returned activation facts and activation telemetry should describe the same reached cells"
    );
    assert_eq!(
        report.outcome.edges.len(),
        report.facts.activation_edges.len(),
        "returned activation edges and activation-edge telemetry should describe the same graph"
    );

    for fact in &report.outcome.activations {
        assert!(
            report.facts.activations.iter().any(|event| {
                event.activation_id == fact.activation_id.0
                    && event.fn_id == fact.fn_id
                    && event.input_count == fact.input_tys.len()
                    && event.state == return_state_name(&fact.return_state)
            }),
            "activation fact should be observable through telemetry: {fact:?}"
        );
    }
    for edge in &report.outcome.edges {
        assert!(
            report.facts.activation_edges.iter().any(|event| {
                event.caller_activation_id == edge.caller_activation_id.0
                    && event.caller_fn_id == edge.caller_fn_id
                    && event.callee_activation_id == edge.callee_activation_id.0
                    && event.callee_fn_id == edge.callee_fn_id
                    && event.callsite_slot == emit_slot_name(edge.callsite.callsite.slot)
                    && event.callsite_span_start == edge.callsite.span_start
                    && event.callsite_span_end == edge.callsite.span_end
                    && !event.caller_fn_name.is_empty()
                    && !event.callee_fn_name.is_empty()
            }),
            "activation edge should be observable through telemetry: {edge:?}"
        );
    }

    let reduce_fact = report
        .outcome
        .activations
        .iter()
        .find(|fact| {
            module.fn_by_id(fact.fn_id).name == "Enum.reduce"
                && fact.input_tys.len() == 3
                && matches!(
                    &fact.return_state,
                    TypeInferReturnState::Known(ret) if t.is_equivalent(ret, &int)
                )
        })
        .unwrap_or_else(|| {
            panic!(
                "Enum.reduce activation should be returned as known int; got {:?}",
                report
                    .outcome
                    .activations
                    .iter()
                    .filter(|fact| module.fn_by_id(fact.fn_id).name == "Enum.reduce")
                    .collect::<Vec<_>>()
            )
        });

    assert!(
        t.is_equivalent(&reduce_fact.input_tys[1], &int),
        "Enum.reduce activation should carry the concrete accumulator input, got {:?}",
        reduce_fact.input_tys
    );
    assert!(
        report.facts.activations.iter().any(|event| {
            event.activation_id == reduce_fact.activation_id.0
                && event.fn_id == reduce_fact.fn_id
                && event.input_count == reduce_fact.input_tys.len()
                && event.state == "known"
                && event.return_ty.as_ref().is_some_and(|ty| t.is_equivalent(ty, &int))
        }),
        "known activation return should be visible through telemetry too"
    );
    assert!(
        report.outcome.edges.iter().any(|edge| {
            module.fn_by_id(edge.caller_fn_id).name == "Enum.reduce"
                && module.fn_by_id(edge.callee_fn_id).name == "Enumerable.List.reduce"
                && edge.callsite.callsite.slot == EmitSlot::Direct
        }),
        "Enum.reduce should expose the activation edge it used to reach Enumerable.List.reduce; edges={:?}",
        report
            .outcome
            .edges
            .iter()
            .map(|edge| (
                module.fn_by_id(edge.caller_fn_id).name.as_str(),
                module.fn_by_id(edge.callee_fn_id).name.as_str()
            ))
            .collect::<Vec<_>>()
    );
    assert!(
        report.outcome.dead_arms.iter().all(|dead_arm| {
            report.facts.dead_arms.iter().any(|event| {
                event.activation_id == dead_arm.activation_id.0
                    && event.block == dead_arm.block_id.0 as u64
                    && event.branch
                        == match dead_arm.branch {
                            DeadBranch::Then => "then",
                            DeadBranch::Else => "else",
                        }
                    && !event.fn_name.is_empty()
            })
        }),
        "dead-arm facts should also be observable through telemetry: {:?}",
        report.outcome.dead_arms
    );
}

#[test]
fn invalid_named_reduce_reducer_emits_operator_diagnostic() {
    let module = linked_unplanned_fixture(include_str!("fixtures/enum_reduce_named_ref.fz"));
    let mut t = crate::types::new();
    let report = infer_report_via_main(&mut t, &module);
    assert_eq!(report.outcome.status, TypeInferStatus::Invalid);
    assert!(
        report.facts.has_invalid_operator_for("broken_reducer", "+"),
        "expected invalid + diagnostic for Main.broken_reducer/2, got {:?}",
        report.facts.diagnostics
    );
}

#[test]
fn kernel_declares_the_arithmetic_operator_surface() {
    let module = lower("fn main(), do: 1 + 2");
    let mut missing = Vec::new();
    for name in ["Kernel.+", "Kernel.-", "Kernel.*", "Kernel./", "Kernel.%"] {
        let Some(f) = module.fn_by_name(name) else {
            missing.push(format!("{name}/2"));
            continue;
        };
        match module.declared_specs.get(&f.id) {
            Some(specs) if specs.arrows.len() == 4 => {}
            Some(specs) => missing.push(format!("{name}/2 has {} arrows", specs.arrows.len())),
            None => missing.push(format!("{name}/2 has no declared specs")),
        }
    }
    assert!(
        missing.is_empty(),
        "Kernel arithmetic operators should expose the four concrete int/float arrows: {missing:?}"
    );
}

#[test]
fn arithmetic_binops_infer_from_kernel_operator_specs() {
    let mut t = crate::types::new();
    let module = lower("fn main() do\n  {1 + 2, 4 - 1, 2 * 3, 4 / 2, 5 % 2, 1 + 2.0, 4.0 - 1, 2 * 3.0}\nend");
    let ret = infer_entry_return_via_main(&module);
    let int = t.int();
    let float = t.float();
    let expected = t.tuple(&[
        int.clone(),
        int.clone(),
        int.clone(),
        int.clone(),
        int,
        float.clone(),
        float.clone(),
        float,
    ]);
    assert!(
        t.is_equivalent(&ret, &expected),
        "arithmetic operators should be typed by Kernel operator specs, got {ret:?}"
    );
}

#[test]
fn arithmetic_binops_union_successful_returns_for_any_operands() {
    let module = lower("fn add(left, right), do: left + right");
    let add_id = module.fn_by_name("add").expect("add fn").id;
    let tel = ConfiguredTelemetry::new();
    let cap = TypeInferCapture::new();
    tel.attach(&["fz", "type_infer"], cap.handler());

    let mut t = crate::types::new();
    let any = t.any();
    let int = t.int();
    let float = t.float();
    let success = t.union(int.clone(), float);
    let outcome = infer_from_entry(&mut t, &module, add_id, &[any, int], &tel);

    assert_eq!(outcome.status, TypeInferStatus::Complete);
    assert!(
        outcome.activations.iter().any(|fact| {
            fact.fn_id == add_id
                && matches!(
                    &fact.return_state,
                    TypeInferReturnState::Known(ret) if t.is_equivalent(ret, &success)
                )
        }),
        "any + integer should infer the union of successful operator returns: {:?}",
        outcome.activations
    );
    assert!(
        !cap.snapshot().has_invalid_operator_for("add", "+"),
        "broad but successful operator input should not be reported as impossible"
    );
}

#[test]
fn add_infers_int_via_harness() {
    let mut t = crate::types::new();
    let module = lower(include_str!("fixtures/add.fz"));
    let add_id = module.fn_by_name("add").expect("add fn").id;
    let int = t.int();
    let ret = infer_return(&mut t, &module, add_id, &[int.clone(), int.clone()]);
    assert!(t.is_equivalent(&ret, &int), "add(int, int) should infer int");
}

#[test]
fn infer_return_erases_residual_unknown_to_any_at_boundary() {
    let mut b = FnBuilder::new(FnId(0), "unknown_expr");
    let entry = b.block(vec![]);
    // Bitstrings are modeled as `str_t()` now; use an intentionally
    // unmodeled reader init to keep the body result `Unknown`.
    let bits = b.let_(entry, Prim::MakeBitstring(vec![]));
    let value = b.let_(entry, Prim::BitReaderInit(bits));
    b.set_terminator(entry, Term::Return(value));

    let mut mb = ModuleBuilder::new();
    mb.add_fn(b.build());
    let module = mb.build();

    let mut t = crate::types::new();
    let ret = infer_return(&mut t, &module, FnId(0), &[]);
    let any = t.any();
    assert!(
        t.is_equivalent(&ret, &any),
        "a live value the engine cannot prove should erase to any at the Ty boundary, got {ret:?}"
    );
}

#[test]
fn live_unknown_branch_survives_control_join_to_boundary() {
    let mut b = FnBuilder::new(FnId(0), "branch_unknown");
    let cond = b.fresh_var();
    let entry = b.block(vec![cond]);
    let unknown_b = b.block(vec![]);
    let known_b = b.block(vec![]);
    // The unknown arm must stay live through the join until the public
    // boundary erases it, so use the same intentionally unmodeled prim.
    let bits = b.let_(unknown_b, Prim::MakeBitstring(vec![]));
    let unknown = b.let_(unknown_b, Prim::BitReaderInit(bits));
    b.set_terminator(unknown_b, Term::Return(unknown));
    let one = b.let_(known_b, Prim::Const(Const::Int(1)));
    b.set_terminator(known_b, Term::Return(one));
    b.set_terminator(entry, Term::if_user(cond, unknown_b, known_b));

    let mut mb = ModuleBuilder::new();
    mb.add_fn(b.build());
    let module = mb.build();

    let mut t = crate::types::new();
    let bool_ty = t.bool();
    let ret = infer_return(&mut t, &module, FnId(0), &[bool_ty]);
    let any = t.any();
    assert!(
        t.is_equivalent(&ret, &any),
        "a live unknown arm must not be displaced by a known sibling arm, got {ret:?}"
    );
}

#[test]
fn halt_branch_contributes_no_return_value_to_control_join() {
    let mut b = FnBuilder::new(FnId(0), "branch_halt");
    let cond = b.fresh_var();
    let entry = b.block(vec![cond]);
    let halt_b = b.block(vec![]);
    let return_b = b.block(vec![]);
    let halted = b.let_(halt_b, Prim::Const(Const::Int(1)));
    b.set_terminator(halt_b, Term::Halt(halted));
    let returned = b.let_(return_b, Prim::Const(Const::Int(2)));
    b.set_terminator(return_b, Term::Return(returned));
    b.set_terminator(entry, Term::if_user(cond, halt_b, return_b));

    let mut mb = ModuleBuilder::new();
    mb.add_fn(b.build());
    let module = mb.build();

    let mut t = crate::types::new();
    let bool_ty = t.bool();
    let ret = infer_return(&mut t, &module, FnId(0), &[bool_ty]);
    let int = t.int();
    assert!(
        t.is_equivalent(&ret, &int),
        "a halt arm contributes no function return value; sibling return should remain int, got {ret:?}"
    );
}

#[test]
fn direct_calls_instantiate_polymorphic_identity_per_callsite() {
    let mut t = crate::types::new();
    let module = lower(include_str!("fixtures/poly_id.fz"));
    let ret = infer_entry_return_via_main(&module);
    let expected = {
        let int = t.int();
        let ok = t.atom_lit("ok");
        t.tuple(&[int, ok])
    };
    assert!(
        t.is_equivalent(&ret, &expected),
        "main should keep id(1) and id(:ok) as separate instantiations, got {ret:?}"
    );
}

#[test]
fn named_refs_instantiate_polymorphic_identity_per_callsite() {
    let mut t = crate::types::new();
    let module = lower(include_str!("fixtures/poly_named_ref.fz"));
    let ret = infer_fn_via_main(&module, "main");
    let expected = {
        let int = t.int();
        let ok = t.atom_lit("ok");
        t.tuple(&[int, ok])
    };
    assert!(
        t.is_equivalent(&ret, &expected),
        "&id/1 should create separate activation reads for int and :ok calls, got {ret:?}"
    );
}

#[test]
fn named_ref_return_preserves_thin_callable_kind() {
    let mut t = crate::types::new();
    let module = lower("fn id(x), do: x\nfn main(), do: &id/1");
    let ret = infer_return(&mut t, &module, main_id(&module), &[]);

    assert_eq!(callable_kind(&t, &ret), Some(CallableValueKind::FnRef));
    assert_eq!(
        t.closure_lit_parts(&ret).map(|info| info.captures.len()),
        Some(0),
        "thin fn refs should carry no capture payload in inference"
    );
}

#[test]
fn zero_capture_lambda_return_preserves_thin_callable_kind() {
    let mut t = crate::types::new();
    let module = lower("fn main(), do: fn(x) -> x end");
    let ret = infer_return(&mut t, &module, main_id(&module), &[]);

    assert_eq!(callable_kind(&t, &ret), Some(CallableValueKind::FnRef));
    assert_eq!(
        t.closure_lit_parts(&ret).map(|info| info.captures.len()),
        Some(0),
        "zero-capture lambdas should infer as thin callable values"
    );
}

#[test]
fn captured_lambda_return_preserves_closure_kind() {
    let mut t = crate::types::new();
    let module = lower("fn mk(x), do: fn(y) -> x + y end\nfn main(), do: mk(1)");
    let ret = infer_return(&mut t, &module, main_id(&module), &[]);

    assert_eq!(callable_kind(&t, &ret), Some(CallableValueKind::Closure));
    assert_eq!(
        t.closure_lit_parts(&ret).map(|info| info.captures.len()),
        Some(1),
        "captured lambdas should preserve capture payload in inference"
    );
}

#[test]
fn named_refs_drive_pattern_dispatch_per_activation() {
    let mut t = crate::types::new();
    let module = lower(include_str!("fixtures/poly_named_ref_pattern.fz"));
    let ret = infer_fn_via_main(&module, "main");
    let expected = {
        let one = t.atom_lit("one");
        let two = t.atom_lit("two");
        t.tuple(&[one, two])
    };
    assert!(
        t.is_equivalent(&ret, &expected),
        "&pick/1 should feed each call argument into matcher proof and keep the catch-all dead, got {ret:?}"
    );
}

#[test]
fn captured_closure_refs_instantiate_by_capture_and_arg_facts() {
    let mut t = crate::types::new();
    let module = lower(include_str!("fixtures/poly_capture_ref.fz"));
    let ret = infer_fn_via_main(&module, "main");
    let expected = {
        let ok = t.atom_lit("ok");
        let int = t.int();
        let right = t.atom_lit("right");
        let int_pair = t.tuple(&[ok.clone(), int]);
        let atom_pair = t.tuple(&[ok, right]);
        t.tuple(&[int_pair, atom_pair])
    };
    assert!(
        t.is_equivalent(&ret, &expected),
        "captured closure should prepend capture facts inside inference while keeping call arity explicit, got {ret:?}"
    );
}

#[test]
fn direct_calls_specialize_atom_pattern_dispatch_by_input() {
    let mut t = crate::types::new();
    let module = lower(include_str!("fixtures/match_atom_partition.fz"));
    let ret = infer_fn_via_main(&module, "main");
    let expected = {
        let one = t.atom_lit("one");
        let two = t.atom_lit("two");
        t.tuple(&[one, two])
    };
    assert!(
        t.is_equivalent(&ret, &expected),
        "main should select distinct matcher leaves for :left and :right activations, got {ret:?}"
    );
}

#[test]
fn direct_calls_specialize_list_pattern_dispatch_by_shape() {
    let mut t = crate::types::new();
    let module = lower(include_str!("fixtures/match_list_partition.fz"));
    let ret = infer_fn_via_main(&module, "main");
    let expected = {
        let empty = t.atom_lit("empty");
        let cons = t.atom_lit("cons");
        t.tuple(&[empty, cons])
    };
    assert!(
        t.is_equivalent(&ret, &expected),
        "main should select empty-list and cons matcher leaves per activation, got {ret:?}"
    );
}

#[test]
fn list_pattern_binding_flows_into_selected_leaf() {
    let mut t = crate::types::new();
    let module = lower(include_str!("fixtures/match_list_binding.fz"));
    let ret = infer_fn_via_main(&module, "main");
    let expected = {
        let empty = t.atom_lit("empty");
        let int = t.int();
        t.tuple(&[empty, int])
    };
    assert!(
        t.is_equivalent(&ret, &expected),
        "cons leaf should return the matched head type, got {ret:?}"
    );
}

#[test]
fn tuple_pattern_binding_flows_into_selected_leaf() {
    let mut t = crate::types::new();
    let module = lower(include_str!("fixtures/match_tuple_binding.fz"));
    let ret = infer_fn_via_main(&module, "main");
    let expected = {
        let int = t.int();
        let error = t.atom_lit("error");
        t.tuple(&[int, error])
    };
    assert!(
        t.is_equivalent(&ret, &expected),
        "tuple leaf should return the matched payload type, got {ret:?}"
    );
}

#[test]
fn nested_pattern_binding_flows_into_selected_leaf() {
    let mut t = crate::types::new();
    let module = lower(include_str!("fixtures/match_nested_binding.fz"));
    let ret = infer_fn_via_main(&module, "main");
    let expected = {
        let int = t.int();
        let error = t.atom_lit("error");
        t.tuple(&[int, error])
    };
    assert!(
        t.is_equivalent(&ret, &expected),
        "nested tuple/list leaf should return the matched head type, got {ret:?}"
    );
}

#[test]
fn nested_pattern_partition_selects_sibling_leaves() {
    let mut t = crate::types::new();
    let module = lower(include_str!("fixtures/match_nested_partition.fz"));
    let ret = infer_fn_via_main(&module, "main");
    let expected = {
        let empty = t.atom_lit("empty");
        let int = t.int();
        let error = t.atom_lit("error");
        t.tuple(&[empty, int, error])
    };
    assert!(
        t.is_equivalent(&ret, &expected),
        "nested tuple/list partition should select empty, cons, and error leaves, got {ret:?}"
    );
}

#[test]
fn tuple_tag_partition_selects_matching_payloads() {
    let mut t = crate::types::new();
    let module = lower(include_str!("fixtures/match_tuple_tag_partition.fz"));
    let ret = infer_fn_via_main(&module, "main");
    let expected = {
        let int = t.int();
        let bad = t.atom_lit("bad");
        t.tuple(&[int, bad])
    };
    assert!(
        t.is_equivalent(&ret, &expected),
        "same-arity tuple partition should select payloads by tag, got {ret:?}"
    );
}

#[test]
fn tuple_arity_partition_selects_matching_shape() {
    let mut t = crate::types::new();
    let module = lower(include_str!("fixtures/match_tuple_arity_partition.fz"));
    let ret = infer_fn_via_main(&module, "main");
    let expected = {
        let int = t.int();
        let pair = t.tuple(&[int.clone(), int.clone()]);
        let other = t.atom_lit("other");
        t.tuple(&[int, pair, other])
    };
    assert!(
        t.is_equivalent(&ret, &expected),
        "tuple arity partition should select each matching shape, got {ret:?}"
    );
}

#[test]
fn guard_partition_selects_refined_clause() {
    let mut t = crate::types::new();
    let module = lower(include_str!("fixtures/match_guard_partition.fz"));
    let ret = infer_fn_via_main(&module, "main");
    let expected = {
        let int = t.int();
        let fallback = t.atom_lit("fallback");
        t.tuple(&[int, fallback])
    };
    assert!(
        t.is_equivalent(&ret, &expected),
        "guarded tuple clause should select by guard proof, got {ret:?}"
    );
}

#[test]
fn map_pattern_binding_flows_into_selected_leaf() {
    let mut t = crate::types::new();
    let module = lower(include_str!("fixtures/match_map_binding.fz"));
    let ret = infer_fn_via_main(&module, "main");
    let expected = {
        let int = t.int();
        let none = t.atom_lit("none");
        t.tuple(&[int, none])
    };
    assert!(
        t.is_equivalent(&ret, &expected),
        "map leaf should bind the matched key value without reaching the catch-all, got {ret:?}"
    );
}

#[test]
fn matcher_dead_arms_are_observable_via_telemetry() {
    let module = lower(include_str!("fixtures/poly_named_ref_pattern.fz"));
    let mut t = crate::types::new();
    let report = infer_report_via_main(&mut t, &module);

    assert!(
        !report.facts.dead_arms.is_empty(),
        "matcher proof should emit dead-arm telemetry for source-total catch-all dispatch"
    );
    assert!(
        !report.outcome.dead_arms.is_empty(),
        "dead-arm proof should also be returned in the production outcome"
    );
}

#[test]
fn corpus_folds_settle_myreduce_to_int() {
    let corpus = [
        ("fold_tail", include_str!("fixtures/fold_tail.fz")),
        ("fold_nontail", include_str!("fixtures/fold_nontail.fz")),
        ("fold_capture_int", include_str!("fixtures/fold_capture_int.fz")),
        ("fold_capture_closure", include_str!("fixtures/fold_capture_closure.fz")),
        ("fold_state_machine", include_str!("fixtures/fold_state_machine.fz")),
    ];
    let mut t = crate::types::new();
    let int = t.int();
    for (name, src) in corpus {
        let module = lower(src);
        let ret = infer_fn_via_main(&module, "myreduce");
        assert!(
            t.is_equivalent(&ret, &int),
            "{name}: myreduce should settle to int, got {ret:?}"
        );
    }
}

#[test]
fn closure_apply_prepends_captures_as_leading_params() {
    let mut t = crate::types::new();
    let cap = t.int();
    let clo = t.closure_lit(ClosureTarget(7), vec![cap], 2);
    let a = t.int();
    let b = t.int();
    let (target, inputs) = closure_apply_contract(&t, &clo, &[a, b]).expect("singleton closure");
    assert_eq!(target, FnId(7));
    assert_eq!(inputs.len(), 3, "captures ++ args");
}

#[test]
fn captured_closure_is_carried_concretely() {
    let mut t = crate::types::new();
    let inner = t.closure_lit(ClosureTarget(9), vec![], 2);
    let outer = t.closure_lit(ClosureTarget(8), vec![inner], 2);
    let a = t.int();
    let b = t.int();
    let (target, inputs) = closure_apply_contract(&t, &outer, &[a, b]).expect("singleton closure");
    assert_eq!(target, FnId(8));
    let captured = t
        .closure_lit_parts(&inputs[0])
        .expect("leading input is the captured closure, concrete");
    assert_eq!(captured.target, ClosureTarget(9));
    assert_eq!(captured.kind, CallableValueKind::Closure);
}

#[test]
fn non_closure_has_no_apply_contract() {
    let mut t = crate::types::new();
    let int = t.int();
    assert!(closure_apply_contract(&t, &int, &[]).is_none());
}
