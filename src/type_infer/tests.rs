use super::{
    TypeInferOutcome, TypeInferReturnState, TypeInferStatus, closure_apply_contract,
    infer_from_entry, infer_return,
};
use crate::fz_ir::{Const, FnBuilder, FnId, Module, ModuleBuilder, Prim, Term};
use crate::telemetry::{ConfiguredTelemetry, Handler, Value};
use crate::types::{ClosureTarget, ClosureTypes, ConcreteTypes, Ty, Types};
use std::cell::RefCell;
use std::panic::AssertUnwindSafe;
use std::rc::Rc;

/// Captures the `Module` from the `fz.frontend.lowered` telemetry event: the
/// exact IR the planner consumes, emitted by the production frontend just before
/// planning.
struct LoweredCapture(Rc<RefCell<Option<Module>>>);

impl Handler for LoweredCapture {
    fn handle(&self, ev: &crate::telemetry::Event<'_, '_, '_>) {
        if let ["fz", "frontend", "lowered"] = ev.name {
            if let Some(module) = ev
                .metadata
                .get("module")
                .and_then(|v| v.downcast_ref::<Module>())
            {
                *self.0.borrow_mut() = Some(module.clone());
            }
        }
    }
}

/// Lower a source program to its IR `Module` via the production frontend,
/// snapshotting the module from telemetry at the lowering stage. The corpus runs
/// the normal flow, including the old planner; the lowered event fires before
/// planning, so the snapshot lands first and any later panic is ignored.
fn lower(src: &str) -> Module {
    let captured = Rc::new(RefCell::new(None));
    let tel = ConfiguredTelemetry::new();
    tel.attach(&["fz"], Box::new(LoweredCapture(captured.clone())));

    let prev_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let _ = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let mut t = ConcreteTypes;
        let providers = crate::modules::pipeline::ProviderInputs::new(
            crate::modules::artifact_store::DEFAULT_ARTIFACT_ROOT.to_string(),
            Vec::new(),
        );
        let _ = crate::modules::pipeline::compile_source_with_providers(
            &mut t,
            src.to_string(),
            "type_infer_fixture.fz".to_string(),
            &providers,
            &tel,
        );
    }));
    std::panic::set_hook(prev_hook);

    captured
        .borrow_mut()
        .take()
        .expect("frontend emitted no lowered module")
}

/// Compile a program to its LTO-linked IR `Module` via the production pipeline:
/// the runtime graph where `Enum.reduce`, `List.reduce`,
/// `Enumerable.List.reduce`, and protocol dispatch stubs are local fns.
fn linked(src: &str) -> Module {
    use crate::modules::pipeline::{
        CompileMode, ProviderInputs, checked_module_for_mode, compile_source_with_providers,
        prepare_execution_graph,
    };
    let mut t = ConcreteTypes;
    let tel = crate::telemetry::NullTelemetry;
    let providers = ProviderInputs::new(
        crate::modules::artifact_store::DEFAULT_ARTIFACT_ROOT.to_string(),
        Vec::new(),
    );
    let frontend = compile_source_with_providers(
        &mut t,
        src.to_string(),
        "type_infer_fixture.fz".to_string(),
        &providers,
        &tel,
    )
    .unwrap_or_else(|e| panic!("frontend: {e}"));
    let checked = checked_module_for_mode(&mut t, frontend, &tel, CompileMode::Normal)
        .unwrap_or_else(|e| panic!("checked: {e}"));
    let graph = prepare_execution_graph(&mut t, checked, &providers, &tel, CompileMode::Normal)
        .unwrap_or_else(|e| panic!("execution graph: {e}"));
    graph.module
}

fn main_id(module: &Module) -> FnId {
    module
        .fns
        .iter()
        .find(|f| f.name == "main" || f.name.ends_with(".main"))
        .expect("main fn")
        .id
}

#[derive(Clone, Debug, Default)]
struct TypeInferFacts {
    fn_returns: Vec<FnReturnFact>,
    activations: Vec<ActivationFact>,
    diagnostics: Vec<DiagnosticFact>,
    dead_arms: usize,
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
    fn_id: FnId,
    fn_name: String,
    input_count: usize,
    state: String,
    return_ty: Option<Ty>,
}

#[derive(Clone, Debug)]
struct DiagnosticFact {
    code: String,
    op: Option<String>,
    fn_name: Option<String>,
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
    fn handle(&self, ev: &crate::telemetry::Event<'_, '_, '_>) {
        let mut facts = self.0.borrow_mut();
        match ev.name {
            ["fz", "type_infer", "fn_return"] => {
                if let (Some(fn_name), Some(state)) = (
                    event_metadata_str(ev, "fn_name"),
                    event_metadata_str(ev, "state"),
                ) {
                    facts.fn_returns.push(FnReturnFact {
                        fn_name,
                        state,
                        return_ty: event_metadata_ty(ev, "return_ty_data"),
                    });
                }
            }
            ["fz", "type_infer", "activation"] => {
                if let (Some(fn_name), Some(fn_id), Some(input_count), Some(state)) = (
                    event_metadata_str(ev, "fn_name"),
                    event_metadata_u64(ev, "fn_id"),
                    event_metadata_u64(ev, "input_count"),
                    event_metadata_str(ev, "state"),
                ) {
                    facts.activations.push(ActivationFact {
                        fn_id: FnId(fn_id as u32),
                        fn_name,
                        input_count: input_count as usize,
                        state,
                        return_ty: event_metadata_ty(ev, "return_ty_data"),
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
            ["fz", "type_infer", "dead_arm"] => {
                facts.dead_arms += 1;
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

fn infer_report_via_main(t: &mut ConcreteTypes, module: &Module) -> TelemetryReport {
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
    let mut t = ConcreteTypes;
    let report = infer_report_via_main(&mut t, module);
    report.facts.return_for_fn_named(fn_name)
}

fn infer_entry_return_via_main(module: &Module) -> Ty {
    let mut t = ConcreteTypes;
    infer_report_via_main(&mut t, module).outcome.entry_return
}

fn event_metadata_str(ev: &crate::telemetry::Event<'_, '_, '_>, key: &str) -> Option<String> {
    match ev.metadata.get(key)? {
        Value::Str(value) => Some(value.to_string()),
        _ => None,
    }
}

fn event_metadata_ty(ev: &crate::telemetry::Event<'_, '_, '_>, key: &str) -> Option<Ty> {
    ev.metadata.get(key)?.downcast_ref::<Ty>().cloned()
}

fn event_metadata_u64(ev: &crate::telemetry::Event<'_, '_, '_>, key: &str) -> Option<u64> {
    match ev.metadata.get(key)? {
        Value::U64(value) => Some(*value),
        _ => None,
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
        (
            "fold_capture_int",
            include_str!("fixtures/fold_capture_int.fz"),
        ),
        (
            "fold_capture_closure",
            include_str!("fixtures/fold_capture_closure.fz"),
        ),
        (
            "fold_state_machine",
            include_str!("fixtures/fold_state_machine.fz"),
        ),
    ] {
        let module = lower(src);
        let mut t = ConcreteTypes;
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
        (
            "list lambda",
            "Enum.reduce",
            include_str!("fixtures/enum_reduce.fz"),
        ),
        (
            "named-fn ref",
            "Enum.reduce",
            include_str!("fixtures/enum_reduce_named_ref_ok.fz"),
        ),
        (
            "count",
            "Enum.count",
            include_str!("fixtures/enum_count.fz"),
        ),
        (
            "range reduce",
            "Enum.reduce",
            include_str!("fixtures/enum_reduce_range.fz"),
        ),
    ];
    let mut t = ConcreteTypes;
    let int = t.int();
    for (label, entry, src) in cases {
        let module = linked(src);
        let ret = infer_fn_via_main(&module, entry);
        assert!(
            t.is_equivalent(&ret, &int),
            "{label}: {entry} should settle to int, got {ret:?}"
        );
    }
}

#[test]
fn enum_reduce_runtime_graph_settles() {
    let module = linked(include_str!("fixtures/enum_reduce.fz"));
    let mut t = ConcreteTypes;
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
    let module = linked(include_str!("fixtures/enum_reduce.fz"));
    let mut t = ConcreteTypes;
    let int = t.int();
    let report = infer_report_via_main(&mut t, &module);

    assert_eq!(report.outcome.status, TypeInferStatus::Complete);
    assert_eq!(
        report.outcome.activations.len(),
        report.facts.activations.len(),
        "returned activation facts and activation telemetry should describe the same reached cells"
    );

    for fact in &report.outcome.activations {
        assert!(
            report.facts.activations.iter().any(|event| {
                event.fn_id == fact.fn_id
                    && event.input_count == fact.input_tys.len()
                    && event.state == return_state_name(&fact.return_state)
            }),
            "activation fact should be observable through telemetry: {fact:?}"
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
            event.fn_id == reduce_fact.fn_id
                && event.input_count == reduce_fact.input_tys.len()
                && event.state == "known"
                && event
                    .return_ty
                    .as_ref()
                    .is_some_and(|ty| t.is_equivalent(ty, &int))
        }),
        "known activation return should be visible through telemetry too"
    );
}

#[test]
fn invalid_named_reduce_reducer_emits_operator_diagnostic() {
    let module = linked(include_str!("fixtures/enum_reduce_named_ref.fz"));
    let mut t = ConcreteTypes;
    let report = infer_report_via_main(&mut t, &module);
    assert_eq!(report.outcome.status, TypeInferStatus::Invalid);
    assert!(
        report.facts.has_invalid_operator_for("broken_reducer", "+"),
        "expected invalid + diagnostic for Main.broken_reducer/2, got {:?}",
        report.facts.diagnostics
    );
}

#[test]
fn add_infers_int_via_harness() {
    let mut t = ConcreteTypes;
    let module = lower(include_str!("fixtures/add.fz"));
    let add_id = module.fn_by_name("add").expect("add fn").id;
    let int = t.int();
    let ret = infer_return(&mut t, &module, add_id, &[int.clone(), int.clone()]);
    assert!(
        t.is_equivalent(&ret, &int),
        "add(int, int) should infer int"
    );
}

#[test]
fn infer_return_erases_residual_unknown_to_any_at_boundary() {
    let mut b = FnBuilder::new(FnId(0), "unknown_expr");
    let entry = b.block(vec![]);
    let value = b.let_(entry, Prim::MakeBitstring(vec![]));
    b.set_terminator(entry, Term::Return(value));

    let mut mb = ModuleBuilder::new();
    mb.add_fn(b.build());
    let module = mb.build();

    let mut t = ConcreteTypes;
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
    let unknown = b.let_(unknown_b, Prim::MakeBitstring(vec![]));
    b.set_terminator(unknown_b, Term::Return(unknown));
    let one = b.let_(known_b, Prim::Const(Const::Int(1)));
    b.set_terminator(known_b, Term::Return(one));
    b.set_terminator(entry, Term::if_user(cond, unknown_b, known_b));

    let mut mb = ModuleBuilder::new();
    mb.add_fn(b.build());
    let module = mb.build();

    let mut t = ConcreteTypes;
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

    let mut t = ConcreteTypes;
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
    let mut t = ConcreteTypes;
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
    let mut t = ConcreteTypes;
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
fn named_refs_drive_pattern_dispatch_per_activation() {
    let mut t = ConcreteTypes;
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
    let mut t = ConcreteTypes;
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
    let mut t = ConcreteTypes;
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
    let mut t = ConcreteTypes;
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
    let mut t = ConcreteTypes;
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
    let mut t = ConcreteTypes;
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
    let mut t = ConcreteTypes;
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
    let mut t = ConcreteTypes;
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
    let mut t = ConcreteTypes;
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
    let mut t = ConcreteTypes;
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
    let mut t = ConcreteTypes;
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
    let mut t = ConcreteTypes;
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
    let mut t = ConcreteTypes;
    let report = infer_report_via_main(&mut t, &module);

    assert!(
        report.facts.dead_arms > 0,
        "matcher proof should emit dead-arm telemetry for source-total catch-all dispatch"
    );
}

#[test]
fn corpus_folds_settle_myreduce_to_int() {
    let corpus = [
        ("fold_tail", include_str!("fixtures/fold_tail.fz")),
        ("fold_nontail", include_str!("fixtures/fold_nontail.fz")),
        (
            "fold_capture_int",
            include_str!("fixtures/fold_capture_int.fz"),
        ),
        (
            "fold_capture_closure",
            include_str!("fixtures/fold_capture_closure.fz"),
        ),
        (
            "fold_state_machine",
            include_str!("fixtures/fold_state_machine.fz"),
        ),
    ];
    let mut t = ConcreteTypes;
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
    let mut t = ConcreteTypes;
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
    let mut t = ConcreteTypes;
    let inner = t.closure_lit(ClosureTarget(9), vec![], 2);
    let outer = t.closure_lit(ClosureTarget(8), vec![inner], 2);
    let a = t.int();
    let b = t.int();
    let (target, inputs) = closure_apply_contract(&t, &outer, &[a, b]).expect("singleton closure");
    assert_eq!(target, FnId(8));
    let captured = t
        .closure_lit_parts(&inputs[0])
        .expect("leading input is the captured closure, concrete");
    assert_eq!(FnId::from(captured.target), FnId(9));
}

#[test]
fn non_closure_has_no_apply_contract() {
    let mut t = ConcreteTypes;
    let int = t.int();
    assert!(closure_apply_contract(&t, &int, &[]).is_none());
}
