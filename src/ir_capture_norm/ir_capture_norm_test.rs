use super::*;
use crate::diag::Span;
use crate::exec::matcher::{Matcher, MatcherLeaf, MatcherNode};
use crate::fz_ir::{
    BinOp, BlockId, CallsiteIdent, Const, FnBuilder, FnCategory, FnId, ModuleBuilder, Prim, ReceiveAfter, ReceiveClause,
};
use crate::telemetry::capture::OwnedEvent;
use crate::telemetry::{Capture, ConfiguredTelemetry, Value};
use std::sync::Arc;

fn build_module_with_call_cont(captured: Vec<Var>, captured_params: Vec<Var>, used: Var) -> Module {
    let caller_id = FnId(0);
    let cont_id = FnId(1);

    let mut caller = FnBuilder::new(caller_id, "caller");
    let entry = caller.block(vec![]);
    let callee_arg = caller.let_(entry, Prim::Const(Const::Int(0)));
    caller.set_terminator(
        entry,
        Term::Call {
            ident: CallsiteIdent::from_source(Span::DUMMY),
            callee: FnId(99),
            args: vec![callee_arg],
            continuation: Cont {
                fn_id: cont_id,
                captured,
            },
        },
    );

    let mut cont = FnBuilder::new(cont_id, "k_1").with_category(FnCategory::CpsCont);
    let result = Var(0);
    let mut params = vec![result];
    params.extend(captured_params);
    let entry = cont.block(params);
    cont.set_terminator(entry, Term::Return(used));

    let mut mb = ModuleBuilder::new();
    mb.add_fn(caller.build());
    mb.add_fn(cont.build());
    mb.build()
}

fn build_module_with_callclosure_dead_transitive_capture() -> Module {
    let caller_id = FnId(0);
    let cont_id = FnId(1);

    let mut caller = FnBuilder::new(caller_id, "caller");
    let entry = caller.block(vec![]);
    let closure = caller.let_(entry, Prim::Const(Const::Atom(1)));
    let arg = caller.let_(entry, Prim::Const(Const::Int(0)));
    caller.set_terminator(
        entry,
        Term::CallClosure {
            ident: CallsiteIdent::from_source(Span::DUMMY),
            closure,
            args: vec![arg],
            continuation: Cont {
                fn_id: cont_id,
                captured: vec![Var(10), Var(11)],
            },
        },
    );

    let mut cont = FnBuilder::new(cont_id, "k_resume").with_category(FnCategory::CpsCont);
    let result = cont.fresh_var();
    let live = cont.fresh_var();
    let dead = cont.fresh_var();
    let entry = cont.block(vec![result, live, dead]);
    let _unused = cont.let_(entry, Prim::BinOp(BinOp::Add, dead, result));
    cont.set_terminator(entry, Term::Return(live));

    let mut mb = ModuleBuilder::new();
    mb.add_fn(caller.build());
    mb.add_fn(cont.build());
    mb.build()
}

fn build_module_with_shared_cont_site() -> Module {
    let cont_id = FnId(2);
    let mut mb = ModuleBuilder::new();

    for caller_raw in [0, 1] {
        let caller_id = FnId(caller_raw);
        let mut caller = FnBuilder::new(caller_id, format!("caller_{}", caller_raw));
        let entry = caller.block(vec![]);
        let callee_arg = caller.let_(entry, Prim::Const(Const::Int(0)));
        caller.set_terminator(
            entry,
            Term::Call {
                ident: CallsiteIdent::from_source(Span::DUMMY),
                callee: FnId(99),
                args: vec![callee_arg],
                continuation: Cont {
                    fn_id: cont_id,
                    captured: vec![Var(10), Var(11)],
                },
            },
        );
        mb.add_fn(caller.build());
    }

    let mut cont = FnBuilder::new(cont_id, "shared_k").with_category(FnCategory::CpsCont);
    let entry = cont.block(vec![Var(0), Var(1), Var(2)]);
    cont.set_terminator(entry, Term::Return(Var(2)));
    mb.add_fn(cont.build());
    mb.build()
}

fn build_module_with_tail_call_cont_site() -> Module {
    let cont_id = FnId(2);
    let mut mb = ModuleBuilder::new();

    for (caller_raw, live_arg, dead_arg) in [(0, Var(10), Var(11)), (1, Var(20), Var(21))] {
        let caller_id = FnId(caller_raw);
        let mut caller = FnBuilder::new(caller_id, format!("branch_{}", caller_raw));
        let entry = caller.block(vec![]);
        caller.set_terminator(
            entry,
            Term::TailCall {
                ident: CallsiteIdent::from_source(Span::DUMMY),
                callee: cont_id,
                args: vec![live_arg, dead_arg],
                is_back_edge: false,
            },
        );
        mb.add_fn(caller.build());
    }

    let mut cont = FnBuilder::new(cont_id, "if_join").with_category(FnCategory::ControlFlowCont);
    let entry = cont.block(vec![Var(0), Var(1)]);
    cont.set_terminator(entry, Term::Return(Var(0)));
    mb.add_fn(cont.build());
    mb.build()
}

fn empty_matcher() -> Arc<Matcher> {
    Arc::new(Matcher::new(
        vec![],
        MatcherNode::Leaf(MatcherLeaf {
            body_id: 0,
            bindings: vec![],
            span: Span::DUMMY,
        }),
    ))
}

fn build_module_with_receive_matched(captures: Vec<Var>) -> Module {
    let mut caller = FnBuilder::new(FnId(0), "receiver");
    let entry = caller.block(vec![]);
    caller.set_terminator(
        entry,
        Term::ReceiveMatched {
            ident: CallsiteIdent::from_source(Span::DUMMY),
            clauses: vec![ReceiveClause {
                ident: CallsiteIdent::synthetic(),
                bound_names: vec!["msg".to_string()],
                guard: None,
                body: FnId(1),
                span: Span::DUMMY,
            }],
            matcher: empty_matcher(),
            after: Some(ReceiveAfter {
                ident: CallsiteIdent::synthetic(),
                timeout: Var(99),
                body: FnId(2),
                span: Span::DUMMY,
            }),
            pinned: vec![],
            captures,
        },
    );

    let mut body = FnBuilder::new(FnId(1), "rx_body").with_category(FnCategory::CpsCont);
    let entry = body.block(vec![Var(0), Var(1), Var(2)]);
    body.set_terminator(entry, Term::Return(Var(0)));

    let mut after = FnBuilder::new(FnId(2), "rx_after").with_category(FnCategory::CpsCont);
    let entry = after.block(vec![Var(3), Var(4)]);
    after.set_terminator(entry, Term::Return(Var(4)));

    let mut mb = ModuleBuilder::new();
    mb.add_fn(caller.build());
    mb.add_fn(body.build());
    mb.add_fn(after.build());
    mb.build()
}

fn normalize_with_capture(module: &mut Module) -> Capture {
    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());
    normalize_continuation_captures_with_telemetry(module, &tel);
    cap
}

fn assert_pruned_event(cap: &Capture, producer: &str, before: u64, after: u64, pruned: u64) -> OwnedEvent {
    let ev = cap
        .last(&["fz", "ir", "capture_norm", "captures_pruned"])
        .expect("captures_pruned event");
    assert!(matches!(
        ev.metadata.get("producer"),
        Some(Value::Str(s)) if s.as_ref() == producer
    ));
    assert!(matches!(
        ev.measurements.get("before_captures"),
        Some(Value::U64(n)) if *n == before
    ));
    assert!(matches!(
        ev.measurements.get("after_captures"),
        Some(Value::U64(n)) if *n == after
    ));
    assert!(matches!(
        ev.measurements.get("pruned_captures"),
        Some(Value::U64(n)) if *n == pruned
    ));
    ev
}

#[test]
fn drops_unused_continuation_captures() {
    let mut module = build_module_with_call_cont(vec![Var(10), Var(11)], vec![Var(1), Var(2)], Var(2));

    let cap = normalize_with_capture(&mut module);
    let ev = assert_pruned_event(&cap, "call_continuation", 2, 1, 1);
    assert!(matches!(
        ev.measurements.get("deduplicated_captures"),
        Some(Value::U64(0))
    ));

    let caller = module.fn_by_id(FnId(0));
    let Term::Call { continuation, .. } = &caller.block(BlockId(0)).terminator else {
        panic!("expected call terminator");
    };
    assert_eq!(continuation.captured, vec![Var(11)]);

    let cont = module.fn_by_id(FnId(1));
    assert_eq!(cont.block(BlockId(0)).params, vec![Var(0), Var(2)]);
}

#[test]
fn deduplicates_same_outer_var_and_rewrites_body() {
    let mut module = build_module_with_call_cont(vec![Var(10), Var(10)], vec![Var(1), Var(2)], Var(2));

    let cap = normalize_with_capture(&mut module);
    let ev = assert_pruned_event(&cap, "call_continuation", 2, 1, 1);
    assert!(matches!(
        ev.measurements.get("deduplicated_captures"),
        Some(Value::U64(1))
    ));

    let caller = module.fn_by_id(FnId(0));
    let Term::Call { continuation, .. } = &caller.block(BlockId(0)).terminator else {
        panic!("expected call terminator");
    };
    assert_eq!(continuation.captured, vec![Var(10)]);

    let cont = module.fn_by_id(FnId(1));
    let entry = cont.block(BlockId(0));
    assert_eq!(entry.params, vec![Var(0), Var(1)]);
    assert!(matches!(entry.terminator, Term::Return(Var(1))));
}

#[test]
fn prunes_dead_positions_from_shared_continuation_sites() {
    let mut module = build_module_with_shared_cont_site();

    let cap = normalize_with_capture(&mut module);
    let ev = assert_pruned_event(&cap, "shared_call_continuation", 2, 1, 1);
    assert!(matches!(ev.measurements.get("caller_count"), Some(Value::U64(2))));

    for caller_id in [FnId(0), FnId(1)] {
        let caller = module.fn_by_id(caller_id);
        let Term::Call { continuation, .. } = &caller.block(BlockId(0)).terminator else {
            panic!("expected call terminator");
        };
        assert_eq!(continuation.captured, vec![Var(11)]);
    }

    let cont = module.fn_by_id(FnId(2));
    assert_eq!(cont.block(BlockId(0)).params, vec![Var(0), Var(2)]);
}

#[test]
fn leaves_shared_continuation_sites_unchanged_when_all_positions_live() {
    let mut module = build_module_with_shared_cont_site();
    {
        let cont_idx = *module.fn_idx.get(&FnId(2)).expect("cont exists");
        let cont = &mut module.fns[cont_idx];
        let block = cont
            .blocks
            .iter_mut()
            .find(|block| block.id == BlockId(0))
            .expect("entry block exists");
        block
            .stmts
            .push(Stmt::Let(Var(3), Prim::BinOp(BinOp::Add, Var(1), Var(2))));
        block.terminator = Term::Return(Var(3));
    }

    let cap = normalize_with_capture(&mut module);
    assert_eq!(cap.count(&["fz", "ir", "capture_norm", "captures_pruned"]), 0);

    for caller_id in [FnId(0), FnId(1)] {
        let caller = module.fn_by_id(caller_id);
        let Term::Call { continuation, .. } = &caller.block(BlockId(0)).terminator else {
            panic!("expected call terminator");
        };
        assert_eq!(continuation.captured, vec![Var(10), Var(11)]);
    }

    let cont = module.fn_by_id(FnId(2));
    assert_eq!(cont.block(BlockId(0)).params, vec![Var(0), Var(1), Var(2)]);
}

#[test]
fn prunes_callclosure_capture_used_only_by_dead_pure_stmt() {
    let mut module = build_module_with_callclosure_dead_transitive_capture();

    let cap = normalize_with_capture(&mut module);
    let ev = assert_pruned_event(&cap, "call_continuation", 2, 1, 1);
    assert!(matches!(
        ev.measurements.get("deduplicated_captures"),
        Some(Value::U64(0))
    ));

    let caller = module.fn_by_id(FnId(0));
    let Term::CallClosure { continuation, .. } = &caller.block(BlockId(0)).terminator else {
        panic!("expected call-closure terminator");
    };
    assert_eq!(continuation.captured, vec![Var(10)]);

    let cont = module.fn_by_id(FnId(1));
    assert_eq!(cont.block(BlockId(0)).params, vec![Var(0), Var(1)]);
}

#[test]
fn normalizes_tail_call_continuation_args_across_all_callers() {
    let mut module = build_module_with_tail_call_cont_site();

    let cap = normalize_with_capture(&mut module);
    let ev = assert_pruned_event(&cap, "tail_call_continuation", 2, 1, 1);
    assert!(matches!(ev.measurements.get("caller_count"), Some(Value::U64(2))));

    for (caller_id, expected_arg) in [(FnId(0), Var(10)), (FnId(1), Var(20))] {
        let caller = module.fn_by_id(caller_id);
        let Term::TailCall { args, .. } = &caller.block(BlockId(0)).terminator else {
            panic!("expected tail-call terminator");
        };
        assert_eq!(args, &vec![expected_arg]);
    }

    let cont = module.fn_by_id(FnId(2));
    assert_eq!(cont.block(BlockId(0)).params, vec![Var(0)]);
}

#[test]
fn normalizes_receive_matched_shared_captures() {
    let mut module = build_module_with_receive_matched(vec![Var(10), Var(11)]);

    let cap = normalize_with_capture(&mut module);
    let ev = assert_pruned_event(&cap, "receive_matched", 2, 1, 1);
    assert!(matches!(ev.measurements.get("outcome_count"), Some(Value::U64(2))));

    let caller = module.fn_by_id(FnId(0));
    let Term::ReceiveMatched { captures, .. } = &caller.block(BlockId(0)).terminator else {
        panic!("expected receive matched terminator");
    };
    assert_eq!(captures, &vec![Var(11)]);

    let body = module.fn_by_id(FnId(1));
    assert_eq!(body.block(BlockId(0)).params, vec![Var(0), Var(2)]);

    let after = module.fn_by_id(FnId(2));
    assert_eq!(after.block(BlockId(0)).params, vec![Var(4)]);
}
