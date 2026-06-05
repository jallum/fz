use super::*;
use crate::diag::FileId;
use crate::modules::identity::ModuleName;
use crate::modules::interface::{FZ_INTERFACE_ABI_VERSION, InterfaceFn, InterfaceSpec, ModuleInterface};

/// fz-t1m.3.1.1 — a compiled `Module` round-trips losslessly through
/// serde_json. Builds a non-trivial module (two fns, a Call term, an If, a
/// MakeTuple, a MakeClosure, and an atom Const) carrying *real* spans, then
/// asserts the canonical `serde_json::Value` is identical before and after
/// a deserialize round-trip. Finally rebuilds the skipped indices and proves
/// `fn_by_id` reconstructs.
#[test]
fn module_serde_roundtrips() {
    let file = FileId(7);
    let span = |start, end| Span::new(file, start, end);

    // callee: fn pair(x) = { :ok, x }  — exercises MakeTuple + atom Const
    let mut callee = FnBuilder::new(FnId(0), "pair");
    let cx = callee.fresh_var();
    let centry = callee.block(vec![cx]);
    let ok = callee.let_(centry, Prim::Const(Const::Atom(3)));
    let tup = callee.let_(centry, Prim::MakeTuple(vec![ok, cx]));
    callee.set_terminator(centry, Term::Return(tup));

    // caller: fn go(p) = if p then <call pair> else <closure over p>
    // — exercises If (real span), Call (real span ident), MakeClosure.
    let mut caller = FnBuilder::new(FnId(1), "go");
    let p = caller.fresh_var();
    let entry = caller.block(vec![p]);
    let then_b = caller.block(vec![]);
    let else_b = caller.block(vec![]);
    caller.set_terminator(
        entry,
        Term::If {
            cond: p,
            then_b,
            else_b,
            origin: BranchOrigin::User,
        },
    );
    // then: call pair(p) -> return its result
    let k = caller.block(vec![Var(99)]);
    caller.set_terminator(
        then_b,
        Term::Call {
            ident: CallsiteIdent::from_source(span(10, 20)),
            callee: FnId(0),
            args: vec![p],
            continuation: Cont {
                fn_id: FnId(2),
                captured: vec![],
            },
        },
    );
    caller.set_terminator(k, Term::Return(Var(99)));
    // else: build a closure capturing p, then return it
    let clos = caller.let_(else_b, Prim::make_closure(span(30, 40), FnId(0), vec![p]));
    caller.set_terminator(else_b, Term::Return(clos));

    let mut mb = ModuleBuilder::new();
    mb.add_fn(callee.build());
    mb.add_fn(caller.build());
    let mut m = mb.build();
    m.atom_names = vec!["a0".into(), "a1".into(), "a2".into(), "ok".into()];
    // Populate the tuple-keyed span side-tables to exercise their
    // sequence-based serialization.
    m.source.stmt_spans.insert((FnId(1), BlockId(2)), vec![span(30, 40)]);
    m.source.term_span.insert((FnId(1), BlockId(0)), span(0, 5));

    // Canonical, order-independent round-trip (serde_json::Value sorts
    // object keys), so equality is structural, not textual.
    let v1 = serde_json::to_value(&m).unwrap();
    let back: Module = serde_json::from_value(v1.clone()).unwrap();
    let v2 = serde_json::to_value(&back).unwrap();
    assert_eq!(v1, v2);

    // Spans survive: the Call ident's span is load-bearing identity.
    let back_caller = back.fns.iter().find(|f| f.name == "go").unwrap();
    match &back_caller.block(BlockId(1)).terminator {
        Term::Call { ident, .. } => assert_eq!(ident.span(), span(10, 20)),
        other => panic!("expected Call, got {:?}", other),
    }

    // The skipped indices reconstruct.
    let mut back = back;
    back.rebuild_indices();
    assert_eq!(back.fn_by_id(FnId(0)).name, "pair");
    assert_eq!(back.fn_by_id(FnId(1)).name, "go");
}

/// fz-t1m.3.1.6 — `Module::remap_file_ids` rewrites the `file` of every
/// span reachable from the module. Builds a module populating EVERY span
/// site, places one span in an unmapped file and one DUMMY span, applies
/// `{FileId(7) -> FileId(3)}`, and asserts every FileId(7) span (including
/// the receive dispatch plan's) became FileId(3) while FileId(9) and DUMMY are
/// untouched.
#[test]
fn remap_file_ids_rewrites_every_span_site() {
    use crate::dispatch_matrix::pattern::{
        PatternDispatchOutcome, PatternDispatchPlan, PatternInput, PatternPinnedInput, PatternSubjectRef,
    };
    use crate::dispatch_matrix::{
        DispatchGraph, DispatchMatrix, DispatchNode, EdgeEvidence, GraphNodeId, Order, Outcome, OutcomeId,
        OutcomeMultiplicity, Subject, SubjectId, SubjectSource,
    };
    use std::sync::Arc;

    let f7 = FileId(7);
    let f9 = FileId(9);
    let s7 = |start, end| Span::new(f7, start, end);

    // One fn carrying a MakeClosure (Prim span), a Term::Call (ident span),
    // and a Term::ReceiveMatched whose dispatch plan carries non-DUMMY spans.
    let mut b = FnBuilder::new(FnId(0), "host");
    let p = b.fresh_var();
    let entry = b.block(vec![p]);
    let call_b = b.block(vec![]);
    let recv_b = b.block(vec![]);
    let k = b.block(vec![Var(99)]);

    // entry: MakeClosure (Prim span at f7) then Goto call_b.
    let _clos = b.let_(entry, Prim::make_closure(s7(30, 40), FnId(0), vec![p]));
    b.set_terminator(entry, Term::Goto(call_b, vec![]));

    // call_b: Term::Call with a non-DUMMY ident span at f7.
    b.set_terminator(
        call_b,
        Term::Call {
            ident: CallsiteIdent::from_source(s7(10, 20)),
            callee: FnId(0),
            args: vec![p],
            continuation: Cont {
                fn_id: FnId(0),
                captured: vec![],
            },
        },
    );

    // recv_b: Term::ReceiveMatched with clause/after spans + a dispatch plan
    // whose input and outcome spans live in f7.
    let dispatch = {
        PatternDispatchPlan {
            matrix: DispatchMatrix {
                subjects: vec![Subject {
                    id: SubjectId(0),
                    source: SubjectSource::Input { ordinal: 0 },
                }],
                outcomes: vec![Outcome {
                    id: OutcomeId(0),
                    multiplicity: OutcomeMultiplicity::Unique,
                }],
                arms: vec![],
                order: Order::Source,
            },
            graph: DispatchGraph {
                nodes: vec![DispatchNode::Outcome {
                    outcome: OutcomeId(0),
                    evidence: EdgeEvidence::empty(),
                }],
                root: GraphNodeId(0),
            },
            inputs: vec![PatternInput {
                var: Some(p),
                span: s7(50, 51),
            }],
            subjects: vec![Some(PatternSubjectRef::Input(0))],
            outcomes: vec![PatternDispatchOutcome {
                outcome: OutcomeId(0),
                body_id: 0,
                bindings: Vec::new(),
                span: s7(52, 53),
            }],
            guards: vec![],
            pinned: vec![PatternPinnedInput {
                name: "keep".to_string(),
                var: None,
                span: Span::new(f9, 54, 55),
            }],
            prepared_keys: vec![],
            bitstring_direct_bindings: HashMap::new(),
        }
    };
    b.set_terminator(
        recv_b,
        Term::ReceiveMatched {
            ident: CallsiteIdent::from_source(s7(60, 61)),
            clauses: vec![ReceiveClause {
                ident: CallsiteIdent::from_source(s7(62, 63)),
                bound_names: vec![],
                guard: None,
                body: FnId(0),
                span: s7(62, 63),
            }],
            dispatch: Arc::new(dispatch),
            after: Some(ReceiveAfter {
                ident: CallsiteIdent::from_source(s7(64, 65)),
                timeout: p,
                body: FnId(0),
                span: s7(64, 65),
            }),
            pinned: vec![],
            captures: vec![],
        },
    );
    b.set_terminator(k, Term::Return(Var(99)));

    let mut mb = ModuleBuilder::new();
    mb.add_fn(b.build());
    let mut m = mb.build();

    // SourceInfo side-tables: var_span, fn_span, stmt_spans, term_span.
    // Slot 0 = f7, slot 1 = f9 (unmapped), slot 2 = DUMMY.
    m.source.var_span = vec![s7(0, 1), Span::new(f9, 2, 3), Span::DUMMY];
    m.source.fn_span = vec![s7(4, 5)];
    m.source.stmt_spans.insert((FnId(0), BlockId(0)), vec![s7(6, 7)]);
    m.source.term_span.insert((FnId(0), BlockId(1)), s7(8, 9));

    // external_call_edge whose callsite ident span is non-DUMMY (f7).
    let export = ExportKey::new(ModuleName::from_segments(vec!["A".to_string()]), "f", 0);
    m.external_call_edges.push(ExternalCallEdge {
        callsite: CallsiteId::new(FnId(0), &CallsiteIdent::from_source(s7(70, 71)), EmitSlot::Direct),
        target: export,
    });

    let remap: HashMap<FileId, FileId> = [(FileId(7), FileId(3))].into_iter().collect();
    m.remap_file_ids(&remap);

    let f3 = FileId(3);
    // SourceInfo: f7 -> f3; f9 and DUMMY unchanged.
    assert_eq!(m.source.var_span[0].file, f3, "var_span f7");
    assert_eq!(m.source.var_span[1].file, f9, "var_span f9 untouched");
    assert!(m.source.var_span[2].is_dummy(), "var_span DUMMY untouched");
    assert_eq!(m.source.fn_span[0].file, f3, "fn_span f7");
    assert_eq!(m.source.stmt_spans[&(FnId(0), BlockId(0))][0].file, f3, "stmt_span f7");
    assert_eq!(m.source.term_span[&(FnId(0), BlockId(1))].file, f3, "term_span f7");

    // Per-fn spans.
    let host = m.fn_by_name("host").unwrap();
    match host.block(BlockId(0)).stmts.first() {
        Some(Stmt::Let(_, Prim::MakeClosure(ident, ..))) => {
            assert_eq!(ident.span().file, f3, "MakeClosure ident f7")
        }
        other => panic!("expected MakeClosure, got {:?}", other),
    }
    match &host.block(BlockId(1)).terminator {
        Term::Call { ident, .. } => assert_eq!(ident.span().file, f3, "Call ident f7"),
        other => panic!("expected Call, got {:?}", other),
    }
    match &host.block(BlockId(2)).terminator {
        Term::ReceiveMatched {
            ident,
            clauses,
            dispatch,
            after,
            ..
        } => {
            assert_eq!(ident.span().file, f3, "Receive ident f7");
            assert_eq!(clauses[0].span.file, f3, "ReceiveClause f7");
            assert_eq!(after.as_ref().unwrap().span.file, f3, "ReceiveAfter f7");
            assert_eq!(dispatch.inputs[0].span.file, f3, "dispatch input f7");
            assert_eq!(dispatch.outcomes[0].span.file, f3, "dispatch outcome f7");
            assert_eq!(dispatch.pinned[0].span.file, f9, "dispatch f9 pinned untouched");
        }
        other => panic!("expected ReceiveMatched, got {:?}", other),
    }

    // external_call_edge ident span.
    assert_eq!(
        m.external_call_edges[0].callsite.ident.span().file,
        f3,
        "external edge ident f7"
    );
}

/// fz-t1m.3.1.2 — `Module::referenced_files` is the read-only twin of
/// `remap_file_ids`: it collects every non-`NONE` `FileId` its spans touch.
/// Populates spans at FileId(7) and FileId(9) plus a DUMMY span and asserts
/// exactly {FileId(7), FileId(9)} comes back — DUMMY excluded.
#[test]
fn referenced_files_collects_non_dummy_file_ids() {
    let f7 = FileId(7);
    let f9 = FileId(9);

    // A trivial fn so the module is well-formed; its body carries no spans.
    let mut b = FnBuilder::new(FnId(0), "host");
    let x = b.fresh_var();
    let entry = b.block(vec![x]);
    b.set_terminator(entry, Term::Return(x));
    let mut mb = ModuleBuilder::new();
    mb.add_fn(b.build());
    let mut m = mb.build();

    // SourceInfo spans across two files plus a DUMMY that must be excluded.
    m.source.var_span = vec![Span::new(f7, 0, 1), Span::new(f9, 2, 3), Span::DUMMY];

    let files = m.referenced_files();
    assert_eq!(
        files,
        [f7, f9].into_iter().collect::<BTreeSet<_>>(),
        "referenced_files returns exactly the non-DUMMY files"
    );
}

/// fn identity(x) = x
fn build_identity() -> FnIr {
    let mut b = FnBuilder::new(FnId(0), "identity");
    let x = b.fresh_var();
    let entry = b.block(vec![x]);
    b.set_terminator(entry, Term::Return(x));
    b.build()
}

/// fn add1(x) = x + 1
fn build_add1() -> FnIr {
    let mut b = FnBuilder::new(FnId(1), "add1");
    let x = b.fresh_var();
    let entry = b.block(vec![x]);
    let one = b.let_(entry, Prim::Const(Const::Int(1)));
    let sum = b.let_(entry, Prim::BinOp(BinOp::Add, x, one));
    b.set_terminator(entry, Term::Return(sum));
    b.build()
}

/// fn iszero(x) = if x == 0 then true else false
fn build_iszero() -> FnIr {
    let mut b = FnBuilder::new(FnId(2), "iszero");
    let x = b.fresh_var();
    let entry = b.block(vec![x]);
    let zero = b.let_(entry, Prim::Const(Const::Int(0)));
    let cond = b.let_(entry, Prim::BinOp(BinOp::Eq, x, zero));
    let then_b = b.block(vec![]);
    let else_b = b.block(vec![]);
    b.set_terminator(entry, Term::if_user(cond, then_b, else_b));
    let t = b.let_(then_b, Prim::Const(Const::True));
    b.set_terminator(then_b, Term::Return(t));
    let fl = b.let_(else_b, Prim::Const(Const::False));
    b.set_terminator(else_b, Term::Return(fl));
    b.build()
}

#[test]
fn build_identity_fn_has_one_block_and_returns_param() {
    let fn_ir = build_identity();
    assert_eq!(fn_ir.name, "identity");
    assert_eq!(fn_ir.blocks.len(), 1);
    assert_eq!(fn_ir.entry, BlockId(0));
    let entry = fn_ir.block(BlockId(0));
    assert_eq!(entry.params.len(), 1);
    assert!(entry.stmts.is_empty());
    match entry.terminator {
        Term::Return(v) => assert_eq!(v, Var(0)),
        _ => panic!("expected Return"),
    }
}

#[test]
fn fresh_vars_are_unique() {
    let mut b = FnBuilder::new(FnId(0), "f");
    let a = b.fresh_var();
    let c = b.fresh_var();
    assert_ne!(a, c);
}

#[test]
fn physical_entry_params_are_not_semantic_key_inputs() {
    use crate::types::Types;

    let mut b = FnBuilder::new(FnId(0), "with_physical");
    let head = b.fresh_var();
    let source = b.fresh_var();
    let value = b.fresh_var();
    let entry = b.block(vec![source, value]);
    b.record_owned_cons_reuse_capability(head, source);
    b.set_terminator(entry, Term::Return(value));
    let fn_ir = b.build();

    assert_eq!(fn_ir.physical_entry_params, vec![source]);
    assert_eq!(
        fn_ir.physical_capabilities,
        vec![PhysicalCapabilityFact {
            source,
            capability: PhysicalCapability::OwnedConsReuse { head },
        }]
    );
    assert_eq!(fn_ir.semantic_entry_params(), vec![value]);

    let mut t = crate::types::new();
    let key = fn_ir.semantic_key(vec![t.any(), t.int()]);
    assert!(key[0].is_none());
    assert!(key[1].is_some());
}

#[test]
fn build_add1_has_two_lets_and_returns_sum() {
    let fn_ir = build_add1();
    let entry = fn_ir.block(fn_ir.entry);
    assert_eq!(entry.stmts.len(), 2);
    match &entry.stmts[0] {
        Stmt::Let(_, Prim::Const(Const::Int(1))) => {}
        other => panic!("expected let _ = const(1), got {:?}", other),
    }
    match &entry.stmts[1] {
        Stmt::Let(_, Prim::BinOp(BinOp::Add, _, _)) => {}
        other => panic!("expected let _ = add, got {:?}", other),
    }
}

#[test]
fn build_iszero_has_three_blocks_with_if_then_else() {
    let fn_ir = build_iszero();
    assert_eq!(fn_ir.blocks.len(), 3);
    let entry = fn_ir.block(fn_ir.entry);
    match entry.terminator {
        Term::If { then_b, else_b, .. } => {
            assert_ne!(then_b, else_b);
            assert_eq!(then_b, BlockId(1));
            assert_eq!(else_b, BlockId(2));
        }
        _ => panic!("expected If terminator"),
    }
}

#[test]
fn module_holds_multiple_fns_and_lookup_by_name() {
    let mut mb = ModuleBuilder::new();
    mb.add_fn(build_identity());
    mb.add_fn(build_add1());
    let m = mb.build();
    assert_eq!(m.fns.len(), 2);
    assert!(m.fn_by_name("identity").is_some());
    assert!(m.fn_by_name("add1").is_some());
    assert!(m.fn_by_name("missing").is_none());
    assert_eq!(m.fn_by_id(FnId(0)).name, "identity");
    assert_eq!(m.fn_by_id(FnId(1)).name, "add1");
}

#[test]
fn lto_rewrites_external_call_edge_to_direct_fn_id() {
    let ident = CallsiteIdent::synthetic();
    let mut caller = FnBuilder::new(FnId(0), "caller");
    let entry = caller.block(vec![]);
    caller.set_terminator(
        entry,
        Term::TailCall {
            ident: ident.clone(),
            callee: FnId(999),
            args: Vec::new(),
            is_back_edge: false,
        },
    );
    let mut target = FnBuilder::new(FnId(1), "A.f");
    let target_entry = target.block(vec![]);
    target.set_terminator(target_entry, Term::Halt(Var(0)));
    let mut mb = ModuleBuilder::new();
    mb.add_fn(caller.build());
    mb.add_fn(target.build());
    let mut module = mb.build();
    let export = ExportKey::new(ModuleName::from_segments(vec!["A".to_string()]), "f", 0);
    module.external_call_edges.push(ExternalCallEdge {
        callsite: CallsiteId::new(FnId(0), &ident, EmitSlot::Direct),
        target: export.clone(),
    });
    let exports = [(export, FnId(1))].into_iter().collect();

    assert_eq!(module.rewrite_external_calls_for_lto(&exports), Ok(1));
    assert!(module.external_call_edges.is_empty());
    match &module.fn_by_id(FnId(0)).block(BlockId(0)).terminator {
        Term::TailCall { callee, .. } => assert_eq!(*callee, FnId(1)),
        other => panic!("expected TailCall, got {:?}", other),
    }
}

#[test]
fn lto_reports_missing_external_call_target() {
    let ident = CallsiteIdent::synthetic();
    let mut caller = FnBuilder::new(FnId(0), "caller");
    let entry = caller.block(vec![]);
    caller.set_terminator(
        entry,
        Term::TailCall {
            ident: ident.clone(),
            callee: FnId(999),
            args: Vec::new(),
            is_back_edge: false,
        },
    );
    let mut mb = ModuleBuilder::new();
    mb.add_fn(caller.build());
    let mut module = mb.build();
    let export = ExportKey::new(ModuleName::from_segments(vec!["Missing".to_string()]), "f", 0);
    module.external_call_edges.push(ExternalCallEdge {
        callsite: CallsiteId::new(FnId(0), &ident, EmitSlot::Direct),
        target: export.clone(),
    });
    let exports = BTreeMap::new();

    assert_eq!(
        module.rewrite_external_calls_for_lto(&exports),
        Err(ExternalLinkError::MissingTarget(export))
    );
    assert!(!module.external_call_edges.is_empty());
}

#[test]
fn lto_export_map_comes_from_validated_interfaces() {
    let mut target = FnBuilder::new(FnId(7), "Math.add");
    let target_entry = target.block(vec![Var(0), Var(1)]);
    target.set_terminator(target_entry, Term::Halt(Var(0)));
    let mut mb = ModuleBuilder::new();
    mb.add_fn(target.build());
    let module = mb.build();

    let math = ModuleName::from_segments(vec!["Math".to_string()]);
    let mut interfaces = BTreeMap::new();
    interfaces.insert(
        math.clone(),
        ModuleInterface {
            name: math.clone(),
            abi_version: FZ_INTERFACE_ABI_VERSION,
            imports: Vec::new(),
            exports: vec![InterfaceFn {
                name: "add".to_string(),
                arity: 2,
                specs: vec![InterfaceSpec {
                    params: vec!["Ident(\"integer\")".to_string(), "Ident(\"integer\")".to_string()],
                    result: "Ident(\"integer\")".to_string(),
                }],
                name_span: Span::DUMMY,
            }],
            types: Vec::new(),
            protocols: Vec::new(),
            protocol_impls: Vec::new(),
            docs: None,
            fingerprint_inputs: Vec::new(),
        },
    );

    let key = ExportKey::new(math, "add", 2);
    assert_eq!(module.interface_export_map(&interfaces).get(&key), Some(&FnId(7)));
}

#[test]
fn module_holds_schemas() {
    use fz_runtime::heap::{FieldDescriptor, FieldKind};
    let mut mb = ModuleBuilder::new();
    let id = mb.add_schema(Schema {
        name: "Frame_identity".into(),
        size: 16,
        fields: vec![FieldDescriptor {
            offset: 0,
            kind: FieldKind::AnyValue,
            name: None,
        }],
    });
    assert_eq!(id, 0);
    let m = mb.build();
    assert_eq!(m.schemas.len(), 1);
    assert_eq!(m.schemas[0].name, "Frame_identity");
}

#[test]
fn pretty_print_identity() {
    let fn_ir = build_identity();
    let s = format!("{}", fn_ir);
    assert!(s.contains("fn0 identity"));
    assert!(s.contains("entry=bb0"));
    assert!(s.contains("bb0(v0):"));
    assert!(s.contains("return v0"));
}

#[test]
fn pretty_print_add1() {
    let fn_ir = build_add1();
    let s = format!("{}", fn_ir);
    assert!(s.contains("let v1 = const(1)"));
    assert!(s.contains("let v2 = v0 + v1"));
    assert!(s.contains("return v2"));
}

#[test]
fn pretty_print_iszero_branches() {
    let fn_ir = build_iszero();
    let s = format!("{}", fn_ir);
    assert!(s.contains("if v2 then bb1 else bb2"));
    assert!(s.contains("return"));
}

#[test]
fn pretty_print_module() {
    let mut mb = ModuleBuilder::new();
    mb.add_fn(build_identity());
    mb.add_fn(build_add1());
    let m = mb.build();
    let s = format!("{}", m);
    assert!(s.starts_with("module"));
    assert!(s.contains("identity"));
    assert!(s.contains("add1"));
}

#[test]
fn term_call_with_continuation_round_trips() {
    let mut b = FnBuilder::new(FnId(3), "caller");
    let x = b.fresh_var();
    let entry = b.block(vec![x]);
    b.set_terminator(
        entry,
        Term::Call {
            ident: CallsiteIdent::synthetic(),
            callee: FnId(0),
            args: vec![x],
            continuation: Cont {
                fn_id: FnId(7),
                captured: vec![x],
            },
        },
    );
    let fn_ir = b.build();
    let s = format!("{}", fn_ir);
    assert!(s.contains("call fn0([v0]) -> cont(fn7, captured=[v0])"));
}

#[test]
fn term_tail_call() {
    let mut b = FnBuilder::new(FnId(4), "tc");
    let x = b.fresh_var();
    let entry = b.block(vec![x]);
    b.set_terminator(
        entry,
        Term::TailCall {
            ident: CallsiteIdent::synthetic(),
            callee: FnId(0),
            args: vec![x],
            is_back_edge: false,
        },
    );
    let fn_ir = b.build();
    let s = format!("{}", fn_ir);
    assert!(s.contains("tail_call fn0([v0])"));
}

#[test]
fn term_halt_pretty_prints() {
    let mut b = FnBuilder::new(FnId(5), "top");
    let entry = b.block(vec![]);
    let v = b.let_(entry, Prim::Const(Const::Int(42)));
    b.set_terminator(entry, Term::Halt(v));
    let s = format!("{}", b.build());
    assert!(s.contains("halt v0"));
}

#[test]
fn list_prims_pretty_print() {
    let mut b = FnBuilder::new(FnId(6), "lst");
    let entry = b.block(vec![]);
    let one = b.let_(entry, Prim::Const(Const::Int(1)));
    let l = b.let_(entry, Prim::MakeList(vec![one], None));
    let h = b.let_(entry, Prim::ListHead(l));
    let _t = b.let_(entry, Prim::ListTail(l));
    let _z = b.let_(entry, Prim::IsEmptyList(l));
    b.set_terminator(entry, Term::Return(h));
    let s = format!("{}", b.build());
    assert!(s.contains("list([v0])"));
    assert!(s.contains("head(v1)"));
    assert!(s.contains("tail(v1)"));
    assert!(s.contains("is_nil(v1)"));
}

#[test]
fn goto_with_args_pretty_prints() {
    let mut b = FnBuilder::new(FnId(8), "g");
    let x = b.fresh_var();
    let entry = b.block(vec![x]);
    let next = b.block(vec![Var(99)]);
    b.set_terminator(entry, Term::Goto(next, vec![x]));
    b.set_terminator(next, Term::Return(Var(99)));
    let s = format!("{}", b.build());
    assert!(s.contains("goto bb1(v0)"));
}
