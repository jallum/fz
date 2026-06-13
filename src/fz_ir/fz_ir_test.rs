use super::*;
use crate::modules::identity::ModuleName;
use crate::modules::interface::{InterfaceFn, InterfaceSpec, ModuleInterface};

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
    b.record_reusable_cons_cell(head, source);
    b.set_terminator(entry, Term::Return(value));
    let fn_ir = b.build();

    assert_eq!(fn_ir.physical_entry_params, vec![source]);
    assert_eq!(
        fn_ir.physical_capabilities,
        vec![PhysicalCapabilityFact {
            source,
            capability: PhysicalCapability::ReusableConsCell { rebuilt_head: head },
        }]
    );
    assert_eq!(fn_ir.semantic_entry_params(), vec![value]);

    let mut t = crate::types::new();
    let key = fn_ir.semantic_key(vec![t.any(), t.int()]);
    assert!(key[0].is_none());
    assert!(key[1].is_some());
}

#[test]
fn local_reusable_cons_sources_do_not_become_physical_entry_params() {
    let mut b = FnBuilder::new(FnId(0), "local_reusable_cons");
    let entry = b.block(vec![]);
    let source = b.let_(entry, Prim::Const(Const::Int(1)));
    let head = b.let_(entry, Prim::Const(Const::Int(2)));
    b.record_reusable_cons_cell(head, source);
    b.set_terminator(entry, Term::Return(head));
    let fn_ir = b.build();

    assert!(
        fn_ir.physical_entry_params.is_empty(),
        "local reusable-cons sources should stay local metadata, not hidden entry params",
    );
    assert_eq!(
        fn_ir.physical_capabilities,
        vec![PhysicalCapabilityFact {
            source,
            capability: PhysicalCapability::ReusableConsCell { rebuilt_head: head },
        }],
        "the reusable-cons capability should still be recorded for local codegen consumption",
    );
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
            ident,
            callee: DirectCallTarget::ProviderBoundary(Mfa::new(
                ModuleName::from_segments(vec!["A".to_string()]),
                "f",
                0,
            )),
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
    let export = Mfa::new(ModuleName::from_segments(vec!["A".to_string()]), "f", 0);
    let exports = [(export, FnId(1))].into_iter().collect();

    assert_eq!(module.rewrite_external_calls_for_lto(&exports), Ok(1));
    assert!(module.external_call_edges().is_empty());
    match &module.fn_by_id(FnId(0)).block(BlockId(0)).terminator {
        Term::TailCall { callee, .. } => assert_eq!(*callee, DirectCallTarget::Local(FnId(1))),
        other => panic!("expected TailCall, got {:?}", other),
    }
}

#[test]
fn lto_reports_missing_external_call_target() {
    let ident = CallsiteIdent::synthetic();
    let mut caller = FnBuilder::new(FnId(0), "caller");
    let entry = caller.block(vec![]);
    let export = Mfa::new(ModuleName::from_segments(vec!["Missing".to_string()]), "f", 0);
    caller.set_terminator(
        entry,
        Term::TailCall {
            ident,
            callee: DirectCallTarget::ProviderBoundary(export.clone()),
            args: Vec::new(),
            is_back_edge: false,
        },
    );
    let mut mb = ModuleBuilder::new();
    mb.add_fn(caller.build());
    let mut module = mb.build();
    let exports = BTreeMap::new();

    assert_eq!(
        module.rewrite_external_calls_for_lto(&exports),
        Err(ExternalLinkError::MissingTarget(export))
    );
    assert!(!module.external_call_edges().is_empty());
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

    let key = Mfa::new(math, "add", 2);
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
            callee: DirectCallTarget::Local(FnId(0)),
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
            callee: DirectCallTarget::Local(FnId(0)),
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
