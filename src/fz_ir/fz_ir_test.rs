use super::*;

/// fn identity(x) = x
fn build_identity() -> FnIr {
    let mut b = FnBuilder::new(FnId(0), "identity");
    let x = b.fresh_var();
    let entry = b.block(vec![x]);
    b.set_terminator(entry, Term::Return(x));
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
    let mut b = FnBuilder::new(FnId(0), "with_physical");
    let source = b.fresh_var();
    let value = b.fresh_var();
    let entry = b.block(vec![source, value]);
    b.record_physical_entry_param(source);
    b.set_terminator(entry, Term::Return(value));
    let fn_ir = b.build();

    assert_eq!(fn_ir.physical_entry_params, vec![source]);

    assert_eq!(fn_ir.semantic_entry_params(), vec![value]);
}

#[test]
fn list_retention_source_is_a_traced_construction_operand() {
    let source = Var(0);
    let head = Var(1);
    let tail = Var(2);
    let prim = Prim::MakeList(
        vec![head],
        Some(tail),
        Some(ListRetention {
            source,
            permission: RewritePermission::RetainOnly,
        }),
    );
    let mut used = crate::fast_hash::HashSet::default();
    prim.collect_used_vars(&mut used);
    assert_eq!(used, [source, head, tail].into_iter().collect());
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
    mb.add_fn(build_iszero());
    let m = mb.build();
    assert_eq!(m.fns.len(), 2);
    assert_eq!(m.fn_by_id(FnId(0)).name, "identity");
    assert_eq!(m.fn_by_id(FnId(2)).name, "iszero");
}

#[test]
fn module_holds_schemas() {
    use fz_runtime::heap::{FieldDescriptor, FieldKind};
    let mut mb = ModuleBuilder::new();
    let id = mb.add_schema(Schema {
        identity: fz_runtime::heap::SchemaIdentity::Internal("Frame_identity".into()),
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
    assert_eq!(m.schemas[0].identity.display_name(), "Frame_identity");
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
    mb.add_fn(build_iszero());
    let m = mb.build();
    let s = format!("{}", m);
    assert!(s.starts_with("module"));
    assert!(s.contains("identity"));
    assert!(s.contains("iszero"));
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
fn term_raise_pretty_prints_the_value_it_raises() {
    let mut b = FnBuilder::new(FnId(5), "top");
    let entry = b.block(vec![]);
    let value = b.let_(entry, Prim::Const(Const::Int(3)));
    b.set_terminator(entry, Term::Raise { value });
    let s = format!("{}", b.build());
    assert!(s.contains("raise v0"), "{s}");
}

#[test]
fn a_block_left_without_a_terminator_is_unreachable() {
    let mut b = FnBuilder::new(FnId(5), "top");
    b.block(vec![]);
    let s = format!("{}", b.build());
    assert!(s.contains("unreachable"), "{s}");
}

#[test]
fn list_prims_pretty_print() {
    let mut b = FnBuilder::new(FnId(6), "lst");
    let entry = b.block(vec![]);
    let one = b.let_(entry, Prim::Const(Const::Int(1)));
    let l = b.let_(entry, Prim::MakeList(vec![one], None, None));
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

/// A foreign signature spells a parameter once, however many words carry it:
/// a walked binary travels as its source and its bit position, and every
/// other type is the single class it names. The whole-list form is those
/// per-parameter classes laid end to end.
#[test]
fn a_parameter_occupies_the_words_that_carry_it() {
    assert_eq!(
        ExternTy::BinaryCursor.wire().collect::<Vec<_>>(),
        vec![ExternTy::Any, ExternTy::I64]
    );
    assert_eq!(ExternTy::F64.wire().collect::<Vec<_>>(), vec![ExternTy::F64]);
    assert_eq!(
        ExternTy::wire_classes(&[ExternTy::I64, ExternTy::BinaryCursor, ExternTy::Bool]),
        vec![ExternTy::I64, ExternTy::Any, ExternTy::I64, ExternTy::Bool]
    );
}

/// Intent: a builder's block ids are positions, so a statement appended to any
/// block lands in exactly that block however many blocks exist.
#[test]
fn builder_appends_land_in_the_block_named_by_id_across_many_blocks() {
    let mut b = FnBuilder::new(FnId(0), "many");
    let ids: Vec<BlockId> = (0..500).map(|_| b.block(vec![])).collect();
    // Interleave late and early appends so lookup order cannot matter.
    let mut bound = Vec::new();
    for (round, id) in ids.iter().rev().chain(ids.iter()).enumerate() {
        bound.push((*id, b.let_(*id, Prim::Const(Const::Int(round as i64)))));
    }
    for id in &ids {
        b.set_terminator(
            *id,
            Term::Return(bound.iter().find(|(owner, _)| owner == id).unwrap().1),
        );
    }
    let f = b.build();
    assert_eq!(f.entry, ids[0]);
    for (position, id) in ids.iter().enumerate() {
        assert_eq!(id.0 as usize, position, "ids are creation positions");
        let block = f.block(*id);
        assert_eq!(block.id, *id);
        let owned: Vec<Var> = bound.iter().filter(|(owner, _)| owner == id).map(|(_, v)| *v).collect();
        let stmt_vars: Vec<Var> = block
            .stmts
            .iter()
            .map(|s| match s {
                Stmt::Let(v, _) => *v,
                other => panic!("unexpected stmt {other:?}"),
            })
            .collect();
        assert_eq!(stmt_vars, owned);
    }
}

#[test]
fn a_block_read_through_the_function_is_the_block_with_that_id() {
    let mut b = FnBuilder::new(FnId(7), "many_blocks");
    let ids: Vec<BlockId> = (0..64)
        .map(|_| {
            let param = b.fresh_var();
            let block = b.block(vec![param]);
            b.set_terminator(block, Term::Return(param));
            block
        })
        .collect();
    let mut fn_ir = b.build();

    for id in &ids {
        let block = fn_ir.block(*id);
        assert_eq!(block.id, *id);
        assert_eq!(block.terminator, Term::Return(block.params[0]));
    }
    let last = *ids.last().unwrap();
    fn_ir
        .block_mut(last)
        .stmts
        .push(Stmt::Let(Var(99), Prim::Const(Const::True)));
    assert_eq!(fn_ir.block(last).stmts.len(), 1);
    assert!(fn_ir.block(ids[0]).stmts.is_empty());
}
