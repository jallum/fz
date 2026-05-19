use super::*;
use crate::fz_ir::{BinOp, Const, FnBuilder, FnId, ModuleBuilder, Prim, Term, Var};

fn build_module(fns: Vec<crate::fz_ir::FnIr>) -> Module {
    let mut mb = ModuleBuilder::new();
    for f in fns {
        mb.add_fn(f);
    }
    mb.build()
}

/// fz-pky.2 — test helper. Returns "the most narrow registered
/// spec for fn at index i, or an ad-hoc any-key view if unregistered."
fn fn_view(m: &Module, mt: &ModuleTypes, i: usize) -> FnTypes {
    let fid = m.fns[i].id;
    if let Some(ft) = mt.any_spec_for(fid) {
        return ft.clone();
    }
    // Unreachable fn — type ad-hoc under all-any.
    let n_params = m.fns[i].block(m.fns[i].entry).params.len();
    let any_key: Vec<Descr> = vec![Descr::any(); n_params];
    type_fn(&m.fns[i], m, Some(&any_key))
}

// ---- .24.2 tests (preserved, adjusted to FnTypes API) ----

#[test]
fn const_int_typed_as_singleton() {
    let mut b = FnBuilder::new(FnId(0), "main");
    let entry = b.block(vec![]);
    let v = b.let_(entry, Prim::Const(Const::Int(42)));
    b.set_terminator(entry, Term::Halt(v));
    let m = build_module(vec![b.build()]);
    let mt = type_module(&m);
    assert!(
        fn_view(&m, &mt, 0)
            .vars
            .get(&v)
            .unwrap()
            .is_equiv(&Descr::int_lit(42))
    );
}

#[test]
fn add1_body_is_int_top_when_param_is_any() {
    let mut b = FnBuilder::new(FnId(0), "add1");
    let x = b.fresh_var();
    let entry = b.block(vec![x]);
    let one = b.let_(entry, Prim::Const(Const::Int(1)));
    let sum = b.let_(entry, Prim::BinOp(BinOp::Add, x, one));
    b.set_terminator(entry, Term::Return(sum));
    let m = build_module(vec![b.build()]);
    let mt = type_module(&m);
    let sum_t = fn_view(&m, &mt, 0).vars.get(&sum).cloned().unwrap();
    assert!(
        sum_t.is_equiv(&Descr::int().union(&Descr::float())),
        "got {}",
        sum_t
    );
}

#[test]
fn make_list_of_ints() {
    let mut b = FnBuilder::new(FnId(0), "f");
    let entry = b.block(vec![]);
    let a = b.let_(entry, Prim::Const(Const::Int(1)));
    let bv = b.let_(entry, Prim::Const(Const::Int(2)));
    let cv = b.let_(entry, Prim::Const(Const::Int(3)));
    let l = b.let_(entry, Prim::MakeList(vec![a, bv, cv], None));
    b.set_terminator(entry, Term::Return(l));
    let m = build_module(vec![b.build()]);
    let mt = type_module(&m);
    let lt = fn_view(&m, &mt, 0).vars.get(&l).cloned().unwrap();
    let elem = crate::typer::list_element_type(&lt);
    assert!(elem.is_subtype(&Descr::int()), "list elem: {}", elem);
    assert!(!elem.is_empty());
}

#[test]
fn goto_joins_param_types_across_predecessors() {
    let mut b = FnBuilder::new(FnId(0), "join");
    let entry = b.block(vec![]);
    let zero = b.let_(entry, Prim::Const(Const::Int(0)));
    let bb1 = b.block(vec![]);
    let bb2 = b.block(vec![]);
    let joined = Var(99);
    let bb3 = b.block(vec![joined]);
    b.set_terminator(entry, Term::if_user(zero, bb1, bb2));
    let one = b.let_(bb1, Prim::Const(Const::Int(1)));
    b.set_terminator(bb1, Term::Goto(bb3, vec![one]));
    let two = b.let_(bb2, Prim::Const(Const::Int(2)));
    b.set_terminator(bb2, Term::Goto(bb3, vec![two]));
    b.set_terminator(bb3, Term::Return(joined));
    let m = build_module(vec![b.build()]);
    let mt = type_module(&m);
    let join_t = fn_view(&m, &mt, 0).vars.get(&joined).cloned().unwrap();
    let expected = Descr::int_lit(1).union(&Descr::int_lit(2));
    assert!(join_t.is_equiv(&expected), "got {}", join_t);
}

// ---- .24.3 narrowing tests ----

#[test]
fn tuple_field_projects_elem_descr() {
    // fn f(t), do: TupleField(t, 0)
    //   - call site builds t = {1, :ok} so we have a concrete tuple shape.
    let mut b = FnBuilder::new(FnId(0), "f");
    let entry = b.block(vec![]);
    let one = b.let_(entry, Prim::Const(Const::Int(1)));
    let ok = b.let_(entry, Prim::Const(Const::Atom(7)));
    let t = b.let_(entry, Prim::MakeTuple(vec![one, ok]));
    let f0 = b.let_(entry, Prim::TupleField(t, 0));
    b.set_terminator(entry, Term::Return(f0));
    let m = build_module(vec![b.build()]);
    let mt = type_module(&m);
    let f0_t = fn_view(&m, &mt, 0).vars.get(&f0).cloned().unwrap();
    assert!(
        f0_t.is_subtype(&Descr::int_lit(1)) && Descr::int_lit(1).is_subtype(&f0_t),
        "field 0 should be int_lit(1), got {}",
        f0_t
    );
}

#[test]
fn list_head_yields_element_type() {
    let mut b = FnBuilder::new(FnId(0), "f");
    let entry = b.block(vec![]);
    let one = b.let_(entry, Prim::Const(Const::Int(1)));
    let two = b.let_(entry, Prim::Const(Const::Int(2)));
    let l = b.let_(entry, Prim::MakeList(vec![one, two], None));
    let h = b.let_(entry, Prim::ListHead(l));
    b.set_terminator(entry, Term::Return(h));
    let m = build_module(vec![b.build()]);
    let mt = type_module(&m);
    let h_t = fn_view(&m, &mt, 0).vars.get(&h).cloned().unwrap();
    // head type = list elem = union(int_lit(1), int_lit(2)) ⊆ int.
    assert!(h_t.is_subtype(&Descr::int()), "head type: {}", h_t);
}

#[test]
fn if_is_empty_list_narrows_v_to_empty_list_in_then_branch() {
    // Build:
    //   entry(l):
    //     c = IsEmptyList(l)
    //     if c then then_b else else_b
    //   then_b: return l   (l narrowed to empty list here)
    //   else_b: return l   (l narrowed to list_top here)
    let mut b = FnBuilder::new(FnId(0), "f");
    let l = b.fresh_var();
    let entry = b.block(vec![l]);
    let c = b.let_(entry, Prim::IsEmptyList(l));
    let then_b = b.block(vec![]);
    let else_b = b.block(vec![]);
    b.set_terminator(entry, Term::if_user(c, then_b, else_b));
    b.set_terminator(then_b, Term::Return(l));
    b.set_terminator(else_b, Term::Return(l));
    let m = build_module(vec![b.build()]);
    let mt = type_module(&m);

    // fz-s9y.3 — in then_b's entry env, l is narrowed to the empty
    // list, encoded in the lattice as list_of(none()). Pre-s9y.3 this
    // narrowed to Descr::nil() (the nil atom-like value), reflecting
    // the now-obsolete runtime conflation.
    let ft = fn_view(&m, &mt, 0);
    let then_env = ft.block_envs.get(&then_b).unwrap();
    let l_then = then_env.get(&l).cloned().unwrap();
    let empty_list = Descr::list_of(Descr::none());
    assert!(
        l_then.is_subtype(&empty_list) && empty_list.is_subtype(&l_then),
        "l in then-branch should be the empty list (list(none)): {}",
        l_then
    );

    // In else_b's entry env, l should be narrowed to list_top (no nil).
    let else_env = ft.block_envs.get(&else_b).unwrap();
    let l_else = else_env.get(&l).cloned().unwrap();
    // Subtype of list_of(any) (loosely: at least the list portion).
    assert!(
        l_else.is_subtype(&Descr::list_of(Descr::any())),
        "l in else-branch should be list-shaped: {}",
        l_else
    );
}

#[test]
fn if_eq_with_int_singleton_narrows_var_in_then_branch() {
    // entry(x):
    //   z = const(0)
    //   c = (x == z)
    //   if c then then_b else else_b
    let mut b = FnBuilder::new(FnId(0), "f");
    let x = b.fresh_var();
    let entry = b.block(vec![x]);
    let z = b.let_(entry, Prim::Const(Const::Int(0)));
    let c = b.let_(entry, Prim::BinOp(BinOp::Eq, x, z));
    let then_b = b.block(vec![]);
    let else_b = b.block(vec![]);
    b.set_terminator(entry, Term::if_user(c, then_b, else_b));
    b.set_terminator(then_b, Term::Return(x));
    b.set_terminator(else_b, Term::Return(x));
    let m = build_module(vec![b.build()]);
    let mt = type_module(&m);

    let ft = fn_view(&m, &mt, 0);
    let then_env = ft.block_envs.get(&then_b).unwrap();
    let x_then = then_env.get(&x).cloned().unwrap();
    assert!(
        x_then.is_subtype(&Descr::int_lit(0)) && Descr::int_lit(0).is_subtype(&x_then),
        "x in then-branch should be int_lit(0): {}",
        x_then
    );
}

#[test]
fn nested_tuple_projection() {
    // Build {inner, c} where inner = {a, b}; project field 0 to get inner,
    // then field 0 of that to get a.
    let mut b = FnBuilder::new(FnId(0), "f");
    let entry = b.block(vec![]);
    let a = b.let_(entry, Prim::Const(Const::Int(7)));
    let bv = b.let_(entry, Prim::Const(Const::Atom(3)));
    let inner = b.let_(entry, Prim::MakeTuple(vec![a, bv]));
    let c = b.let_(entry, Prim::Const(Const::Int(9)));
    let outer = b.let_(entry, Prim::MakeTuple(vec![inner, c]));
    let p0 = b.let_(entry, Prim::TupleField(outer, 0));
    let p00 = b.let_(entry, Prim::TupleField(p0, 0));
    b.set_terminator(entry, Term::Return(p00));
    let m = build_module(vec![b.build()]);
    let mt = type_module(&m);
    let p00_t = fn_view(&m, &mt, 0).vars.get(&p00).cloned().unwrap();
    assert!(
        p00_t.is_equiv(&Descr::int_lit(7)),
        "outer.0.0 should be int_lit(7), got {}",
        p00_t
    );
}

// ---- .24.6 unreachable-arm diagnostics ----

#[test]
fn list_is_nil_on_int_var_flags_both_branches_unreachable() {
    // entry():
    //   five = 5
    //   c = IsEmptyList(five)    -- predicate over an int -> both branches empty
    //   if c then then_b else else_b
    // then_b: halt five    -- env[five] narrowed to int_lit(5) ∩ nil = empty
    // else_b: halt five    -- env[five] narrowed to int_lit(5) ∩ list = empty
    let mut b = FnBuilder::new(FnId(0), "f");
    let entry = b.block(vec![]);
    let five = b.let_(entry, Prim::Const(Const::Int(5)));
    let c = b.let_(entry, Prim::IsEmptyList(five));
    let then_b = b.block(vec![]);
    let else_b = b.block(vec![]);
    b.set_terminator(entry, Term::if_user(c, then_b, else_b));
    b.set_terminator(then_b, Term::Halt(five));
    b.set_terminator(else_b, Term::Halt(five));
    let m = build_module(vec![b.build()]);
    let t = type_module(&m);
    let diags = collect_diagnostics(&m, &t);
    assert_eq!(
        diags.len(),
        2,
        "expected two unreachable arms, got {:?}",
        diags
    );
    assert!(
        diags
            .iter()
            .all(|d| d.code == crate::diag::codes::TYPE_UNREACHABLE_ARM)
    );
}

#[test]
fn happy_path_emits_no_warnings() {
    // entry(): halt 42  -- single-block, no narrowing, no warnings.
    let mut b = FnBuilder::new(FnId(0), "f");
    let entry = b.block(vec![]);
    let v = b.let_(entry, Prim::Const(Const::Int(42)));
    b.set_terminator(entry, Term::Halt(v));
    let m = build_module(vec![b.build()]);
    let t = type_module(&m);
    let diags = collect_diagnostics(&m, &t);
    assert!(diags.is_empty(), "expected no warnings, got {:?}", diags);
}

#[test]
fn eq_then_eq_dup_clause_flags_second_arm_unreachable() {
    // entry(x):
    //   z = 0
    //   c1 = (x == z)
    //   if c1 then halt_b else next_check
    // next_check:
    //   z2 = 0
    //   c2 = (x == z2)        -- x's env in next_check = any \ int_lit(0)
    //   if c2 then dead_b else fallback
    // dead_b: this is the unreachable second "fn f(0)" clause.
    //         env[x] narrows to (any \ 0) ∩ 0 = empty.
    let mut b = FnBuilder::new(FnId(0), "f");
    let x = b.fresh_var();
    let entry = b.block(vec![x]);
    let z = b.let_(entry, Prim::Const(Const::Int(0)));
    let c1 = b.let_(entry, Prim::BinOp(BinOp::Eq, x, z));
    let halt_b = b.block(vec![]);
    let next_check = b.block(vec![]);
    b.set_terminator(entry, Term::if_user(c1, halt_b, next_check));
    b.set_terminator(halt_b, Term::Halt(x));
    let z2 = b.let_(next_check, Prim::Const(Const::Int(0)));
    let c2 = b.let_(next_check, Prim::BinOp(BinOp::Eq, x, z2));
    let dead_b = b.block(vec![]);
    let fallback = b.block(vec![]);
    b.set_terminator(next_check, Term::if_user(c2, dead_b, fallback));
    b.set_terminator(dead_b, Term::Halt(x));
    b.set_terminator(fallback, Term::Halt(x));

    let m = build_module(vec![b.build()]);
    let t = type_module(&m);
    let diags = collect_diagnostics(&m, &t);
    // The dead-block id is mentioned in the diagnostic's notes (post-
    // .20.5 the message is the headline; details live in notes).
    let needle = format!("bb{}", dead_b.0);
    assert!(
        diags
            .iter()
            .any(|d| d.notes.iter().any(|n| n.contains(&needle))),
        "expected dead_b (bb{}) flagged, got {:?}",
        dead_b.0,
        diags
    );
}

// ---- .24.5 vec kind refinement ----

#[test]
fn rewrite_vec_kinds_keeps_int_vec_when_all_elems_int() {
    let mut b = FnBuilder::new(FnId(0), "f");
    let entry = b.block(vec![]);
    let one = b.let_(entry, Prim::Const(Const::Int(1)));
    let two = b.let_(entry, Prim::Const(Const::Int(2)));
    let v = b.let_(entry, Prim::MakeVec(VecKindIr::I64, vec![one, two]));
    b.set_terminator(entry, Term::Return(v));
    let mut m = build_module(vec![b.build()]);
    let t = type_module(&m);
    rewrite_vec_kinds(&mut m, &t).expect("no error");
    let stmt = &m.fns[0].blocks[0].stmts[2];
    match stmt {
        crate::fz_ir::Stmt::Let(_, Prim::MakeVec(VecKindIr::I64, _)) => {}
        other => panic!("expected MakeVec(I64), got {:?}", other),
    }
}

#[test]
fn rewrite_vec_kinds_promotes_to_f64_when_elem_typed_float() {
    // Build: f0 = const(1.0); v = MakeVec(I64, [f0])  -- intentionally I64 to test the rewrite.
    let mut b = FnBuilder::new(FnId(0), "f");
    let entry = b.block(vec![]);
    let f0 = b.let_(entry, Prim::Const(Const::Float(1.0)));
    let v = b.let_(entry, Prim::MakeVec(VecKindIr::I64, vec![f0]));
    b.set_terminator(entry, Term::Return(v));
    let mut m = build_module(vec![b.build()]);
    let t = type_module(&m);
    rewrite_vec_kinds(&mut m, &t).expect("no error");
    let stmt = &m.fns[0].blocks[0].stmts[1];
    match stmt {
        crate::fz_ir::Stmt::Let(_, Prim::MakeVec(VecKindIr::F64, _)) => {}
        other => panic!("expected MakeVec(F64) after rewrite, got {:?}", other),
    }
}

#[test]
fn rewrite_vec_kinds_errors_on_mixed_int_and_float_elems() {
    let mut b = FnBuilder::new(FnId(0), "f");
    let entry = b.block(vec![]);
    let i0 = b.let_(entry, Prim::Const(Const::Int(1)));
    let f0 = b.let_(entry, Prim::Const(Const::Float(2.0)));
    let v = b.let_(entry, Prim::MakeVec(VecKindIr::I64, vec![i0, f0]));
    b.set_terminator(entry, Term::Return(v));
    let mut m = build_module(vec![b.build()]);
    let t = type_module(&m);
    let err = rewrite_vec_kinds(&mut m, &t).expect_err("expected mixed error");
    assert!(
        err.contains("11.24.5"),
        "expected ticket reference, got: {}",
        err
    );
}

#[test]
fn map_get_with_singleton_key_returns_field_type() {
    let mut b = FnBuilder::new(FnId(0), "f");
    let entry = b.block(vec![]);
    let k = b.let_(entry, Prim::Const(Const::Atom(1)));
    let v = b.let_(entry, Prim::Const(Const::Int(42)));
    let mp = b.let_(entry, Prim::MakeMap(vec![(k, v)]));
    let got = b.let_(entry, Prim::MapGet(mp, k));
    b.set_terminator(entry, Term::Return(got));
    let m = build_module(vec![b.build()]);
    let mt = type_module(&m);
    let got_t = fn_view(&m, &mt, 0).vars.get(&got).cloned().unwrap();
    // The map_field_lookup contributes int_lit(42); plus the implicit "may be absent"
    // it can also be any|nil for open-shape semantics. We assert the int_lit(42)
    // is a subtype of the result.
    assert!(
        Descr::int_lit(42).is_subtype(&got_t),
        "map[k] should include the bound value: {}",
        got_t
    );
}

// ----- .20.8: type-rendered diagnostic prose -----

/// The unreachable-arm diagnostic carries two notes: the type the
/// variable had at the branch, and the type the narrowing demanded.
/// Both are rendered through `Descr::display_for_diag`, so a user
/// reading the diagnostic sees set-theoretic vocabulary the typer
/// reasons in — not block ids and Var indices.
#[test]
fn unreachable_arm_diagnostic_includes_type_vocabulary() {
    // Same shape as eq_then_eq_dup_clause_flags_second_arm_unreachable:
    // a `fn f(0); fn f(0)` would dispatch the second clause unreachable.
    let mut b = FnBuilder::new(FnId(0), "f");
    let x = b.fresh_var();
    let entry = b.block(vec![x]);
    let z = b.let_(entry, Prim::Const(Const::Int(0)));
    let c1 = b.let_(entry, Prim::BinOp(BinOp::Eq, x, z));
    let halt_b = b.block(vec![]);
    let next_check = b.block(vec![]);
    b.set_terminator(entry, Term::if_user(c1, halt_b, next_check));
    b.set_terminator(halt_b, Term::Halt(x));
    let z2 = b.let_(next_check, Prim::Const(Const::Int(0)));
    let c2 = b.let_(next_check, Prim::BinOp(BinOp::Eq, x, z2));
    let dead_b = b.block(vec![]);
    let fallback = b.block(vec![]);
    b.set_terminator(next_check, Term::if_user(c2, dead_b, fallback));
    b.set_terminator(dead_b, Term::Halt(x));
    b.set_terminator(fallback, Term::Halt(x));

    let m = build_module(vec![b.build()]);
    let t = type_module(&m);
    let diags = collect_diagnostics(&m, &t);
    let d = diags.iter().next().expect("at least one diagnostic");
    // First note: "type `…`" — rendered set-theoretic vocab.
    let type_note = d
        .notes
        .iter()
        .find(|n| n.contains("has type"))
        .expect("expected a 'has type' note");
    assert!(
        type_note.contains('`'),
        "type note should backtick-quote the rendered type, got {:?}",
        type_note
    );
    // Second note: the narrowing that's uninhabited.
    let narrow_note = d
        .notes
        .iter()
        .find(|n| n.contains("uninhabited"))
        .expect("expected an 'uninhabited' note");
    assert!(
        narrow_note.contains("would need"),
        "narrow note should mention the would-need type, got {:?}",
        narrow_note
    );
}

// ---- fz-ul4.27.10: call-site arg narrowing into entry params ----

#[test]
fn entry_param_narrows_to_caller_arg_type() {
    // callee: fn id(x), do: return x
    let mut cb = FnBuilder::new(FnId(0), "id");
    let x = cb.fresh_var();
    let centry = cb.block(vec![x]);
    cb.set_terminator(centry, Term::Return(x));

    // caller: fn main, do: TailCall id(42)
    let mut mb = FnBuilder::new(FnId(1), "main");
    let mentry = mb.block(vec![]);
    let v = mb.let_(mentry, Prim::Const(Const::Int(42)));
    mb.set_terminator(
        mentry,
        Term::TailCall {
            ident: crate::fz_ir::CallsiteIdent::from_source(crate::diag::Span::DUMMY),
            callee: FnId(0),
            args: vec![v],
            is_back_edge: false,
        },
    );

    let m = build_module(vec![cb.build(), mb.build()]);
    let mt = type_module(&m);
    // `id`'s entry param x should narrow to int_lit(42).
    let xt = fn_view(&m, &mt, 0).vars.get(&x).cloned().unwrap();
    assert!(
        xt.is_equiv(&Descr::int_lit(42)),
        "x should narrow to int_lit(42), got {}",
        xt
    );
}

#[test]
fn entry_param_unions_across_multiple_callers() {
    // callee: fn id(x), do: return x
    let mut cb = FnBuilder::new(FnId(0), "id");
    let x = cb.fresh_var();
    let centry = cb.block(vec![x]);
    cb.set_terminator(centry, Term::Return(x));

    // caller1: TailCall id(1)
    let mut a = FnBuilder::new(FnId(1), "a");
    let aentry = a.block(vec![]);
    let one = a.let_(aentry, Prim::Const(Const::Int(1)));
    a.set_terminator(
        aentry,
        Term::TailCall {
            ident: crate::fz_ir::CallsiteIdent::from_source(crate::diag::Span::DUMMY),
            callee: FnId(0),
            args: vec![one],
            is_back_edge: false,
        },
    );

    // caller2: TailCall id(:atom7)
    let mut bb = FnBuilder::new(FnId(2), "b");
    let bentry = bb.block(vec![]);
    let ok = bb.let_(bentry, Prim::Const(Const::Atom(7)));
    bb.set_terminator(
        bentry,
        Term::TailCall {
            ident: crate::fz_ir::CallsiteIdent::from_source(crate::diag::Span::DUMMY),
            callee: FnId(0),
            args: vec![ok],
            is_back_edge: false,
        },
    );

    let m = build_module(vec![cb.build(), a.build(), bb.build()]);
    let mt = type_module(&m);
    let xt = fn_view(&m, &mt, 0).vars.get(&x).cloned().unwrap();
    // x should accept both int_lit(1) and the atom — the union.
    assert!(
        Descr::int_lit(1).is_subtype(&xt),
        "x should accept int_lit(1), got {}",
        xt
    );
    // Cross-axis: the atom side should be present too. Probe via
    // intersection — the int axis alone should NOT cover all of xt.
    assert!(
        !xt.is_subtype(&Descr::int()),
        "x should also include atom side, got {}",
        xt
    );
}

#[test]
fn closure_target_with_no_direct_callers_keeps_any_entry_params() {
    // fn worker(n), do: return n — packed into a closure by main but
    // never reached via a direct Term::Call/TailCall. With no visible
    // direct caller, the only registered spec is the any-key (which
    // is what closure-invoke dispatches into), and its entry param
    // stays at the initial all-any.
    //
    // fz-ul4.29.3 removed the typer's old `closure_reachable` skip;
    // for closure targets that DO have direct callers, a narrow spec
    // is registered alongside the any-key (exercised below).
    let mut wb = FnBuilder::new(FnId(0), "worker");
    let n = wb.fresh_var();
    let wentry = wb.block(vec![n]);
    wb.set_terminator(wentry, Term::Return(n));

    let mut mb = FnBuilder::new(FnId(1), "main");
    let mentry = mb.block(vec![]);
    let cl = mb.let_(
        mentry,
        Prim::MakeClosure(
            crate::fz_ir::CallsiteIdent::from_source(crate::diag::Span::DUMMY),
            FnId(0),
            vec![],
        ),
    );
    mb.set_terminator(mentry, Term::Halt(cl));

    let m = build_module(vec![wb.build(), mb.build()]);
    let mt = type_module(&m);
    let nt = fn_view(&m, &mt, 0).vars.get(&n).cloned().unwrap();
    assert!(
        nt.is_equiv(&Descr::any()),
        "worker's n must stay at any (no direct callers), got {}",
        nt
    );
}

#[test]
fn closure_target_with_direct_caller_narrows_spec_and_keeps_any_key_body() {
    // fz-ul4.29.3: a fn that's both a MakeClosure target and called
    // directly with a typed arg gets a narrow spec keyed by the
    // direct caller's arg Descrs.
    //
    // fz-try B1+B2: under the new design, the closure-target lambda
    // also has an any-key body — it IS the body, since the
    // closure-target ABI seam speaks uniform Tagged (fz-try.15) and
    // doesn't synchronize via spec keys. The .29.10.3 "drop unused
    // any-key" optimization is structurally subsumed: the any-key
    // body is the canonical compiled body for the closure target.
    let mut wb = FnBuilder::new(FnId(0), "worker");
    let n = wb.fresh_var();
    let wentry = wb.block(vec![n]);
    wb.set_terminator(wentry, Term::Return(n));

    let mut mb = FnBuilder::new(FnId(1), "main");
    let mentry = mb.block(vec![]);
    let _cl = mb.let_(
        mentry,
        Prim::MakeClosure(
            crate::fz_ir::CallsiteIdent::from_source(crate::diag::Span::DUMMY),
            FnId(0),
            vec![],
        ),
    );
    let lit = mb.let_(mentry, Prim::Const(Const::Int(42)));
    mb.set_terminator(
        mentry,
        Term::TailCall {
            ident: crate::fz_ir::CallsiteIdent::from_source(crate::diag::Span::DUMMY),
            callee: FnId(0),
            args: vec![lit],
            is_back_edge: false,
        },
    );

    let m = build_module(vec![wb.build(), mb.build()]);
    let mt = type_module(&m);
    // worker's narrow spec exists with n=int.
    let narrow_spec = mt
        .spec(FnId(0), &[Descr::int_lit(42)])
        .or_else(|| mt.spec(FnId(0), &[Descr::int()]))
        .expect("worker's narrow spec (from direct call) must be registered");
    let nt_narrow = narrow_spec.vars.get(&n).cloned().unwrap();
    assert!(
        nt_narrow.is_subtype(&Descr::int()),
        "worker's narrow-spec n must narrow to int, got {}",
        nt_narrow
    );
    // any-key body also exists: the MakeClosure(worker, []) registers
    // worker as a closure target, so its any-key body is the canonical
    // compiled body.
    assert!(
        mt.spec(FnId(0), &[Descr::any()]).is_some(),
        "worker's any-key body must be registered (worker is a closure target); \
         specs: {:?}",
        mt.specs
            .keys()
            .filter(|(fid, _)| *fid == FnId(0))
            .collect::<Vec<_>>()
    );
    // handle entry: (worker, []) — zero-capture closure handle.
    assert!(
        mt.closure_handles.contains(&(FnId(0), vec![])),
        "expected (worker, []) handle entry; handles: {:?}",
        mt.closure_handles
    );
}

// ----- fz-ul4.29.1: per-callsite specialization map -----

#[test]
fn entry_points_keep_any_key_callees_with_typed_callsites_drop() {
    // fz-ul4.29.12.6 — any-keys are pruned when every callsite has
    // typed coverage. `main` is entry-point-like (no IR caller) and
    // keeps its any-key. `add1` is only called from main with
    // `[int_lit(41)]`; its any-key body is dead → dropped.
    let mut a = FnBuilder::new(FnId(0), "add1");
    let n = a.fresh_var();
    let aentry = a.block(vec![n]);
    let one = a.let_(aentry, Prim::Const(Const::Int(1)));
    let sum = a.let_(aentry, Prim::BinOp(BinOp::Add, n, one));
    a.set_terminator(aentry, Term::Return(sum));

    let mut b = FnBuilder::new(FnId(1), "main");
    let bentry = b.block(vec![]);
    let lit = b.let_(bentry, Prim::Const(Const::Int(41)));
    b.set_terminator(
        bentry,
        Term::TailCall {
            ident: crate::fz_ir::CallsiteIdent::from_source(crate::diag::Span::DUMMY),
            callee: FnId(0),
            args: vec![lit],
            is_back_edge: false,
        },
    );

    let m = build_module(vec![a.build(), b.build()]);
    let mt = type_module(&m);

    let main_any = mt.spec(FnId(1), &[]);
    assert!(
        main_any.is_some(),
        "main (entry-point) must keep its any-key"
    );

    let add1_any = mt.spec(FnId(0), &[Descr::any()]);
    assert!(
        add1_any.is_none(),
        "add1's any-key is dead (only caller passes int_lit(41)) → dropped"
    );
    let add1_narrow = mt.spec(FnId(0), &[Descr::int_lit(41)]);
    assert!(
        add1_narrow.is_some(),
        "add1 must have its narrow callsite-driven spec"
    );
}

#[test]
fn specs_records_narrow_int_callsite() {
    // main calls add1 with an int literal → expect a specialization
    // keyed on `[int]` (not just `[any]`).
    let mut a = FnBuilder::new(FnId(0), "add1");
    let n = a.fresh_var();
    let aentry = a.block(vec![n]);
    let one = a.let_(aentry, Prim::Const(Const::Int(1)));
    let sum = a.let_(aentry, Prim::BinOp(BinOp::Add, n, one));
    a.set_terminator(aentry, Term::Return(sum));

    let mut b = FnBuilder::new(FnId(1), "main");
    let bentry = b.block(vec![]);
    let lit = b.let_(bentry, Prim::Const(Const::Int(41)));
    b.set_terminator(
        bentry,
        Term::TailCall {
            ident: crate::fz_ir::CallsiteIdent::from_source(crate::diag::Span::DUMMY),
            callee: FnId(0),
            args: vec![lit],
            is_back_edge: false,
        },
    );

    let m = build_module(vec![a.build(), b.build()]);
    let mt = type_module(&m);

    // The callsite passes `int_lit(41)`, which is a subtype of int. The
    // spec key carries exactly that Descr.
    let int41 = Descr::int_lit(41);
    let narrow = mt.spec(FnId(0), std::slice::from_ref(&int41));
    assert!(
        narrow.is_some(),
        "add1 must have a specialization keyed on [int_lit(41)]; \
         specs keys present: {:?}",
        mt.specs.keys().filter(|(fid, _)| *fid == FnId(0)).count()
    );
    // The narrowed specialization's `n` should reflect the callsite Descr.
    let nt = narrow.unwrap().vars.get(&n).cloned().unwrap();
    assert!(
        nt.is_equiv(&int41),
        "add1's narrow spec must type n as int_lit(41), got {}",
        nt
    );
}

#[test]
fn fn_view_returns_narrowed_spec_for_direct_caller() {
    // `fn_view` (the post-.29 stand-in for the retired `mt[i]`
    // access) returns the narrow spec produced by the direct
    // callsite — id's entry param narrows to int.
    let mut a = FnBuilder::new(FnId(0), "id");
    let x = a.fresh_var();
    let aentry = a.block(vec![x]);
    a.set_terminator(aentry, Term::Return(x));

    let mut b = FnBuilder::new(FnId(1), "main");
    let bentry = b.block(vec![]);
    let lit = b.let_(bentry, Prim::Const(Const::Int(7)));
    b.set_terminator(
        bentry,
        Term::TailCall {
            ident: crate::fz_ir::CallsiteIdent::from_source(crate::diag::Span::DUMMY),
            callee: FnId(0),
            args: vec![lit],
            is_back_edge: false,
        },
    );

    let m = build_module(vec![a.build(), b.build()]);
    let mt = type_module(&m);

    assert_eq!(mt.specs.len(), 2);
    let id_x = fn_view(&m, &mt, 0).vars.get(&x).cloned().unwrap();
    assert!(
        id_x.is_subtype(&Descr::int()),
        "id's x must be narrowed to int via callsite, got {}",
        id_x
    );
}

// ---- fz-ul4.29.12.1 helper tests ----

fn pipeline(src: &str) -> (Module, ModuleTypes) {
    let toks = crate::lexer::Lexer::new(src).tokenize().expect("lex");
    let prog = crate::parser::Parser::new(toks)
        .parse_program()
        .expect("parse");
    let prog = crate::resolve::flatten_modules(prog).expect("flatten");
    let ir = crate::ir_lower::lower_program(&prog).expect("lower");
    let mt = type_module(&ir);
    (ir, mt)
}

/// fz-rh5.4 — pin upper bounds on deterministic typer-work counters.
/// Bounds are deliberately generous (~2× current observed); failures
/// force the question "is this regression or improvement?" rather
/// than reflex-bless. Tighten in the same commit that lands an
/// intentional improvement.
fn observe_typer_work(src: &str) -> (usize, usize, usize, usize) {
    crate::ir_typer::reset_typer_counters();
    let (_, mt) = pipeline(src);
    let pops = crate::ir_typer::WORKLIST_POPS.with(|c| c.get());
    let walks = crate::ir_typer::WALK_CALLS.with(|c| c.get());
    let typefns = crate::ir_typer::TYPE_FN_CALLS.with(|c| c.get());
    (pops, walks, typefns, mt.specs.len())
}

#[test]
fn typer_work_bounds_ast_eval() {
    let src = std::fs::read_to_string("fixtures/ast_eval/input.fz").expect("read ast_eval fixture");
    let (pops, walks, typefns, specs) = observe_typer_work(&src);
    eprintln!(
        "ast_eval: pops={} walks={} type_fns={} specs={}",
        pops, walks, typefns, specs
    );
    // Bounds are ~2× current observed (Nov 2026). Tighten on
    // intentional improvements; investigate any regression that
    // crosses them.
    assert!(pops < 500, "ast_eval worklist pops regressed: {}", pops);
    assert!(walks < 500, "ast_eval walks regressed: {}", walks);
    assert!(
        typefns < 150,
        "ast_eval type_fn calls regressed: {}",
        typefns
    );
    assert!(specs < 100, "ast_eval spec count regressed: {}", specs);
}

#[test]
fn typer_work_bounds_fib_tailrec() {
    let src =
        std::fs::read_to_string("fixtures/fib_tailrec/input.fz").expect("read fib_tailrec fixture");
    let (pops, walks, typefns, specs) = observe_typer_work(&src);
    eprintln!(
        "fib_tailrec: pops={} walks={} type_fns={} specs={}",
        pops, walks, typefns, specs
    );
    assert!(pops < 200, "fib_tailrec worklist pops regressed: {}", pops);
    assert!(walks < 200, "fib_tailrec walks regressed: {}", walks);
    assert!(
        typefns < 80,
        "fib_tailrec type_fn calls regressed: {}",
        typefns
    );
    assert!(specs < 60, "fib_tailrec spec count regressed: {}", specs);
}

/// fz-2yw.1 — recursive sum's effective return must be the LFP
/// (`int`, joined from base case 0 plus recursive case h + sum(t))
/// — NOT just the base case (0) which is what cycle-cut would give.
#[test]
fn effective_return_lfp_for_recursive_sum() {
    let (m, mt) = pipeline(
        r#"
fn sum([]), do: 0
fn sum([h | t]), do: h + sum(t)
fn main(), do: print(sum([1, 2, 3, 4, 5]))
"#,
    );
    let returns = mt.effective_returns.clone();
    let sum_fn = m.fns.iter().find(|f| f.name == "sum").unwrap();
    // At least one of sum's specs has a non-trivial return.
    let any_int = returns
        .iter()
        .any(|((fid, _), d)| *fid == sum_fn.id && d.is_subtype(&Descr::int()) && !d.is_empty());
    assert!(
        any_int,
        "expected at least one sum spec with return ⊆ int, got: {:?}",
        returns
            .iter()
            .filter(|((fid, _), _)| *fid == sum_fn.id)
            .collect::<Vec<_>>()
    );
    // CRUCIAL: no spec should claim return = singleton 0 (the
    // base case alone). That would mean cycle-cut leaked through.
    for ((fid, _), d) in &returns {
        if *fid != sum_fn.id {
            continue;
        }
        assert!(
            !d.is_equiv(&Descr::int_lit(0)),
            "sum spec return must NOT be just int_lit(0); LFP should \
             lift recursive contribution. Got: {}",
            d
        );
    }
}

/// Helper output for a Call-site Cont must match a key the typer
/// registered in `module_types.specs` under `cont.fn_id`. This is
/// the load-bearing invariant for fz-ul4.29.12.1's SpecRegistry
/// resolve: if it ever fails, the resolve will panic.
#[test]
fn cont_input_key_matches_a_registered_spec_for_call() {
    let (m, mt) = pipeline(
        r#"
fn id(x), do: x
fn main() do
  y = id(7)
  print(y)
end
"#,
    );
    // Find the main fn, locate the Call site, and check the
    // helper's output appears in `mt.specs` for the cont's fn_id.
    let main = m.fns.iter().find(|f| f.name == "main").unwrap();
    let caller_ft = mt.specs.get(&(main.id, vec![])).unwrap();
    let mut found_any = false;
    for blk in &main.blocks {
        if let Term::Call { continuation, .. } = &blk.terminator {
            let key = cont_input_key(blk, continuation, caller_ft, &m, &mt);
            assert!(
                mt.specs.contains_key(&(continuation.fn_id, key.clone())),
                "helper key {:?} for cont fn_id {:?} not in specs; \
                 registered keys for this cont: {:?}",
                key,
                continuation.fn_id,
                mt.specs
                    .iter()
                    .filter(|((f, _), _)| *f == continuation.fn_id)
                    .map(|((_, k), _)| k.clone())
                    .collect::<Vec<_>>(),
            );
            found_any = true;
        }
    }
    assert!(
        found_any,
        "test premise: main should contain a Call with a Cont"
    );
}

/// Direct-Call slot 0 reflects the callee's narrowed return Descr,
/// not `any` — confirms .29.12.1 actually drives narrow Cont SpecId
/// resolution at call-sites where the typer has specialized the
/// callee.
#[test]
fn cont_slot0_narrows_to_callee_return_for_direct_call() {
    let (m, mt) = pipeline(
        r#"
fn add1(n), do: n + 1
fn main(), do: print(add1(40) + 2)
"#,
    );
    let main = m.fns.iter().find(|f| f.name == "main").unwrap();
    let main_ft = mt.specs.get(&(main.id, vec![])).unwrap();
    let mut narrow_found = false;
    for blk in &main.blocks {
        if let Term::Call { .. } = &blk.terminator {
            let s0 = cont_slot0_descr(blk, main_ft, &m, &mt);
            // add1's typer-specialized return for arg int_lit(40) is
            // a strict subtype of `int` — and crucially narrower than
            // `any`.
            assert!(
                !s0.is_equiv(&Descr::any()),
                "slot 0 must narrow below any when callee is specialized, got {}",
                s0
            );
            assert!(
                s0.is_subtype(&Descr::int()),
                "slot 0 should be int-typed, got {}",
                s0
            );
            narrow_found = true;
        }
    }
    assert!(narrow_found, "test premise: main should have a direct Call");
}

/// fz-ul4.29.10: when a top-level fn is passed as a closure value
/// (`apply2(double, …)`), `ir_lower` synthesizes
/// `MakeClosure(double, [])`. .29.10.1 propagates `fn_constants[f]
/// = double` into apply2's spec; .29.10.2 registers double's narrow
/// spec for the typed arg from apply2's CallClosure; the CallClosure
/// is rewritten into a direct `Call(double, …)`.
///
/// fz-try B1+B2: under the new design, double also has an any-key
/// body — it's a closure target (via `MakeClosure(double, [])`), so
/// its any-key body is the canonical compiled body. The narrow spec
/// for the direct-call path coexists. The handle entry
/// `(double, [])` records the zero-capture closure value.
#[test]
fn higher_order_callee_registers_any_key_body_and_narrow_spec() {
    let (m, mt) = pipeline(
        r#"
fn double(x), do: x * 2
fn apply2(f, x), do: f(x)
fn main() do
  print(apply2(double, 21))
end
"#,
    );
    let double = m.fns.iter().find(|f| f.name == "double").unwrap();
    let any_key: Vec<Descr> = vec![Descr::any(); 1];
    assert!(
        mt.specs.contains_key(&(double.id, any_key.clone())),
        "expected double's any-key body to be registered (double is a closure target); \
         registered specs for double: {:?}",
        mt.specs
            .keys()
            .filter(|(fid, _)| *fid == double.id)
            .collect::<Vec<_>>()
    );
    // Narrow spec from the direct-call path also exists.
    let narrow_count = mt
        .specs
        .keys()
        .filter(|(fid, k)| *fid == double.id && !k.iter().all(|d| d.is_equiv(&Descr::any())))
        .count();
    assert!(
        narrow_count >= 1,
        "expected ≥1 narrow spec for double from the direct-call path; \
         registered specs for double: {:?}",
        mt.specs
            .keys()
            .filter(|(fid, _)| *fid == double.id)
            .collect::<Vec<_>>()
    );
    // Handle entry from MakeClosure(double, []).
    assert!(
        mt.closure_handles.contains(&(double.id, vec![])),
        "expected (double, []) handle entry; handles: {:?}",
        mt.closure_handles
    );
}

/// fz-ul4.29.12.6 — a fn whose every IR callsite has typed coverage
/// should NOT have its any-key spec registered in `module_types.specs`.
/// `add` here is only called directly with `[int_lit(1), int_lit(2)]`;
/// no callsite queries with `[any, any]`, so the any-key body is dead.
#[test]
fn fn_with_only_typed_callsites_drops_any_key() {
    let (m, mt) = pipeline(
        r#"
fn add(a, b), do: a + b
fn main(), do: print(add(1, 2))
"#,
    );
    let add = m.fns.iter().find(|f| f.name == "add").unwrap();
    let any_key: Vec<Descr> = vec![Descr::any(); 2];
    assert!(
        !mt.specs.contains_key(&(add.id, any_key.clone())),
        "expected add's any-key to be dropped (no [any, any] callsite); \
         registered specs for add: {:?}",
        mt.specs
            .keys()
            .filter(|(fid, _)| *fid == add.id)
            .collect::<Vec<_>>()
    );
}

/// fz-ul4.29.12.6 — an entry-point-like fn (no IR caller) must keep
/// its any-key. `main` here has zero callsites in the module; the
/// runtime `Runtime::spawn(main_fn_id)` path queries via FnId.0 →
/// SpecId.0, so dropping main's any-key would break runtime entry.
#[test]
fn entry_point_fn_keeps_any_key() {
    let (m, mt) = pipeline(
        r#"
fn main(), do: print(42)
"#,
    );
    let main = m.fns.iter().find(|f| f.name == "main").unwrap();
    let any_key: Vec<Descr> = vec![];
    assert!(
        mt.specs.contains_key(&(main.id, any_key)),
        "main must keep its any-key (entry-point)"
    );
}

/// fz-ul4.29.12.5 — a `Term::Receive` cont with a typed capture must
/// have a narrow spec registered (slot 0 = `any` per the opaque-
/// sender rule, slot 1+ narrowed from the caller's env). .29.12.1's
/// `emit_receive` resolves through subsumption against this spec to
/// pick a narrow cont SpecId for `fz_alloc_frame`; this test pins
/// the typer precondition.
#[test]
fn receive_cont_with_typed_capture_gets_narrow_spec() {
    let (m, mt) = pipeline(
        r#"
fn waiter(tag) do
  m = receive()
  print(m)
  tag
end
fn main() do
  waiter(7)
end
"#,
    );
    // The receive's cont fn is synthesized by ir_lower's CPS split.
    // Find any cont fn referenced from a Term::Receive in waiter.
    let waiter = m.fns.iter().find(|f| f.name == "waiter").unwrap();
    let mut cont_fn_ids: Vec<FnId> = Vec::new();
    for b in &waiter.blocks {
        if let Term::Receive { continuation, .. } = &b.terminator {
            cont_fn_ids.push(continuation.fn_id);
        }
    }
    assert!(
        !cont_fn_ids.is_empty(),
        "test premise: waiter has a Receive"
    );
    // At least one of those cont fns has a narrow spec where slot 1
    // (= the captured `tag`) is `int_lit(7)` (typed via the call
    // `waiter(7)`).
    let mut any_narrow = false;
    for cont_id in cont_fn_ids {
        for (fid, key) in mt.specs.keys() {
            if *fid != cont_id {
                continue;
            }
            if key.is_empty() {
                continue;
            }
            // slot 0 must be `any` (receive opaque).
            if !key[0].is_equiv(&Descr::any()) {
                continue;
            }
            // slot 1+ must include at least one int-typed entry
            // (the propagated `tag` capture).
            if key
                .iter()
                .skip(1)
                .any(|d| d.is_subtype(&Descr::int()) && !d.is_equiv(&Descr::any()))
            {
                any_narrow = true;
            }
        }
    }
    assert!(
        any_narrow,
        "expected ≥1 narrow Receive-cont spec with typed capture; \
         specs for cont fns: {:?}",
        mt.specs
            .iter()
            .filter(|((fid, _), _)| m
                .fns
                .iter()
                .any(|f| f.id == *fid && f.name.contains("waiter")))
            .map(|((fid, k), _)| (*fid, k.clone()))
            .collect::<Vec<_>>()
    );
}

/// fz-ul4.29.12.4 — spawn-with-captures registers a narrow spec for
/// `fz_spawn_thunk` keyed by the spawned closure's Descr. .29.12.2's
/// typed-stub keying then routes spawn dispatch through that narrow
/// stub (verified by the spawn_with_captures fixture across jit /
/// interp / aot). This test asserts the typer prerequisite.
#[test]
fn spawn_with_captures_registers_narrow_fz_spawn_thunk_spec() {
    let (m, mt) = pipeline(
        r#"
fn parent(tag) do
  spawn(fn () -> send(1, tag))
  receive()
end
fn main() do
  print(parent(99))
end
"#,
    );
    let thunk = m.fns.iter().find(|f| f.name == "fz_spawn_thunk").unwrap();
    // fz-try B1+B2 — MakeClosure now registers in ModuleTypes.closure_handles,
    // not as a padded body spec. A handle entry with non-any captures
    // proves the spawn thunk's captures were typed.
    let handles_for_thunk: Vec<&Vec<Descr>> = mt
        .closure_handles
        .iter()
        .filter(|(fid, _)| *fid == thunk.id)
        .map(|(_, caps)| caps)
        .filter(|caps| !caps.is_empty() && !caps.iter().all(|d| d.is_equiv(&Descr::any())))
        .collect();
    assert!(
        !handles_for_thunk.is_empty(),
        "expected ≥1 fz_spawn_thunk handle with typed captures, got 0"
    );
}

/// fz-ul4.29.12.2 — two MakeClosure sites of the same lambda with
/// different capture Descrs must register two distinct narrow specs
/// for the lambda. Codegen keys typed closure stubs off these
/// SpecIds, so this is the load-bearing precondition for typed
/// closure dispatch.
#[test]
fn make_closure_with_distinct_captures_registers_distinct_specs() {
    // Two top-level fns each return a closure that captures a
    // value of a different type. Both target the *same* lambda
    // (well, two different lambdas — adjust below). To force "same
    // lambda, different captures", we use a curried-style helper.
    let (m, mt) = pipeline(
        r#"
fn add_to(x), do: fn (y) -> x + y
fn main() do
  f = add_to(7)
  g = add_to(3.5)
  print(f(1))
  print(g(2.0))
end
"#,
    );
    // Find the lambda FnId — it's the one fn whose name starts
    // with "lambda_".
    let lam = m
        .fns
        .iter()
        .find(|f| f.name.starts_with("lambda_"))
        .expect("expected a lambda fn");
    // fz-try B1+B2 — distinct capture Descrs now produce distinct
    // closure-handle entries (not distinct body specs). The lambda has
    // one compiled body (any-key); the two handles describe the two
    // closure *values* (one captures int, one captures float).
    let handles: Vec<&Vec<Descr>> = mt
        .closure_handles
        .iter()
        .filter(|(fid, _)| *fid == lam.id)
        .map(|(_, caps)| caps)
        .collect();
    assert!(
        handles.len() >= 2,
        "expected ≥2 closure-handle entries for the lambda, got {}: {:?}",
        handles.len(),
        handles
    );
}

/// fz-rh5.1 — at a `CallClosure` whose closure operand resolves
/// via `closure_lit` (not `fn_constants`), the continuation's slot 0
/// must be the lambda's narrow return Descr — NOT `Descr::any()`.
///
/// Pre-fz-5j5.3, `cont_key_for_spec` and `walk_spec_for_discovery`
/// computed slot 0 via different code paths: the walker handled the
/// closure_lit case via `resolve_closure_return`; the cont-key helper
/// fell back to `any`. Under the old whole-graph-rebuild typer the
/// disagreement was invisible (both functions ran under the same
/// wrong logic at every iter); under fz-5j5.3's worklist + reachability
/// sweep split, keys diverged and cont specs went stale.
///
/// This test pins the post-fix behavior: a cont after a CallClosure
/// on a closure_lit-typed value has slot 0 = the lambda's narrow return.
#[test]
fn cont_slot0_after_closure_lit_callclosure_is_narrow_not_any() {
    let (m, mt) = pipeline(
        r#"
fn add_to(x), do: fn (y) -> x + y
fn main() do
  f = add_to(7)
  r = f(1)
  print(r + 100)
end
"#,
    );

    // The cont after `f(1)` receives an `int`. Find the k_ cont fn
    // whose key starts with an int Descr (the lambda's return).
    let int_d = Descr::int();
    let k_specs: Vec<&Vec<Descr>> = mt
        .specs
        .iter()
        .filter(|((fid, _), _)| {
            m.fns
                .iter()
                .find(|f| f.id == *fid)
                .is_some_and(|f| f.name.starts_with("k_"))
        })
        .map(|((_, k), _)| k)
        .collect();

    // At least one k_* cont must have a narrow int-subtype slot 0.
    // If slot 0 were `any`, this assertion would fail — which was
    // the pre-fix behavior under the worklist/sweep split.
    let has_narrow_int_slot0 = k_specs.iter().any(|k| {
        k.first()
            .is_some_and(|d| d.is_subtype(&int_d) && !d.is_equiv(&Descr::any()))
    });
    assert!(
        has_narrow_int_slot0,
        "expected at least one k_* cont spec with narrow int slot 0 \
         from closure_lit-resolved CallClosure; got keys: {:?}",
        k_specs
    );
}

/// Helper's slot 0 for CallClosure / Receive is `Descr::any()` per
/// the typer's opaque-callee rule.
#[test]
fn cont_slot0_is_broad_for_call_closure() {
    // fz-try.7 — cont_slot0_descr uses arrow_join_return without effective_returns
    // context, so the closure's apparent return passes through unrefined. Pre-C3
    // this was `any` (untyped stub); post-C3 it's a parametric type variable
    // (Var(β) where β is fn_id-keyed). Either way, the helper does NOT narrow —
    // refinement requires effective_returns at the walk site, not this helper.
    // The invariant is "no narrowing here," and the test enforces it by
    // requiring the result to NOT be a concrete narrow type (int specifically).
    let (m, mt) = pipeline(
        r#"
fn apply(f, x) do
  r = f(x)
  r + 1
end
fn main() do
  inc = fn (n) -> n + 1
  z = apply(inc, 3)
  print(z)
end
"#,
    );
    let apply_fn = m.fns.iter().find(|f| f.name == "apply").unwrap();
    let caller_ft = mt
        .specs
        .iter()
        .find(|((id, _), _)| *id == apply_fn.id)
        .map(|((_, _), ft)| ft)
        .expect("apply should have at least one spec");
    let mut saw_cc = false;
    for blk in &apply_fn.blocks {
        if matches!(&blk.terminator, Term::CallClosure { .. }) {
            let s0 = cont_slot0_descr(blk, caller_ft, &m, &mt);
            // The helper must not narrow to `int` here — that's refinement
            // work which requires effective_returns. The post-C3 result is
            // Var(β); pre-C3 was `any`. Both are broad/unresolved.
            assert!(
                !s0.is_equiv(&Descr::int()),
                "CallClosure slot 0 must not be narrowed; got {}",
                s0
            );
            assert!(
                s0.is_equiv(&Descr::any()) || s0.has_vars(),
                "CallClosure slot 0 must be broad (any) or parametric (var); got {}",
                s0
            );
            saw_cc = true;
        }
    }
    assert!(saw_cc, "test premise: apply should have a CallClosure");
}

// ---- fz-ul4.29.10.1 — fn_constants side-channel ----

/// A zero-capture `MakeClosure(F, [])` (synthesized by ir_lower when
/// a bare top-level fn name is used as a value) populates
/// `fn_constants[v] = F` on the Let-bound var.
#[test]
fn fn_constant_from_makeclosure_zero_captures() {
    let (m, mt) = pipeline(
        r#"
fn double(x), do: x * 2
fn apply2(f, x), do: f(x)
fn main() do
  print(apply2(double, 21))
end
"#,
    );
    let main = m.fns.iter().find(|f| f.name == "main").unwrap();
    let double = m.fns.iter().find(|f| f.name == "double").unwrap();
    // Find the Var bound to MakeClosure(double, []) in main.
    let mut closure_var: Option<Var> = None;
    for b in &main.blocks {
        for stmt in &b.stmts {
            let Stmt::Let(v, prim) = stmt;
            if let Prim::MakeClosure(_, fid, captured) = prim
                && *fid == double.id
                && captured.is_empty()
            {
                closure_var = Some(*v);
            }
        }
    }
    let v = closure_var.expect("test premise: main has MakeClosure(double, [])");
    let main_ft = mt
        .specs
        .iter()
        .find(|((id, _), _)| *id == main.id)
        .map(|(_, ft)| ft)
        .expect("main spec exists");
    assert_eq!(
        main_ft.fn_constants.get(&v).copied(),
        Some(double.id),
        "zero-capture MakeClosure should populate fn_constants"
    );
}

/// A `MakeClosure` with captures is a real closure value, not a
/// fn-as-value. No `fn_constants` entry.
#[test]
fn fn_constant_not_set_for_captures() {
    let (m, mt) = pipeline(
        r#"
fn main() do
  k = 7
  f = fn (n) -> n + k
  print(f(3))
end
"#,
    );
    let main = m.fns.iter().find(|f| f.name == "main").unwrap();
    let main_ft = mt
        .specs
        .iter()
        .find(|((id, _), _)| *id == main.id)
        .map(|(_, ft)| ft)
        .expect("main spec exists");
    // Find the Var bound to the MakeClosure (the synthesized lambda
    // has captures of [k]).
    let mut closure_var: Option<Var> = None;
    for b in &main.blocks {
        for stmt in &b.stmts {
            let Stmt::Let(v, prim) = stmt;
            if let Prim::MakeClosure(_, _, captured) = prim
                && !captured.is_empty()
            {
                closure_var = Some(*v);
            }
        }
    }
    let v = closure_var.expect("test premise: a captured-MakeClosure in main");
    assert!(
        !main_ft.fn_constants.contains_key(&v),
        "MakeClosure with captures must NOT set fn_constants"
    );
}

/// `apply2(double, 21)` — in apply2's specialized FnTypes, the
/// `f` entry param has `fn_constants[f_param] = double.id`,
/// propagated from main's callsite.
#[test]
fn fn_constant_propagates_via_direct_call() {
    let (m, mt) = pipeline(
        r#"
fn double(x), do: x * 2
fn apply2(f, x), do: f(x)
fn main() do
  print(apply2(double, 21))
end
"#,
    );
    let apply2 = m.fns.iter().find(|f| f.name == "apply2").unwrap();
    let double = m.fns.iter().find(|f| f.name == "double").unwrap();
    let apply2_entry = apply2.block(apply2.entry);
    let f_param = apply2_entry.params[0]; // first param is `f`
    // Look at every spec of apply2 — at least one must carry the
    // propagated fn_constant.
    let mut saw_propagation = false;
    for ((fid, _), ft) in &mt.specs {
        if *fid != apply2.id {
            continue;
        }
        if ft.fn_constants.get(&f_param).copied() == Some(double.id) {
            saw_propagation = true;
        }
    }
    assert!(
        saw_propagation,
        "expected apply2's spec to carry fn_constants[f] = double; \
         specs for apply2: {:?}",
        mt.specs
            .iter()
            .filter(|((fid, _), _)| *fid == apply2.id)
            .map(|((_, k), ft)| (k.clone(), ft.fn_constants.clone()))
            .collect::<Vec<_>>()
    );
}

// ---- fz-ul4.29.10.2 — narrow F-spec from known-target CallClosure ----

// ---- fz-ul4.29.10.3 — IR rewrite of known-target closures ----

/// `rewrite_known_target_closures` replaces `Term::CallClosure(v, …)`
/// with `Term::Call(F, …)` when every spec of the enclosing FnIr
/// agrees that `fn_constants[v] = F`.
#[test]
fn closure_call_rewritten_to_direct_call() {
    let (mut m, mt) = pipeline(
        r#"
fn double(x), do: x * 2
fn apply_plus1(f, x) do
  r = f(x)
  r + 1
end
fn main() do
  print(apply_plus1(double, 21))
end
"#,
    );
    rewrite_known_target_closures(&mut m, &mt);
    let apply2 = m.fns.iter().find(|f| f.name == "apply_plus1").unwrap();
    let double_id = m.fns.iter().find(|f| f.name == "double").unwrap().id;
    let mut saw_direct = false;
    for b in &apply2.blocks {
        match &b.terminator {
            Term::Call { callee, .. } if *callee == double_id => {
                saw_direct = true;
            }
            Term::CallClosure { .. } | Term::TailCallClosure { .. } => {
                panic!("apply2 body still contains a closure-call after rewrite");
            }
            _ => {}
        }
    }
    assert!(
        saw_direct,
        "expected at least one direct Call(double, …) in apply2's body"
    );
}

/// Same rewrite for `Term::TailCallClosure → Term::TailCall`.
#[test]
fn tailcall_closure_variant_rewritten() {
    let (mut m, mt) = pipeline(
        r#"
fn double(x), do: x * 2
fn apply2(f, x), do: f(x)
fn main() do
  apply2(double, 21)
end
"#,
    );
    rewrite_known_target_closures(&mut m, &mt);
    let apply2 = m.fns.iter().find(|f| f.name == "apply2").unwrap();
    let double_id = m.fns.iter().find(|f| f.name == "double").unwrap().id;
    let mut saw_direct = false;
    for b in &apply2.blocks {
        match &b.terminator {
            Term::TailCall { callee, .. } if *callee == double_id => {
                saw_direct = true;
            }
            Term::Call { callee, .. } if *callee == double_id => {
                saw_direct = true;
            }
            Term::CallClosure { .. } | Term::TailCallClosure { .. } => {
                panic!("apply2 body still contains a closure-call after rewrite");
            }
            _ => {}
        }
    }
    assert!(
        saw_direct,
        "expected apply2 body to dispatch directly to double after rewrite"
    );
}

/// `apply2(double, 21)` — apply2's body has `CallClosure(f, [x])`.
/// With `fn_constants[f] = double` propagated from main, the typer's
/// queried-set walk should register `(double, [int_lit(21)])` as a
/// narrow spec for double — alongside its any-key (which .29.10.3
/// will drop). This guarantees a narrow spec exists for the IR
/// rewrite to dispatch into.
#[test]
fn callclosure_with_fn_constant_registers_narrow_spec() {
    let (m, mt) = pipeline(
        r#"
fn double(x), do: x * 2
fn apply2(f, x), do: f(x)
fn main() do
  print(apply2(double, 21))
end
"#,
    );
    let double = m.fns.iter().find(|f| f.name == "double").unwrap();
    let mut saw_narrow = false;
    for (fid, key) in mt.specs.keys() {
        if *fid != double.id {
            continue;
        }
        if key.len() != 1 {
            continue;
        }
        if !key[0].is_equiv(&Descr::any()) && key[0].is_subtype(&Descr::int()) {
            saw_narrow = true;
        }
    }
    assert!(
        saw_narrow,
        "expected a narrow int-typed spec for double from \
         apply2's CallClosure with fn_constants[f] = double; \
         registered specs for double: {:?}",
        mt.specs
            .iter()
            .filter(|((fid, _), _)| *fid == double.id)
            .map(|((_, k), _)| k.clone())
            .collect::<Vec<_>>()
    );
}

// ---- fz-ul4.27.22.9 resolve_closure_return tests ----

fn fid(n: u32) -> FnId {
    FnId(n)
}

#[test]
fn resolve_closure_return_singleton_lookup_hits() {
    // closure_lit(F=7, []) with arg [int_lit(21)]; effective_returns has
    // (7, [int_lit(21)]) -> int. Helper returns Some(int).
    let descr = Descr::closure_lit(fid(7), vec![], 1);
    let mut er: HashMap<(FnId, Vec<Descr>), Descr> = HashMap::new();
    er.insert((fid(7), vec![Descr::int_lit(21)]), Descr::int());
    let r = resolve_closure_return(&descr, &er, &[Descr::int_lit(21)]);
    assert_eq!(r, Some(Descr::int()));
}

#[test]
fn resolve_closure_return_singleton_miss_returns_none() {
    // Singleton with no matching effective_returns entry → None (defer).
    let descr = Descr::closure_lit(fid(7), vec![], 1);
    let er: HashMap<(FnId, Vec<Descr>), Descr> = HashMap::new();
    let r = resolve_closure_return(&descr, &er, &[Descr::int_lit(21)]);
    assert_eq!(r, None);
}

#[test]
fn resolve_closure_return_singleton_with_captures() {
    // closure_lit(F=8, [int_lit(10), int_lit(20)]) — captures + arg form
    // the full body key.
    let descr = Descr::closure_lit(fid(8), vec![Descr::int_lit(10), Descr::int_lit(20)], 1);
    let mut er: HashMap<(FnId, Vec<Descr>), Descr> = HashMap::new();
    er.insert(
        (
            fid(8),
            vec![Descr::int_lit(10), Descr::int_lit(20), Descr::int_lit(12)],
        ),
        Descr::int_lit(42),
    );
    let r = resolve_closure_return(&descr, &er, &[Descr::int_lit(12)]);
    assert_eq!(r, Some(Descr::int_lit(42)));
}

#[test]
fn resolve_closure_return_plain_arrow_uses_sig_ret() {
    // Lit-free arrow: ret comes straight from sig.ret (matches
    // arrow_join_return).
    let descr = Descr::arrow([Descr::any()], Descr::int());
    let er: HashMap<(FnId, Vec<Descr>), Descr> = HashMap::new();
    let r = resolve_closure_return(&descr, &er, &[Descr::int_lit(21)]);
    assert_eq!(r, Some(Descr::int()));
}

#[test]
fn resolve_closure_return_union_of_singletons_joins() {
    // Two clauses: lit(7,[]) returning int, lit(8,[]) returning atom.
    // JOIN = int | atom.
    let a = Descr::closure_lit(fid(7), vec![], 1);
    let b = Descr::closure_lit(fid(8), vec![], 1);
    let descr = a.union(&b);
    let n_clauses = descr
        .components()
        .find_map(|c| match c {
            crate::types::Component::Funcs(v) => Some(v.arrows().count()),
            _ => None,
        })
        .unwrap_or(0);
    assert_eq!(n_clauses, 2, "expect two clauses: {}", descr);
    let mut er: HashMap<(FnId, Vec<Descr>), Descr> = HashMap::new();
    er.insert((fid(7), vec![Descr::int_lit(21)]), Descr::int());
    er.insert((fid(8), vec![Descr::int_lit(21)]), Descr::atom_lit("ok"));
    let r = resolve_closure_return(&descr, &er, &[Descr::int_lit(21)]);
    let expected = Descr::int().union(&Descr::atom_lit("ok"));
    assert_eq!(r, Some(expected));
}

#[test]
fn resolve_closure_return_union_one_miss_defers() {
    // Two clauses; one has a registered spec, the other doesn't. The
    // helper conservatively defers (returns None) so the typer's
    // fixpoint can re-try after the missing spec is registered.
    let a = Descr::closure_lit(fid(7), vec![], 1);
    let b = Descr::closure_lit(fid(8), vec![], 1);
    let descr = a.union(&b);
    let mut er: HashMap<(FnId, Vec<Descr>), Descr> = HashMap::new();
    er.insert((fid(7), vec![Descr::int_lit(21)]), Descr::int());
    // No entry for (8, _) → defer.
    let r = resolve_closure_return(&descr, &er, &[Descr::int_lit(21)]);
    assert_eq!(r, None);
}

#[test]
fn resolve_closure_return_empty_funcs_is_any() {
    // Descr with no funcs at all: arrow_join_return-style any default.
    let descr = Descr::none();
    let er: HashMap<(FnId, Vec<Descr>), Descr> = HashMap::new();
    let r = resolve_closure_return(&descr, &er, &[]);
    assert_eq!(r, Some(Descr::any()));
}

#[test]
fn resolve_closure_return_saturated_arrow_is_any() {
    // Descr::any() has funcs = [Conj::top()] — pos empty, no narrowing.
    let descr = Descr::any();
    let er: HashMap<(FnId, Vec<Descr>), Descr> = HashMap::new();
    let r = resolve_closure_return(&descr, &er, &[Descr::int_lit(21)]);
    assert_eq!(r, Some(Descr::any()));
}

#[test]
fn narrow_for_cond_and_narrows_both_operands_in_then_branch() {
    use crate::fz_ir::{BinOp, Prim, Stmt, Var};
    // Simulate: if x == :ok && y == 1 do … end
    // cx = Eq(x, lit_ok), cy = Eq(y, lit_one), cand = And(cx, cy)
    let x = Var(0);
    let y = Var(1);
    let lit_ok = Var(2);
    let lit_one = Var(3);
    let cx = Var(4);
    let cy = Var(5);
    let cand = Var(6);

    let stmts = vec![
        Stmt::Let(cx, Prim::BinOp(BinOp::Eq, x, lit_ok)),
        Stmt::Let(cy, Prim::BinOp(BinOp::Eq, y, lit_one)),
        Stmt::Let(cand, Prim::BinOp(BinOp::And, cx, cy)),
    ];

    let mut env: HashMap<Var, Descr> = HashMap::new();
    env.insert(x, Descr::any());
    env.insert(y, Descr::any());
    // lit_ok and lit_one already have singleton types in env.
    env.insert(lit_ok, Descr::atom_lit("ok"));
    env.insert(lit_one, Descr::int_lit(1));
    env.insert(cx, Descr::bool_t());
    env.insert(cy, Descr::bool_t());
    env.insert(cand, Descr::bool_t());

    let (then_env, else_env) = narrow_for_cond(cand, &env, &stmts);

    // Then branch: x must be :ok and y must be 1.
    assert_eq!(
        then_env.get(&x).cloned().unwrap_or_else(Descr::any),
        Descr::atom_lit("ok"),
        "then: x should be narrowed to :ok"
    );
    assert_eq!(
        then_env.get(&y).cloned().unwrap_or_else(Descr::any),
        Descr::int_lit(1),
        "then: y should be narrowed to 1"
    );

    // Else branch: at least one failed — union of "x != :ok" and "y != 1".
    // Neither is fully pinned to the singleton.
    let x_else = else_env.get(&x).cloned().unwrap_or_else(Descr::any);
    let y_else = else_env.get(&y).cloned().unwrap_or_else(Descr::any);
    assert!(
        x_else != Descr::atom_lit("ok"),
        "else: x should not be pinned to :ok"
    );
    assert!(
        y_else != Descr::int_lit(1),
        "else: y should not be pinned to 1"
    );
}

/// fz-9pr.1 — EmitterSite ↔ CallsiteId round-trip. Drops then re-attaches
/// a spec-key, recovering the original site exactly. Guards the
/// projection used by reducer / ir_inline / typer to share one
/// callsite vocabulary.
#[test]
fn callsite_id_round_trip() {
    use crate::fz_ir::{BlockId, CallsiteId, EmitSlot};
    use crate::types::Descr;

    let spec_key = (FnId(7), vec![Descr::any(), Descr::int_lit(3)]);
    let _ = BlockId(2); // legacy positional fixture data; ident is now intrinsic.
    let test_ident = crate::fz_ir::CallsiteIdent::synthetic();
    let site = EmitterSite {
        caller: spec_key.clone(),
        ident: test_ident.clone(),
        slot: EmitSlot::ClosureCall,
    };

    let cid: CallsiteId = site.callsite_id();
    assert_eq!(cid.caller, FnId(7));
    assert_eq!(cid.ident, test_ident);
    assert_eq!(cid.slot, EmitSlot::ClosureCall);

    let round = cid.with_spec_key(spec_key);
    assert_eq!(round, site);
}

/// fz-uwq.3/.11 — `type_module` populates `FnTypes.dispatches` with
/// the per-spec dispatch target for each Direct callsite. Build a
/// trivial 2-fn module (main → id), assert the dispatch entry exists
/// at main's spec keyed by `id` plus the literal arg Descr.
#[test]
fn typer_publishes_dispatches_for_direct_call() {
    use crate::fz_ir::{BlockId, CallsiteId, EmitSlot};

    let mut id_b = crate::fz_ir::FnBuilder::new(FnId(0), "id");
    let x = id_b.fresh_var();
    let entry = id_b.block(vec![x]);
    id_b.set_terminator(entry, crate::fz_ir::Term::Return(x));

    let mut main_b = crate::fz_ir::FnBuilder::new(FnId(1), "main");
    let m_entry = main_b.block(vec![]);
    let c42 = main_b.let_(m_entry, Prim::Const(Const::Int(42)));
    let tc_ident = crate::fz_ir::CallsiteIdent::synthetic();
    main_b.set_terminator(
        m_entry,
        crate::fz_ir::Term::TailCall {
            ident: tc_ident.clone(),
            callee: FnId(0),
            args: vec![c42],
            is_back_edge: false,
        },
    );
    let _ = (BlockId(0), m_entry); // legacy positional fixture data.

    let mut mb = crate::fz_ir::ModuleBuilder::new();
    mb.add_fn(id_b.build());
    mb.add_fn(main_b.build());
    let m = mb.build();
    let mt = type_module(&m);

    let cid = CallsiteId {
        caller: FnId(1),
        ident: tc_ident,
        slot: EmitSlot::Direct,
    };
    let main_spec = mt
        .specs
        .get(&(FnId(1), vec![]))
        .expect("main's empty-key spec must exist");
    let (fid, key) = main_spec
        .dispatches
        .get(&cid)
        .expect("dispatches should record main's Direct call to id");
    assert_eq!(*fid, FnId(0));
    assert_eq!(key.len(), 1);
    assert_eq!(key[0], Descr::int_lit(42));
}
