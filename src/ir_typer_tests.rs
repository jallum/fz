use super::*;
use crate::fz_ir::{BinOp, Const, FnBuilder, FnId, ModuleBuilder, Prim, Term, Var};
use crate::types::{ClosureTypes, KeySlot, Types};

fn key_tys(tys: Vec<crate::types::Ty>) -> Vec<KeySlot> {
    crate::types::key_slots_from_tys(tys)
}

fn slot_ty(slot: &KeySlot) -> Option<&crate::types::Ty> {
    slot.as_ref()
}

fn build_module(fns: Vec<crate::fz_ir::FnIr>) -> Module {
    let mut mb = ModuleBuilder::new();
    for f in fns {
        mb.add_fn(f);
    }
    mb.build()
}

/// fz-pky.2 — test helper. Returns "the most narrow registered
/// spec for fn at index i, or an ad-hoc any-key view if unregistered."
fn fn_view(t: &mut crate::types::ConcreteTypes, m: &Module, mt: &ModuleTypes, i: usize) -> FnTypes {
    let fid = m.fns[i].id;
    if let Some(ft) = mt.any_spec_for(fid) {
        return ft.clone();
    }
    // Unreachable fn — type ad-hoc under all-any.
    let n_params = m.fns[i].block(m.fns[i].entry).params.len();
    let any_key: Vec<crate::types::Ty> = (0..n_params).map(|_| t.any()).collect();
    type_fn(t, &m.fns[i], m, Some(&any_key))
}

fn assert_ty_subtype(
    t: &mut crate::types::ConcreteTypes,
    ty: &crate::types::Ty,
    expected: &crate::types::Ty,
) {
    assert!(
        t.is_subtype(ty, expected),
        "expected subtype of {}, got {}",
        t.display(expected),
        t.display(ty)
    );
}

fn assert_ty_not_empty(t: &crate::types::ConcreteTypes, ty: &crate::types::Ty) {
    assert!(!t.is_empty(ty), "unexpected empty type: {}", t.display(ty));
}

// ---- .24.2 tests (preserved, adjusted to FnTypes API) ----

#[test]
fn const_int_typed_as_singleton() {
    let mut b = FnBuilder::new(FnId(0), "main");
    let entry = b.block(vec![]);
    let v = b.let_(entry, Prim::Const(Const::Int(42)));
    b.set_terminator(entry, Term::Halt(v));
    let m = build_module(vec![b.build()]);
    let mut t = crate::types::ConcreteTypes;
    let mt = type_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    let ty = fn_view(&mut t, &m, &mt, 0).vars.get(&v).unwrap().clone();
    assert_eq!(t.as_int_singleton(&ty), Some(42));
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
    let mut t = crate::types::ConcreteTypes;
    let mt = type_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    let sum_t = fn_view(&mut t, &m, &mt, 0).vars.get(&sum).unwrap().clone();
    let int = t.int();
    let float = t.float();
    let expected = t.union(int, float);
    assert!(
        t.is_equivalent(&sum_t, &expected),
        "got {}",
        t.display(&sum_t)
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
    let mut t = crate::types::ConcreteTypes;
    let mt = type_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    let lt = fn_view(&mut t, &m, &mt, 0).vars.get(&l).unwrap().clone();
    let elem = t.list_element_type(&lt);
    let int = t.int();
    assert_ty_subtype(&mut t, &elem, &int);
    assert_ty_not_empty(&t, &elem);
}

#[test]
fn list_cons_onto_empty_list_keeps_head_element_type() {
    let mut b = FnBuilder::new(FnId(0), "f");
    let entry = b.block(vec![]);
    let one = b.let_(entry, Prim::Const(Const::Int(1)));
    let empty = b.let_(entry, Prim::MakeList(vec![], None));
    let cons = b.let_(entry, Prim::ListCons(one, empty));
    b.set_terminator(entry, Term::Return(cons));

    let m = build_module(vec![b.build()]);
    let mut t = crate::types::ConcreteTypes;
    let mt = type_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    let cons_t = fn_view(&mut t, &m, &mt, 0).vars.get(&cons).unwrap().clone();
    let elem = t.list_element_type(&cons_t);
    assert_eq!(
        t.as_int_singleton(&elem),
        Some(1),
        "got {}",
        t.display(&cons_t)
    );
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
    let mut t = crate::types::ConcreteTypes;
    let mt = type_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    let join_t = fn_view(&mut t, &m, &mt, 0)
        .vars
        .get(&joined)
        .unwrap()
        .clone();
    let one = t.int_lit(1);
    let two = t.int_lit(2);
    let expected = t.union(one, two);
    assert!(
        t.is_equivalent(&join_t, &expected),
        "got {}",
        t.display(&join_t)
    );
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
    let mut t = crate::types::ConcreteTypes;
    let mt = type_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    let f0_t = fn_view(&mut t, &m, &mt, 0).vars.get(&f0).unwrap().clone();
    assert_eq!(
        t.as_int_singleton(&f0_t),
        Some(1),
        "got {}",
        t.display(&f0_t)
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
    let mut t = crate::types::ConcreteTypes;
    let mt = type_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    let h_t = fn_view(&mut t, &m, &mt, 0).vars.get(&h).unwrap().clone();
    let int = t.int();
    assert_ty_subtype(&mut t, &h_t, &int);
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
    let mut t = crate::types::ConcreteTypes;
    let mt = type_module(&mut t, &m, &crate::telemetry::NullTelemetry);

    // In then_b's entry env, l is narrowed to the explicit empty-list
    // shape. Pre-s9y.3 this narrowed to `nil()` (the nil atom-like value),
    // reflecting the now-obsolete runtime conflation.
    let ft = fn_view(&mut t, &m, &mt, 0);
    let then_env = ft.block_envs.get(&then_b).unwrap();
    let l_then = then_env.get(&l).unwrap();
    let empty_list = t.empty_list();
    assert!(
        t.is_equivalent(l_then, &empty_list),
        "l in then-branch should be the empty list: {}",
        t.display(l_then)
    );

    // In else_b's entry env, l should be narrowed to the non-empty list shape.
    let else_env = ft.block_envs.get(&else_b).unwrap();
    let l_else = else_env.get(&l).unwrap();
    let any = t.any();
    let nonempty_any = t.non_empty_list(any);
    assert!(
        t.is_equivalent(l_else, &nonempty_any),
        "l in else-branch should be non-empty-list-shaped: {}",
        t.display(l_else)
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
    let mut t = crate::types::ConcreteTypes;
    let mt = type_module(&mut t, &m, &crate::telemetry::NullTelemetry);

    let ft = fn_view(&mut t, &m, &mt, 0);
    let then_env = ft.block_envs.get(&then_b).unwrap();
    let x_then = then_env.get(&x).unwrap();
    let zero = t.int_lit(0);
    assert!(
        t.is_equivalent(x_then, &zero),
        "x in then-branch should be int_lit(0): {}",
        t.display(x_then)
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
    let mut t = crate::types::ConcreteTypes;
    let mt = type_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    let p00_t = fn_view(&mut t, &m, &mt, 0).vars.get(&p00).unwrap().clone();
    assert_eq!(
        t.as_int_singleton(&p00_t),
        Some(7),
        "got {}",
        t.display(&p00_t)
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
    let mut ct = crate::types::ConcreteTypes;
    let t = type_module(&mut ct, &m, &crate::telemetry::NullTelemetry);
    let diags = collect_diagnostics(&mut ct, &m, &t);
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
    let mut ct = crate::types::ConcreteTypes;
    let t = type_module(&mut ct, &m, &crate::telemetry::NullTelemetry);
    let diags = collect_diagnostics(&mut ct, &m, &t);
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
    let mut ct = crate::types::ConcreteTypes;
    let t = type_module(&mut ct, &m, &crate::telemetry::NullTelemetry);
    let diags = collect_diagnostics(&mut ct, &m, &t);
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
    let mut t = crate::types::ConcreteTypes;
    let mt = type_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    let got_t = fn_view(&mut t, &m, &mt, 0).vars.get(&got).unwrap().clone();
    // The map_field_lookup contributes int_lit(42); plus the implicit "may be absent"
    // it can also be any|nil for open-shape semantics. We assert the int_lit(42)
    // is a subtype of the result.
    let int42 = t.int_lit(42);
    assert!(
        t.is_subtype(&int42, &got_t),
        "map[k] should include the bound value: {}",
        t.display(&got_t)
    );
}

// ----- .20.8: type-rendered diagnostic prose -----

/// The unreachable-arm diagnostic carries two notes: the type the
/// variable had at the branch, and the type the narrowing demanded.
/// Both are rendered through the seam's diagnostic display, so a user
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
    let mut ct = crate::types::ConcreteTypes;
    let t = type_module(&mut ct, &m, &crate::telemetry::NullTelemetry);
    let diags = collect_diagnostics(&mut ct, &m, &t);
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
    let mut t = crate::types::ConcreteTypes;
    let mt = type_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    // `id`'s entry param x should narrow to int_lit(42).
    let xt = fn_view(&mut t, &m, &mt, 0).vars.get(&x).unwrap().clone();
    assert_eq!(t.as_int_singleton(&xt), Some(42), "got {}", t.display(&xt));
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
    let mut t = crate::types::ConcreteTypes;
    let mt = type_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    let xt = fn_view(&mut t, &m, &mt, 0).vars.get(&x).unwrap().clone();
    // x should accept both int_lit(1) and the atom — the union.
    let one = t.int_lit(1);
    assert!(
        t.is_subtype(&one, &xt),
        "x should accept int_lit(1), got {}",
        t.display(&xt)
    );
    // Cross-axis: the atom side should be present too. Probe via
    // intersection — the int axis alone should NOT cover all of xt.
    let int = t.int();
    assert!(
        !t.is_subtype(&xt, &int),
        "x should also include atom side, got {}",
        t.display(&xt)
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
    let mut t = crate::types::ConcreteTypes;
    let mt = type_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    let nt = fn_view(&mut t, &m, &mt, 0).vars.get(&n).unwrap().clone();
    let any = t.any();
    assert!(
        t.is_equivalent(&nt, &any),
        "worker's n must stay at any (no direct callers), got {}",
        t.display(&nt)
    );
}

#[test]
fn closure_target_with_direct_caller_narrows_spec_and_keeps_any_key_body() {
    // fz-ul4.29.3: a fn that's both a MakeClosure target and called
    // directly with a typed arg gets a narrow spec keyed by the
    // direct caller's arg types.
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
    let mut t = crate::types::ConcreteTypes;
    let mt = type_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    // worker's narrow spec exists with n=int.
    let narrow_spec = mt
        .spec_ty(FnId(0), &[t.int_lit(42)])
        .or_else(|| mt.spec_ty(FnId(0), &[t.int()]))
        .expect("worker's narrow spec (from direct call) must be registered");
    let nt_narrow = narrow_spec.vars.get(&n).unwrap().clone();
    let int = t.int();
    assert!(
        t.is_subtype(&nt_narrow, &int),
        "worker's narrow-spec n must narrow to int, got {}",
        t.display(&nt_narrow)
    );
    // any-key body also exists: the MakeClosure(worker, []) registers
    // worker as a closure target, so its any-key body is the canonical
    // compiled body.
    assert!(
        mt.spec_ty(FnId(0), &[t.any()]).is_some(),
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
    let mut t = crate::types::ConcreteTypes;
    let mt = type_module(&mut t, &m, &crate::telemetry::NullTelemetry);

    let main_any = mt.spec_ty(FnId(1), &[]);
    assert!(
        main_any.is_some(),
        "main (entry-point) must keep its any-key"
    );

    let add1_any = mt.spec_ty(FnId(0), &[t.any()]);
    assert!(
        add1_any.is_none(),
        "add1's any-key is dead (only caller passes int_lit(41)) → dropped"
    );
    let add1_narrow = mt.spec_ty(FnId(0), &[t.int_lit(41)]);
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
    let mut t = crate::types::ConcreteTypes;
    let mt = type_module(&mut t, &m, &crate::telemetry::NullTelemetry);

    // The callsite passes `int_lit(41)`, which is a subtype of int. The
    // spec key carries exactly that type.
    let int41 = t.int_lit(41);
    let narrow = mt.spec_ty(FnId(0), std::slice::from_ref(&int41));
    assert!(
        narrow.is_some(),
        "add1 must have a specialization keyed on [int_lit(41)]; \
         specs keys present: {:?}",
        mt.specs.keys().filter(|(fid, _)| *fid == FnId(0)).count()
    );
    // The narrowed specialization's `n` should reflect the callsite type.
    let nt = narrow.unwrap().vars.get(&n).unwrap().clone();
    assert!(t.is_equivalent(&nt, &int41), "got {}", t.display(&nt));
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
    let mut t = crate::types::ConcreteTypes;
    let mt = type_module(&mut t, &m, &crate::telemetry::NullTelemetry);

    assert_eq!(mt.specs.len(), 2);
    let id_x = fn_view(&mut t, &m, &mt, 0).vars.get(&x).unwrap().clone();
    let int = t.int();
    assert!(
        t.is_subtype(&id_x, &int),
        "id's x must be narrowed to int via callsite, got {}",
        t.display(&id_x)
    );
}

// ---- fz-ul4.29.12.1 helper tests ----

fn pipeline(
    src: &str,
    tel: &dyn crate::telemetry::Telemetry,
) -> (crate::types::ConcreteTypes, Module, ModuleTypes) {
    let toks = crate::lexer::Lexer::new(src).tokenize().expect("lex");
    let prog = crate::parser::Parser::new(toks)
        .parse_program()
        .expect("parse");
    let mut t = crate::types::ConcreteTypes;
    let prog = crate::resolve::flatten_modules(&mut t, prog).expect("flatten");
    let ir = crate::ir_lower::lower_program(&mut t, &prog).expect("lower");
    let mt = type_module(&mut t, &ir, tel);
    (t, ir, mt)
}

#[test]
fn empty_list_call_only_reaches_empty_clause() {
    let (t, m, mt) = pipeline(
        r#"
fn classify([]), do: :empty
fn classify([_ | _]), do: :cons

fn main() do
  print(classify([]))
end
"#,
        &crate::telemetry::NullTelemetry,
    );
    let classify = m.fn_by_name("classify").expect("classify");
    let found = mt
        .effective_returns
        .iter()
        .find(|((fid, key), _)| {
            *fid == classify.id && crate::types::display_key_slots(&t, key) == "[[]]"
        })
        .map(|(_, ret)| t.display(ret));
    assert_eq!(found.as_deref(), Some(":empty"));
}

#[test]
fn wildcard_param_becomes_semantic_key_hole() {
    let (_t, m, mt) = pipeline(
        r#"
fn ignore(_, x), do: x

fn main() do
  a = ignore(1, 2)
  b = ignore(:ok, 2)
  print(a)
  print(b)
end
"#,
        &crate::telemetry::NullTelemetry,
    );
    let ignore = m.fn_by_name("ignore").expect("ignore fn");
    assert_eq!(ignore.ignored_entry_params, vec![true, false]);

    let keys: Vec<_> = mt
        .specs
        .keys()
        .filter(|(fid, _)| *fid == ignore.id)
        .map(|(_, key)| key.clone())
        .collect();
    assert_eq!(
        keys.len(),
        1,
        "ignored arg variation should not fork specs: {keys:?}"
    );
    assert!(keys[0][0].is_none());
    assert!(keys[0][1].is_some());
}

/// fz-rh5.4 — pin upper bounds on deterministic typer-work counters.
/// Bounds are deliberately generous (~2× current observed); failures
/// force the question "is this regression or improvement?" rather
/// than reflex-bless. Tighten in the same commit that lands an
/// intentional improvement.
fn observe_typer_work(src: &str) -> (usize, usize, usize, usize) {
    use crate::telemetry::{Capture, ConfiguredTelemetry};
    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());
    let _ = pipeline(src, &tel);
    let ev = cap
        .last(&["fz", "typer", "typed"])
        .expect("fz.typer.typed event not emitted");
    let pops = match ev.measurements.get("worklist_pops") {
        Some(crate::telemetry::Value::U64(n)) => *n as usize,
        other => panic!("worklist_pops missing or wrong type: {:?}", other),
    };
    let walks = match ev.measurements.get("walk_calls") {
        Some(crate::telemetry::Value::U64(n)) => *n as usize,
        other => panic!("walk_calls missing or wrong type: {:?}", other),
    };
    let typefns = match ev.measurements.get("type_fn_calls") {
        Some(crate::telemetry::Value::U64(n)) => *n as usize,
        other => panic!("type_fn_calls missing or wrong type: {:?}", other),
    };
    let specs = match ev.measurements.get("spec_count") {
        Some(crate::telemetry::Value::U64(n)) => *n as usize,
        other => panic!("spec_count missing or wrong type: {:?}", other),
    };
    (pops, walks, typefns, specs)
}

#[test]
fn typer_work_bounds_ast_eval() {
    let src = std::fs::read_to_string("fixtures/ast_eval/input.fz").expect("read ast_eval fixture");
    let (pops, walks, typefns, specs) = observe_typer_work(&src);
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
    let (mut t, m, mt) = pipeline(
        r#"
fn sum([]), do: 0
fn sum([h | t]), do: h + sum(t)
fn main(), do: print(sum([1, 2, 3, 4, 5]))
"#,
        &crate::telemetry::NullTelemetry,
    );
    let returns = mt.effective_returns.clone();
    let sum_fn = m.fns.iter().find(|f| f.name == "sum").unwrap();
    // At least one of sum's specs has a non-trivial return.
    let int = t.int();
    let any_int = returns
        .iter()
        .any(|((fid, _), d)| *fid == sum_fn.id && t.is_subtype(d, &int) && !t.is_empty(d));
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
        let zero = t.int_lit(0);
        assert!(
            !t.is_equivalent(d, &zero),
            "sum spec return must NOT be just int_lit(0); LFP should \
             lift recursive contribution. Got: {}",
            t.display(d)
        );
    }
}

/// Helper output for a Call-site Cont must match a key the typer
/// registered in `module_types.specs` under `cont.fn_id`. This is
/// the load-bearing invariant for fz-ul4.29.12.1's SpecRegistry
/// resolve: if it ever fails, the resolve will panic.
#[test]
fn cont_input_key_matches_a_registered_spec_for_call() {
    let (mut t, m, mt) = pipeline(
        r#"
fn id(x), do: x
fn main() do
  y = id(7)
  print(y)
end
"#,
        &crate::telemetry::NullTelemetry,
    );
    // Find the main fn, locate the Call site, and check the
    // helper's output appears in `mt.specs` for the cont's fn_id.
    let main = m.fns.iter().find(|f| f.name == "main").unwrap();
    let caller_ft = mt.specs.get(&(main.id, vec![])).unwrap();
    let mut found_any = false;
    for blk in &main.blocks {
        if let Term::Call { continuation, .. } = &blk.terminator {
            let key = cont_input_key(&mut t, blk, continuation, caller_ft, &m, &mt);
            let key = key_tys(key);
            assert!(
                mt.specs.contains_key(&(continuation.fn_id, key.clone())),
                "helper key {:?} for cont fn_id {:?} not in specs; \
                 registered keys for this cont: {:?}",
                key,
                continuation.fn_id,
                mt.specs
                    .iter()
                    .filter(|((f, _), _)| *f == continuation.fn_id)
                    .map(|((_, k), _)| crate::types::display_key_slots(&t, k))
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

/// Direct-Call slot 0 reflects the callee's narrowed return type,
/// not `any` — confirms .29.12.1 actually drives narrow Cont SpecId
/// resolution at call-sites where the typer has specialized the
/// callee.
#[test]
fn cont_slot0_narrows_to_callee_return_for_direct_call() {
    let (mut t, m, mt) = pipeline(
        r#"
fn add1(n), do: n + 1
fn main(), do: print(add1(40) + 2)
"#,
        &crate::telemetry::NullTelemetry,
    );
    let main = m.fns.iter().find(|f| f.name == "main").unwrap();
    let main_ft = mt.specs.get(&(main.id, vec![])).unwrap();
    let mut narrow_found = false;
    for blk in &main.blocks {
        if let Term::Call { .. } = &blk.terminator {
            let s0 = cont_slot0_descr(&mut t, blk, main_ft, &m, &mt);
            // add1's typer-specialized return for arg int_lit(40) is
            // a strict subtype of `int` — and crucially narrower than
            // `any`.
            let any = t.any();
            assert!(
                !t.is_equivalent(&s0, &any),
                "slot 0 must narrow below any when callee is specialized, got {}",
                t.display(&s0)
            );
            let int = t.int();
            assert!(
                t.is_subtype(&s0, &int),
                "slot 0 should be int-typed, got {}",
                t.display(&s0)
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
    let (mut t, m, mt) = pipeline(
        r#"
fn double(x), do: x * 2
fn apply2(f, x), do: f(x)
fn main() do
  print(apply2(double, 21))
end
"#,
        &crate::telemetry::NullTelemetry,
    );
    let double = m.fns.iter().find(|f| f.name == "double").unwrap();
    let any_key = key_tys(vec![t.any()]);
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
        .filter(|(fid, k)| {
            *fid == double.id && !k.iter().all(|d| slot_ty(d).is_some_and(|ty| t.is_top(ty)))
        })
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
    let (mut t, m, mt) = pipeline(
        r#"
fn add(a, b), do: a + b
fn main(), do: print(add(1, 2))
"#,
        &crate::telemetry::NullTelemetry,
    );
    let add = m.fns.iter().find(|f| f.name == "add").unwrap();
    let any_key = {
        let a = t.any();
        let b = t.any();
        key_tys(vec![a, b])
    };
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
    let (_t, m, mt) = pipeline(
        r#"
fn main(), do: print(42)
"#,
        &crate::telemetry::NullTelemetry,
    );
    let main = m.fns.iter().find(|f| f.name == "main").unwrap();
    let any_key: Vec<KeySlot> = vec![];
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
    let (t, m, mt) = pipeline(
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
        &crate::telemetry::NullTelemetry,
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
            if !slot_ty(&key[0]).is_some_and(|ty| t.is_top(ty)) {
                continue;
            }
            // slot 1+ must include at least one int-typed entry
            // (the propagated `tag` capture).
            if key
                .iter()
                .skip(1)
                .any(|d| slot_ty(d).is_some_and(|ty| t.is_integer(ty) && !t.is_top(ty)))
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
/// `fz_spawn_thunk` keyed by the spawned closure's type. .29.12.2's
/// typed-stub keying then routes spawn dispatch through that narrow
/// stub (verified by the spawn_with_captures fixture across jit /
/// interp / aot). This test asserts the typer prerequisite.
#[test]
fn spawn_with_captures_registers_narrow_fz_spawn_thunk_spec() {
    let (t, m, mt) = pipeline(
        r#"
fn parent(tag) do
  spawn(fn () -> send(1, tag))
  receive()
end
fn main() do
  print(parent(99))
end
"#,
        &crate::telemetry::NullTelemetry,
    );
    let thunk = m.fns.iter().find(|f| f.name == "fz_spawn_thunk").unwrap();
    // fz-try B1+B2 — MakeClosure now registers in ModuleTypes.closure_handles,
    // not as a padded body spec. A handle entry with non-any captures
    // proves the spawn thunk's captures were typed.
    let handles_for_thunk: Vec<&Vec<crate::types::Ty>> = mt
        .closure_handles
        .iter()
        .filter(|(fid, _)| *fid == thunk.id)
        .map(|(_, caps)| caps)
        .filter(|caps| !caps.is_empty() && !caps.iter().all(|d| t.is_top(d)))
        .collect();
    assert!(
        !handles_for_thunk.is_empty(),
        "expected ≥1 fz_spawn_thunk handle with typed captures, got 0"
    );
}

/// fz-ul4.29.12.2 — two MakeClosure sites of the same lambda with
/// different capture types must register two distinct narrow specs
/// for the lambda. Codegen keys typed closure stubs off these
/// SpecIds, so this is the load-bearing precondition for typed
/// closure dispatch.
#[test]
fn make_closure_with_distinct_captures_registers_distinct_specs() {
    // Two top-level fns each return a closure that captures a
    // value of a different type. Both target the *same* lambda
    // (well, two different lambdas — adjust below). To force "same
    // lambda, different captures", we use a curried-style helper.
    let (_t, m, mt) = pipeline(
        r#"
fn add_to(x), do: fn (y) -> x + y
fn main() do
  f = add_to(7)
  g = add_to(3.5)
  print(f(1))
  print(g(2.0))
end
"#,
        &crate::telemetry::NullTelemetry,
    );
    // Find the lambda FnId — it's the one fn whose name starts
    // with "lambda_".
    let lam = m
        .fns
        .iter()
        .find(|f| f.name.starts_with("lambda_"))
        .expect("expected a lambda fn");
    // fz-try B1+B2 — distinct capture types now produce distinct
    // closure-handle entries (not distinct body specs). The lambda has
    // one compiled body (any-key); the two handles describe the two
    // closure *values* (one captures int, one captures float).
    let handles: Vec<&Vec<crate::types::Ty>> = mt
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
/// must be the lambda's narrow return type — NOT `any()`.
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
    let (t, m, mt) = pipeline(
        r#"
fn add_to(x), do: fn (y) -> x + y
fn main() do
  f = add_to(7)
  r = f(1)
  print(r + 100)
end
"#,
        &crate::telemetry::NullTelemetry,
    );

    // The cont after `f(1)` receives an `int`. Find the k_ cont fn
    // whose key starts with an int type (the lambda's return).
    let k_specs: Vec<&Vec<KeySlot>> = mt
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
            .and_then(slot_ty)
            .is_some_and(|d| t.is_integer(d) && !t.is_top(d))
    });
    assert!(
        has_narrow_int_slot0,
        "expected at least one k_* cont spec with narrow int slot 0 \
         from closure_lit-resolved CallClosure; got keys: {:?}",
        k_specs
    );
}

/// Helper's slot 0 for CallClosure / Receive is `any()` per
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
    let (mut t, m, mt) = pipeline(
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
        &crate::telemetry::NullTelemetry,
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
            let s0 = cont_slot0_descr(&mut t, blk, caller_ft, &m, &mt);
            // The helper must not narrow to `int` here — that's refinement
            // work which requires effective_returns. The post-C3 result is
            // Var(β); pre-C3 was `any`. Both are broad/unresolved.
            let int = t.int();
            assert!(
                !t.is_equivalent(&s0, &int),
                "CallClosure slot 0 must not be narrowed; got {}",
                t.display(&s0)
            );
            let any = t.any();
            assert!(
                t.is_equivalent(&s0, &any) || t.has_vars(&s0),
                "CallClosure slot 0 must be broad (any) or parametric (var); got {}",
                t.display(&s0)
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
    let (_t, m, mt) = pipeline(
        r#"
fn double(x), do: x * 2
fn apply2(f, x), do: f(x)
fn main() do
  print(apply2(double, 21))
end
"#,
        &crate::telemetry::NullTelemetry,
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
    let (_t, m, mt) = pipeline(
        r#"
fn main() do
  k = 7
  f = fn (n) -> n + k
  print(f(3))
end
"#,
        &crate::telemetry::NullTelemetry,
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
    let (_t, m, mt) = pipeline(
        r#"
fn double(x), do: x * 2
fn apply2(f, x), do: f(x)
fn main() do
  print(apply2(double, 21))
end
"#,
        &crate::telemetry::NullTelemetry,
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
    let (mut t, mut m, mt) = pipeline(
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
        &crate::telemetry::NullTelemetry,
    );
    rewrite_known_target_closures(&mut t, &mut m, &mt);
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
    let (mut t, mut m, mt) = pipeline(
        r#"
fn double(x), do: x * 2
fn apply2(f, x), do: f(x)
fn main() do
  apply2(double, 21)
end
"#,
        &crate::telemetry::NullTelemetry,
    );
    rewrite_known_target_closures(&mut t, &mut m, &mt);
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
    let (t, m, mt) = pipeline(
        r#"
fn double(x), do: x * 2
fn apply2(f, x), do: f(x)
fn main() do
  print(apply2(double, 21))
end
"#,
        &crate::telemetry::NullTelemetry,
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
        if slot_ty(&key[0]).is_some_and(|ty| !t.is_top(ty) && t.is_integer(ty)) {
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
    let mut t = crate::types::ConcreteTypes;
    let closure = t.closure_lit(fid(7).into(), vec![], 1);
    let mut er: HashMap<(FnId, Vec<KeySlot>), crate::types::Ty> = HashMap::new();
    let key = vec![t.int_lit(21)];
    let int = t.int();
    er.insert((fid(7), key_tys(key)), int.clone());
    let arg_tys = [t.int_lit(21)];
    let r = resolve_closure_return(&mut t, &closure, &er, &arg_tys).unwrap();
    assert!(t.is_equivalent(&r, &int));
}

#[test]
fn resolve_closure_return_singleton_miss_returns_none() {
    // Singleton with no matching effective_returns entry → None (defer).
    let er: HashMap<(FnId, Vec<KeySlot>), crate::types::Ty> = HashMap::new();
    let mut t = crate::types::ConcreteTypes;
    let closure = t.closure_lit(fid(7).into(), vec![], 1);
    let arg_tys = [t.int_lit(21)];
    let r = resolve_closure_return(&mut t, &closure, &er, &arg_tys);
    assert_eq!(r, None);
}

#[test]
fn resolve_closure_return_singleton_with_captures() {
    // closure_lit(F=8, [int_lit(10), int_lit(20)]) — captures + arg form
    // the full body key.
    let mut t = crate::types::ConcreteTypes;
    let cap0 = t.int_lit(10);
    let cap1 = t.int_lit(20);
    let closure = t.closure_lit(fid(8).into(), vec![cap0, cap1], 1);
    let mut er: HashMap<(FnId, Vec<KeySlot>), crate::types::Ty> = HashMap::new();
    let key = vec![t.int_lit(10), t.int_lit(20), t.int_lit(12)];
    let int42 = t.int_lit(42);
    er.insert((fid(8), key_tys(key)), int42);
    let arg_tys = [t.int_lit(12)];
    let r = resolve_closure_return(&mut t, &closure, &er, &arg_tys).unwrap();
    assert_eq!(t.as_int_singleton(&r), Some(42));
}

#[test]
fn resolve_closure_return_plain_arrow_uses_sig_ret() {
    // Lit-free arrow: ret comes straight from sig.ret (matches
    // arrow_join_return).
    let er: HashMap<(FnId, Vec<KeySlot>), crate::types::Ty> = HashMap::new();
    let mut t = crate::types::ConcreteTypes;
    let any = t.any();
    let int = t.int();
    let closure = t.arrow(&[any], int);
    let arg_tys = [t.int_lit(21)];
    let r = resolve_closure_return(&mut t, &closure, &er, &arg_tys).unwrap();
    let int = t.int();
    assert!(t.is_equivalent(&r, &int));
}

#[test]
fn resolve_closure_return_union_of_singletons_joins() {
    // Two clauses: lit(7,[]) returning int, lit(8,[]) returning atom.
    // JOIN = int | atom.
    let mut t = crate::types::ConcreteTypes;
    let a = t.closure_lit(fid(7).into(), vec![], 1);
    let b = t.closure_lit(fid(8).into(), vec![], 1);
    let closure = t.union(a, b);
    let n_clauses = t.callable_clauses(&closure).map(|c| c.len()).unwrap_or(0);
    assert_eq!(n_clauses, 2, "expect two clauses: {}", t.display(&closure));
    let mut er: HashMap<(FnId, Vec<KeySlot>), crate::types::Ty> = HashMap::new();
    let key = vec![t.int_lit(21)];
    let int = t.int();
    let ok = t.atom_lit("ok");
    er.insert((fid(7), key_tys(key.clone())), int.clone());
    er.insert((fid(8), key_tys(key)), ok.clone());
    let arg_tys = [t.int_lit(21)];
    let r = resolve_closure_return(&mut t, &closure, &er, &arg_tys).unwrap();
    let expected = t.union(int, ok);
    assert!(t.is_equivalent(&r, &expected));
}

#[test]
fn resolve_closure_return_union_one_miss_defers() {
    // Two clauses; one has a registered spec, the other doesn't. The
    // helper conservatively defers (returns None) so the typer's
    // fixpoint can re-try after the missing spec is registered.
    let mut t = crate::types::ConcreteTypes;
    let a = t.closure_lit(fid(7).into(), vec![], 1);
    let b = t.closure_lit(fid(8).into(), vec![], 1);
    let closure = t.union(a, b);
    let mut er: HashMap<(FnId, Vec<KeySlot>), crate::types::Ty> = HashMap::new();
    let key = t.int_lit(21);
    let int = t.int();
    er.insert((fid(7), key_tys(vec![key])), int);
    // No entry for (8, _) → defer.
    let arg_tys = [t.int_lit(21)];
    let r = resolve_closure_return(&mut t, &closure, &er, &arg_tys);
    assert_eq!(r, None);
}

#[test]
fn resolve_closure_return_empty_funcs_is_any() {
    // Type with no funcs at all: arrow_join_return-style any default.
    let er: HashMap<(FnId, Vec<KeySlot>), crate::types::Ty> = HashMap::new();
    let mut t = crate::types::ConcreteTypes;
    let closure = t.none();
    let r = resolve_closure_return(&mut t, &closure, &er, &[]).unwrap();
    let any = t.any();
    assert!(t.is_equivalent(&r, &any));
}

#[test]
fn resolve_closure_return_saturated_arrow_is_any() {
    // `any()` has funcs = [Conj::top()] — pos empty, no narrowing.
    let er: HashMap<(FnId, Vec<KeySlot>), crate::types::Ty> = HashMap::new();
    let mut t = crate::types::ConcreteTypes;
    let closure = t.any();
    let arg_tys = [t.int_lit(21)];
    let r = resolve_closure_return(&mut t, &closure, &er, &arg_tys).unwrap();
    let any = t.any();
    assert!(t.is_equivalent(&r, &any));
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

    let mut t = crate::types::ConcreteTypes;
    let mut env: HashMap<Var, crate::types::Ty> = HashMap::new();
    let any_ty = t.any();
    let ok_ty = t.atom_lit("ok");
    let one_ty = t.int_lit(1);
    let bool_ty = t.bool();
    env.insert(x, any_ty.clone());
    env.insert(y, any_ty);
    // lit_ok and lit_one already have singleton types in env.
    env.insert(lit_ok, ok_ty.clone());
    env.insert(lit_one, one_ty.clone());
    env.insert(cx, bool_ty.clone());
    env.insert(cy, bool_ty.clone());
    env.insert(cand, bool_ty);

    let (then_env, else_env) = narrow_for_cond(&mut t, cand, &env, &stmts);

    // Then branch: x must be :ok and y must be 1.
    let x_then = then_env.get(&x).expect("then branch should retain x");
    let y_then = then_env.get(&y).expect("then branch should retain y");
    assert!(t.is_equivalent(x_then, &ok_ty));
    assert!(t.is_equivalent(y_then, &one_ty));

    // Else branch: at least one failed — union of "x != :ok" and "y != 1".
    // Neither is fully pinned to the singleton.
    let x_else = else_env.get(&x).expect("else branch should retain x");
    let y_else = else_env.get(&y).expect("else branch should retain y");
    assert!(!t.is_equivalent(x_else, &ok_ty));
    assert!(!t.is_equivalent(y_else, &one_ty));
}

/// fz-9pr.1 — EmitterSite ↔ CallsiteId round-trip. Drops then re-attaches
/// a spec-key, recovering the original site exactly. Guards the
/// projection used by reducer / ir_inline / typer to share one
/// callsite vocabulary.
#[test]
fn callsite_id_round_trip() {
    use crate::fz_ir::{BlockId, CallsiteId, EmitSlot};

    let mut t = crate::types::ConcreteTypes;
    let any = t.any();
    let three = t.int_lit(3);
    let spec_key = (FnId(7), key_tys(vec![any, three]));
    let _ = BlockId(2); // older positional fixture data; ident is now intrinsic.
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
/// at main's spec keyed by `id` plus the literal arg type.
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
    let _ = (BlockId(0), m_entry); // older positional fixture data.

    let mut mb = crate::fz_ir::ModuleBuilder::new();
    mb.add_fn(id_b.build());
    mb.add_fn(main_b.build());
    let m = mb.build();
    let mut t = crate::types::ConcreteTypes;
    let mt = type_module(&mut t, &m, &crate::telemetry::NullTelemetry);

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
    let Some(ty) = &key[0] else {
        panic!("direct dispatch arg should be typed, got {:?}", key[0]);
    };
    assert_eq!(t.as_int_singleton(ty), Some(42));
}

// ---- fz-swt.8 — `.value` accessor: typing + visibility gating ----

/// Inside the declaring module, `handle.value` typechecks as the inner
/// `T` recorded on the opaque alias — not as the generic
/// `any().union(nil())` map-lookup fallback. The handle
/// here is a fn parameter typed as `A.t` (where `A` declares
/// `@type t :: opaque resource(integer)`), and the body returns
/// `h.value`. The inferred return must be a subtype of `integer`.
#[test]
fn value_accessor_inside_declaring_module_types_as_inner() {
    // Param uses the `x :: T` annotation form so ir_lower emits a
    // `TypeTest` guard; the typer's narrowing then pins the param to
    // `A::t` along the pass-branch entry block. Without the
    // annotation, the param would be `any` and the `.value` accessor
    // would fall through to the generic map-lookup result. The
    // top-level `main` exists only to seed the typer entry — without
    // a caller, `A.get/1` has no registered spec.
    let src = r#"
defmodule A do
  @type t :: opaque resource(integer)

  fn get(h :: t), do: h.value
end

fn main() do
  h = make_resource(7, &print/1)
  A.get(h)
end
"#;
    let (mut t, m, mt) = pipeline(src, &crate::telemetry::NullTelemetry);
    let f = m.fn_by_name("A.get").expect("A.get exists post-lower");
    let ft = mt.any_spec_for(f.id).unwrap_or_else(|| {
        let keys: Vec<_> = mt.specs.keys().filter(|(fid, _)| *fid == f.id).collect();
        panic!("no spec for A.get/1; have keys: {:?}", keys);
    });
    // The fn body lowers `h.value` to a `Prim::MapGet(h, :value)`
    // (TypeTest dispatch wraps it in a few blocks). Find that stmt's
    // result var and check its inferred type — it must be a subtype
    // of integer once the typer reads `m.opaque_inners["A::t"]`.
    let mut found = false;
    for b in &f.blocks {
        for stmt in &b.stmts {
            let crate::fz_ir::Stmt::Let(v, prim) = stmt;
            if matches!(prim, Prim::MapGet(_, _))
                && let Some(rt) = ft.vars.get(v)
            {
                let int = t.int();
                assert!(
                    t.is_subtype(rt, &int),
                    "h.value should type as integer (inner T), got `{}`",
                    t.display(rt),
                );
                found = true;
            }
        }
    }
    assert!(found, "expected at least one MapGet stmt in A.get");
}

/// Outside the declaring module, `handle.value` is rejected with a
/// `type/opaque-visibility` diagnostic. We build the failure scenario
/// directly at the IR layer: a tiny module-with-opaques table, an
/// `A.get`-style fn renamed to live in module `B`, and a synthetic
/// `Module.opaque_inners["A::t"] -> integer` entry. This bypasses the
/// surface-syntax gap that module-qualified type annotations like
/// `h :: A.t` aren't yet resolvable (`type_expr::lookup_named` keys
/// the env on bare alias names), and instead exercises exactly the
/// thing the gate is meant to police: a value already typed as an
/// opaque declared elsewhere.
#[test]
fn value_accessor_outside_declaring_module_emits_diagnostic() {
    use crate::fz_ir::{Const, FnBuilder, FnId, ModuleBuilder, Prim, Term};
    // Module name `B` (post-resolve dotted form: `"B.peek"`).
    // The fn typechecks under a narrow spec where param is `A::t`.
    let mut b = FnBuilder::new(FnId(0), "B.peek");
    let h = b.fresh_var();
    let entry = b.block(vec![h]);
    // key var `:value`
    let key = b.let_(entry, Prim::Const(Const::Atom(0)));
    let v = b.let_(entry, Prim::MapGet(h, key));
    b.set_terminator(entry, Term::Return(v));
    let mut mb = ModuleBuilder::new();
    mb.add_fn(b.build());
    let mut m = mb.build();
    // Atom 0 is `:value`. (atom_names is empty by default; populate
    // index 0 so `var_as_map_key` returns the right key.)
    m.atom_names = vec!["value".to_string()];
    // Record the inner type for the opaque "A::t" alias declared in
    // module A.
    let mut ct = crate::types::ConcreteTypes;
    m.opaque_inners.insert("A::t".to_string(), ct.int());

    // Drive the typer under a narrow spec that pins `h` to A::t.
    let narrow_key_ty = vec![ct.opaque_of("A::t")];
    let ft = crate::ir_typer::type_fn(&mut ct, &m.fns[0], &m, Some(&narrow_key_ty));
    // Register the spec so collect_diagnostics picks it up.
    let mut mt = crate::ir_typer::type_module(&mut ct, &m, &crate::telemetry::NullTelemetry);
    mt.specs.insert((FnId(0), key_tys(narrow_key_ty)), ft);

    let diags = crate::ir_typer::collect_diagnostics(&mut ct, &m, &mt);
    let visibility = diags
        .iter()
        .find(|d| d.code == crate::diag::codes::TYPE_OPAQUE_VISIBILITY)
        .unwrap_or_else(|| {
            panic!(
                "expected a type/opaque-visibility diagnostic; got: {:?}",
                diags
                    .iter()
                    .map(|d| (d.code, &d.message))
                    .collect::<Vec<_>>(),
            )
        });
    assert!(
        visibility.message.contains("A::t"),
        "diag should mention the qualified opaque tag `A::t`; got: {}",
        visibility.message,
    );
    assert!(
        visibility
            .message
            .contains("not accessible from module `B`"),
        "diag should mention the using module `B`; got: {}",
        visibility.message,
    );
    assert!(
        visibility.message.contains("declared in module `A`"),
        "diag should mention the declaring module `A`; got: {}",
        visibility.message,
    );
}

/// Sibling fns in the declaring module reach `.value` without any
/// diagnostic. Pairs with the rejecting test above to prove the gate
/// is module-scoped, not whole-program.
#[test]
fn value_accessor_inside_declaring_module_emits_no_diagnostic() {
    let src = r#"
defmodule A do
  @type t :: opaque resource(integer)

  fn get(h :: t), do: h.value
end
"#;
    let (mut t, m, mt) = pipeline(src, &crate::telemetry::NullTelemetry);
    let diags = crate::ir_typer::collect_diagnostics(&mut t, &m, &mt);
    assert!(
        !diags
            .iter()
            .any(|d| d.code == crate::diag::codes::TYPE_OPAQUE_VISIBILITY),
        "no opaque-visibility diag should fire from inside the declaring module; got: {:?}",
        diags
            .iter()
            .map(|d| (d.code, &d.message))
            .collect::<Vec<_>>(),
    );
}

// fz-axu.1 (K0) — bitstring construction types as str_t().
// Pre-refines, MakeBitstring/ConstBitstring typed as `vec_u8 | vec_bit`. Post-K0
// they type as `str_t()` — the binary/bitstring top of the strs axis — so that
// future tickets can layer the `utf8` brand on top as a proper subset.

#[test]
fn make_bitstring_types_as_str_t() {
    let mut b = FnBuilder::new(FnId(0), "main");
    let entry = b.block(vec![]);
    let bs = b.let_(entry, Prim::MakeBitstring(vec![]));
    b.set_terminator(entry, Term::Halt(bs));
    let m = build_module(vec![b.build()]);
    let mut t = crate::types::ConcreteTypes;
    let mt = type_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    let bs_t = fn_view(&mut t, &m, &mt, 0).vars.get(&bs).unwrap().clone();
    let str_t = t.str_t();
    assert!(
        t.is_equivalent(&bs_t, &str_t),
        "expected MakeBitstring to type as str_t(); got {}",
        t.display(&bs_t),
    );
}

// fz-axu.11 (L3) — string literals lower to a `utf8`-branded
// const bitstring through ir_lower. End-to-end shape: the typer
// publishes the literal's Var as having `brands = {utf8}` and the
// strs axis populated.

#[test]
fn string_literal_lowers_to_utf8_branded_bitstring() {
    // fz-axu.23 (M2) — lower_program_full erases Brand prims as its
    // final phase. The post-erasure invariant is that the ConstBitstring
    // survives and Module.brand_inners still names utf8 (so the type
    // system can recover the brand context when needed), but no
    // Prim::Brand stmt remains in any FnIr.
    let src = r#"fn main(), do: "hi""#;
    let toks = crate::lexer::Lexer::new(src).tokenize().expect("lex");
    let prog = crate::parser::Parser::new(toks)
        .parse_program()
        .expect("parse");
    let mut ct = crate::types::ConcreteTypes;
    let prog = crate::resolve::flatten_modules(&mut ct, prog).expect("resolve");
    let m = crate::ir_lower::lower_program(&mut ct, &prog).expect("lower");
    let main = m.fn_by_name("main").expect("main");
    let mut saw_const_bs = false;
    for block in &main.blocks {
        for stmt in &block.stmts {
            let crate::fz_ir::Stmt::Let(_, prim) = stmt;
            assert!(
                !matches!(prim, Prim::Brand(..)),
                "Prim::Brand survived lowering: {:?}",
                prim,
            );
            if let Prim::ConstBitstring(bytes, bit_len) = prim
                && bytes == b"hi"
                && *bit_len == 16
            {
                saw_const_bs = true;
            }
        }
    }
    assert!(saw_const_bs, "expected ConstBitstring(b\"hi\", 16)");
    assert!(
        m.brand_inners.contains_key("utf8"),
        "Module.brand_inners must still name utf8 after erasure",
    );
}

// fz-axu.4 (K3) — Prim::Brand(v, name) overlays the brand tag on the
// source's structural type. The runtime sees identity; the type system
// records the brand membership.

#[test]
fn brand_overlays_brand_tag_on_source_type() {
    let mut b = FnBuilder::new(FnId(0), "main");
    let entry = b.block(vec![]);
    let bs = b.let_(entry, Prim::ConstBitstring(vec![104, 105], 16));
    let branded = b.let_(entry, Prim::Brand(bs, "utf8".to_string()));
    b.set_terminator(entry, Term::Halt(branded));
    let m = build_module(vec![b.build()]);
    let mut ct = crate::types::ConcreteTypes;
    let mt = type_module(&mut ct, &m, &crate::telemetry::NullTelemetry);
    let ft = fn_view(&mut ct, &m, &mt, 0);
    let source_ty = ft.vars.get(&bs).unwrap().clone();
    let branded_ty = ft.vars.get(&branded).unwrap().clone();
    let expected = ct.mint_brand(source_ty.clone(), "utf8");
    assert!(
        ct.is_equivalent(&branded_ty, &expected),
        "Brand(v, tag) must type like mint_brand(type(v), tag); got {}",
        ct.display(&branded_ty),
    );
    let str_t = ct.str_t();
    assert!(
        ct.is_subtype(&str_t, &source_ty),
        "brand-preserved structural type must still subsume str_t(); got {}",
        ct.display(&source_ty),
    );
}

#[test]
fn brand_does_not_change_underlying_runtime_shape() {
    // Sanity: typing of Brand(v, _) preserves the source's non-brand
    // axes. Distinct from the above by stripping the source from a
    // singleton bitstring const.
    let mut b = FnBuilder::new(FnId(0), "main");
    let entry = b.block(vec![]);
    let bs = b.let_(entry, Prim::MakeBitstring(vec![]));
    let branded = b.let_(entry, Prim::Brand(bs, "ascii".to_string()));
    b.set_terminator(entry, Term::Halt(branded));
    let m = build_module(vec![b.build()]);
    let mut ct = crate::types::ConcreteTypes;
    let mt = type_module(&mut ct, &m, &crate::telemetry::NullTelemetry);
    let ft = fn_view(&mut ct, &m, &mt, 0);
    let source_t = ft.vars.get(&bs).unwrap().clone();
    let branded_t = ft.vars.get(&branded).unwrap().clone();
    let expected = ct.mint_brand(source_t.clone(), "ascii");
    assert!(
        ct.is_equivalent(&branded_t, &expected),
        "Brand must preserve source axes; source={}, branded={}",
        ct.display(&source_t),
        ct.display(&branded_t),
    );
}

#[test]
fn const_bitstring_types_as_str_t() {
    let mut b = FnBuilder::new(FnId(0), "main");
    let entry = b.block(vec![]);
    let bs = b.let_(entry, Prim::ConstBitstring(vec![1, 2, 3], 24));
    b.set_terminator(entry, Term::Halt(bs));
    let m = build_module(vec![b.build()]);
    let mut t = crate::types::ConcreteTypes;
    let mt = type_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    let bs_t = fn_view(&mut t, &m, &mt, 0).vars.get(&bs).unwrap().clone();
    let str_t = t.str_t();
    assert!(
        t.is_equivalent(&bs_t, &str_t),
        "expected ConstBitstring to type as str_t(); got {}",
        t.display(&bs_t),
    );
}

// ----- fz-l4c: typer rejects arithmetic on opaque-integer types -----

#[test]
fn opaque_arithmetic_pid_plus_int_rejected() {
    let src = "fn main(), do: self() + 1";
    let (mut t, m, mt) = pipeline(src, &crate::telemetry::NullTelemetry);
    let diags = crate::ir_typer::collect_diagnostics(&mut t, &m, &mt);
    let d = diags
        .iter()
        .find(|d| d.code == crate::diag::codes::TYPE_OPAQUE_ARITHMETIC)
        .unwrap_or_else(|| {
            panic!(
                "expected a type/opaque-arithmetic diagnostic; got: {:?}",
                diags
                    .iter()
                    .map(|d| (d.code, &d.message))
                    .collect::<Vec<_>>(),
            )
        });
    assert!(
        d.message.contains("pid"),
        "diag should name `pid`; got: {}",
        d.message
    );
    assert!(
        d.message.contains("+"),
        "diag should name the offending operator; got: {}",
        d.message
    );
}

#[test]
fn opaque_arithmetic_ref_plus_int_rejected() {
    let src = "fn main(), do: make_ref() + 1";
    let (mut t, m, mt) = pipeline(src, &crate::telemetry::NullTelemetry);
    let diags = crate::ir_typer::collect_diagnostics(&mut t, &m, &mt);
    assert!(
        diags
            .iter()
            .any(|d| d.code == crate::diag::codes::TYPE_OPAQUE_ARITHMETIC),
        "expected type/opaque-arithmetic on make_ref() + 1; got: {:?}",
        diags
            .iter()
            .map(|d| (d.code, &d.message))
            .collect::<Vec<_>>(),
    );
}

#[test]
fn opaque_equality_remains_permitted() {
    // Pid/ref equality is load-bearing for the selective-receive matcher
    // (`^pinned == msg_field`); comparison must NOT raise the new diagnostic.
    let src = r#"
fn main() do
  a = self()
  b = self()
  a == b
end
"#;
    let (mut t, m, mt) = pipeline(src, &crate::telemetry::NullTelemetry);
    let diags = crate::ir_typer::collect_diagnostics(&mut t, &m, &mt);
    assert!(
        !diags
            .iter()
            .any(|d| d.code == crate::diag::codes::TYPE_OPAQUE_ARITHMETIC),
        "equality must not raise type/opaque-arithmetic; got: {:?}",
        diags
            .iter()
            .map(|d| (d.code, &d.message))
            .collect::<Vec<_>>(),
    );
}

#[test]
fn plain_int_arithmetic_still_passes() {
    let src = "fn main(), do: 1 + 1";
    let (mut t, m, mt) = pipeline(src, &crate::telemetry::NullTelemetry);
    let diags = crate::ir_typer::collect_diagnostics(&mut t, &m, &mt);
    assert!(
        !diags
            .iter()
            .any(|d| d.code == crate::diag::codes::TYPE_OPAQUE_ARITHMETIC),
        "plain int arithmetic must not raise the diagnostic; got: {:?}",
        diags
            .iter()
            .map(|d| (d.code, &d.message))
            .collect::<Vec<_>>(),
    );
}
