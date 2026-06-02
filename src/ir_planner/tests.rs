use super::closures::resolve_closure_return;
use super::fn_types::CallableCapability;
use super::fn_types::{EmitterSite, SpecKey};
use super::narrow::narrow_for_cond;
use super::reachable::cont_slot0_descr;
use super::type_fn::type_fn;
use super::*;
use crate::fz_ir::{
    BinOp, Const, ExternDecl, ExternId, ExternTy, FnBuilder, FnId, InitTokenId, Module,
    ModuleBuilder, Prim, Stmt, Term, Var,
};
use crate::ir_dest::{lower_list_destinations, lower_map_destinations, lower_tuple_destinations};
use crate::types::{ClosureTypes, KeySlot, Types};
use std::collections::HashMap;

fn key_tys(tys: Vec<crate::types::Ty>) -> Vec<KeySlot> {
    crate::types::key_slots_from_tys(tys)
}

fn value_spec_key(fid: FnId, input: Vec<KeySlot>) -> SpecKey {
    SpecKey::value(fid, input)
}

fn slot_ty(slot: &KeySlot) -> Option<&crate::types::Ty> {
    slot.as_ref()
}

fn module_plan_spec_ty<'a>(
    mt: &'a ModulePlan,
    fn_id: FnId,
    input_tys: &[crate::types::Ty],
) -> Option<&'a SpecPlan> {
    let key = mt.specs.keys().find(|spec_key| {
        spec_key.fn_id == fn_id
            && spec_key.demand.is_value()
            && spec_key.input.len() == input_tys.len()
            && spec_key
                .input
                .iter()
                .zip(input_tys.iter())
                .all(|(slot, ty)| match slot {
                    None => true,
                    Some(k) => k == ty,
                })
    })?;
    mt.specs.get(key)
}

fn emitter_site_callsite_id(site: &EmitterSite) -> crate::fz_ir::CallsiteId {
    crate::fz_ir::CallsiteId::new(site.caller.fn_id, &site.ident, site.slot)
}

fn callsite_with_spec_key(cid: crate::fz_ir::CallsiteId, spec_key: SpecKey) -> EmitterSite {
    assert_eq!(cid.caller, spec_key.fn_id);
    EmitterSite {
        caller: spec_key,
        ident: cid.ident,
        slot: cid.slot,
    }
}

fn lambda_any_key_specs(
    t: &mut crate::types::ConcreteTypes,
    m: &Module,
    mt: &ModulePlan,
) -> Vec<SpecKey> {
    mt.specs
        .keys()
        .filter(|key| {
            let f = m.fn_by_id(key.fn_id);
            f.name.starts_with("lambda_")
                && key.demand.is_value()
                && key.input.len() == f.block(f.entry).params.len()
                && key
                    .input
                    .iter()
                    .all(|slot| slot_ty(slot).is_some_and(|ty| t.is_top(ty)))
        })
        .cloned()
        .collect()
}

fn lambda_value_specs(m: &Module, mt: &ModulePlan) -> Vec<SpecKey> {
    mt.specs
        .keys()
        .filter(|key| {
            let f = m.fn_by_id(key.fn_id);
            f.name.starts_with("lambda_") && key.demand.is_value()
        })
        .cloned()
        .collect()
}

fn build_module(fns: Vec<crate::fz_ir::FnIr>) -> Module {
    let mut mb = ModuleBuilder::new();
    for f in fns {
        mb.add_fn(f);
    }
    mb.build()
}

fn lower_src_for_plan(src: &str) -> Module {
    let toks = crate::parser::lexer::Lexer::new(src)
        .tokenize()
        .expect("lex");
    let prog = crate::parser::Parser::new(toks)
        .parse_program()
        .expect("parse");
    crate::ir_lower::lower_program(
        &mut crate::types::ConcreteTypes,
        &prog,
        &crate::telemetry::NullTelemetry,
    )
    .expect("lower")
}

fn count_if_terminators(f: &crate::fz_ir::FnIr) -> usize {
    f.blocks
        .iter()
        .filter(|block| matches!(block.terminator, Term::If { .. }))
        .count()
}

fn count_fold_candidate_prims(f: &crate::fz_ir::FnIr) -> usize {
    f.blocks
        .iter()
        .flat_map(|block| block.stmts.iter())
        .filter(|stmt| matches!(stmt, Stmt::Let(_, Prim::BinOp(..) | Prim::TypeTest(..))))
        .count()
}

#[derive(Debug)]
struct TestDeclaredReturnFact {
    ty: crate::types::Ty,
    complete: bool,
    reads: Vec<SpecKey>,
}

fn declared_return_fact_for_test<T>(
    t: &mut T,
    module: &Module,
    caller: FnId,
    callee: FnId,
    arg_tys: &[crate::types::Ty],
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    complete_returns: Option<&super::fn_types::SpecKeySet>,
) -> Option<TestDeclaredReturnFact>
where
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
{
    let spec_set = module.declared_specs.get(&callee)?;
    let recursive_fns = std::collections::HashSet::new();
    let slot_summaries = super::fn_types::FixedPointSlotSummaries::new();
    let application = crate::specs::apply_spec_set(
        t,
        spec_set,
        arg_tys,
        |t, query: crate::specs::CallbackReturnQuery<'_>| {
            test_callback_return_fact(
                t,
                module,
                &recursive_fns,
                &slot_summaries,
                caller,
                effective_returns,
                complete_returns,
                query,
            )
        },
    );
    match application {
        crate::specs::SpecApplicationOutcome::Known(application) => Some(TestDeclaredReturnFact {
            ty: application.result,
            complete: application.complete,
            reads: application.reads,
        }),
        crate::specs::SpecApplicationOutcome::Underconstrained(application) => {
            application.partial_result.map(|ty| TestDeclaredReturnFact {
                ty,
                complete: false,
                reads: application.reads,
            })
        }
        crate::specs::SpecApplicationOutcome::NoMatch => None,
    }
}

#[allow(clippy::too_many_arguments)]
fn test_callback_return_fact<T>(
    t: &mut T,
    module: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    slot_summaries: &super::fn_types::FixedPointSlotSummaries,
    caller: FnId,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    complete_returns: Option<&super::fn_types::SpecKeySet>,
    query: crate::specs::CallbackReturnQuery<'_>,
) -> Option<crate::specs::CallbackReturnFact<SpecKey>>
where
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
{
    let fn_id: FnId = query.target.into();
    let target_fn = module.fn_by_id(fn_id);
    let n_params = target_fn.block(target_fn.entry).params.len();
    let mut full_key = query.captures.to_vec();
    full_key.extend_from_slice(query.args);
    let key = super::fn_types::fixed_point_spec_key_for_arity(
        t,
        module,
        recursive_fns,
        slot_summaries,
        caller,
        fn_id,
        full_key,
        n_params,
        Some(test_callback_return_demand(query.demand)),
    );
    let Some(ret) = effective_returns.get(&key).cloned() else {
        return Some(crate::specs::CallbackReturnFact::Pending { read: key });
    };
    if complete_returns.is_some_and(|done| !done.contains(&key)) {
        return Some(crate::specs::CallbackReturnFact::Pending { read: key });
    }
    Some(crate::specs::CallbackReturnFact::Known {
        result: ret,
        read: key,
        complete: true,
    })
}

fn test_callback_return_demand(
    demand: crate::specs::CallbackReturnDemand,
) -> super::fn_types::ReturnDemand {
    match demand {
        crate::specs::CallbackReturnDemand::Value => super::fn_types::ReturnDemand::value(),
        crate::specs::CallbackReturnDemand::TupleFields(arity) => {
            super::fn_types::ReturnDemand::tuple_fields(arity)
        }
    }
}

fn extern_decl(
    t: &mut crate::types::ConcreteTypes,
    id: ExternId,
    symbol: &str,
    ret: ExternTy,
) -> ExternDecl {
    ExternDecl {
        id,
        fz_name: symbol.to_string(),
        symbol: symbol.to_string(),
        params: Vec::new(),
        variadic: false,
        ret,
        ret_descr: match ret {
            ExternTy::Unit => t.nil(),
            ExternTy::Never => t.none(),
            ExternTy::I64 => t.int(),
            _ => t.any(),
        },
    }
}

/// fz-pky.2 — test helper. Returns "the most narrow registered
/// spec for fn at index i, or an ad-hoc any-key view if unregistered."
fn fn_view(t: &mut crate::types::ConcreteTypes, m: &Module, mt: &ModulePlan, i: usize) -> SpecPlan {
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

fn ty_for_var_in_fn(
    t: &mut crate::types::ConcreteTypes,
    m: &Module,
    fn_index: usize,
    var: Var,
) -> crate::types::Ty {
    let mt = plan_module(t, m, &crate::telemetry::NullTelemetry);
    fn_view(t, m, &mt, fn_index)
        .vars
        .get(&var)
        .unwrap_or_else(|| panic!("missing type for {}", var))
        .clone()
}

fn only_effect_summary(
    t: &mut crate::types::ConcreteTypes,
    m: &Module,
    fid: FnId,
) -> super::fn_types::EffectSummary {
    let mt = plan_module(t, m, &crate::telemetry::NullTelemetry);
    *mt.fn_effects
        .get(&fid)
        .expect("missing effect summary for fn")
}

#[test]
fn effect_summary_tracks_allocation_without_observability() {
    let mut t = crate::types::ConcreteTypes;
    let mut b = FnBuilder::new(FnId(0), "main");
    let entry = b.block(vec![]);
    let one = b.let_(entry, Prim::Const(Const::Int(1)));
    let list = b.let_(entry, Prim::MakeList(vec![one], None));
    b.set_terminator(entry, Term::Return(list));
    let m = build_module(vec![b.build()]);

    let effects = only_effect_summary(&mut t, &m, FnId(0));
    assert!(effects.allocates);
    assert!(!effects.observable);
    assert!(!effects.reads_allocation_stats);
}

#[test]
fn effect_summary_marks_extern_and_heap_stats_observer() {
    let mut t = crate::types::ConcreteTypes;
    let mut b = FnBuilder::new(FnId(0), "main");
    let entry = b.block(vec![]);
    let stats = b.let_(
        entry,
        Prim::Extern(
            crate::fz_ir::CallsiteIdent::synthetic(),
            ExternId(0),
            vec![],
        ),
    );
    b.set_terminator(entry, Term::Return(stats));
    let mut m = build_module(vec![b.build()]);
    m.externs.push(extern_decl(
        &mut t,
        ExternId(0),
        "fz_process_heap_alloc_stats",
        ExternTy::Any,
    ));
    m.extern_idx.insert(ExternId(0), 0);

    let effects = only_effect_summary(&mut t, &m, FnId(0));
    assert!(effects.observable);
    assert!(effects.reads_allocation_stats);
}

#[test]
fn effect_summary_propagates_observable_tail_calls() {
    let mut t = crate::types::ConcreteTypes;
    let mut helper = FnBuilder::new(FnId(1), "helper");
    let helper_entry = helper.block(vec![]);
    let nil = helper.let_(
        helper_entry,
        Prim::Extern(
            crate::fz_ir::CallsiteIdent::synthetic(),
            ExternId(0),
            vec![],
        ),
    );
    helper.set_terminator(helper_entry, Term::Return(nil));

    let mut main = FnBuilder::new(FnId(0), "main");
    let main_entry = main.block(vec![]);
    main.set_terminator(
        main_entry,
        Term::TailCall {
            ident: crate::fz_ir::CallsiteIdent::synthetic(),
            callee: FnId(1),
            args: Vec::new(),
            is_back_edge: false,
        },
    );
    let mut m = build_module(vec![main.build(), helper.build()]);
    m.externs.push(extern_decl(
        &mut t,
        ExternId(0),
        "fz_dbg_value",
        ExternTy::Unit,
    ));
    m.extern_idx.insert(ExternId(0), 0);

    let effects = only_effect_summary(&mut t, &m, FnId(0));
    assert!(effects.observable);
    assert!(!effects.reads_allocation_stats);
}

// ---- .24.2 tests (preserved, adjusted to SpecPlan API) ----

#[test]
fn const_int_typed_as_singleton() {
    let mut b = FnBuilder::new(FnId(0), "main");
    let entry = b.block(vec![]);
    let v = b.let_(entry, Prim::Const(Const::Int(42)));
    b.set_terminator(entry, Term::Halt(v));
    let m = build_module(vec![b.build()]);
    let mut t = crate::types::ConcreteTypes;
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);
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
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);
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
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    let lt = fn_view(&mut t, &m, &mt, 0).vars.get(&l).unwrap().clone();
    let elem = t.list_element_type(&lt);
    let int = t.int();
    assert_ty_subtype(&mut t, &elem, &int);
    assert_ty_not_empty(&t, &elem);
}

#[test]
fn list_literal_onto_empty_list_keeps_head_element_type() {
    let mut b = FnBuilder::new(FnId(0), "f");
    let entry = b.block(vec![]);
    let one = b.let_(entry, Prim::Const(Const::Int(1)));
    let empty = b.let_(entry, Prim::MakeList(vec![], None));
    let cons = b.let_(entry, Prim::MakeList(vec![one], Some(empty)));
    b.set_terminator(entry, Term::Return(cons));

    let m = build_module(vec![b.build()]);
    let mut t = crate::types::ConcreteTypes;
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);
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
fn lowered_list_freeze_preserves_make_list_type_with_tail() {
    let mut b = FnBuilder::new(FnId(0), "list_dp_type");
    let tail = b.fresh_var();
    let entry = b.block(vec![tail]);
    let one = b.let_(entry, Prim::Const(Const::Int(1)));
    let ok = b.let_(entry, Prim::Const(Const::Atom(7)));
    let list = b.let_(entry, Prim::MakeList(vec![one, ok], Some(tail)));
    b.set_terminator(entry, Term::Return(list));

    let mut m = build_module(vec![b.build()]);
    let mut t = crate::types::ConcreteTypes;
    let tail_elem = t.atom_lit("tail_elem");
    let tail_ty = t.list(tail_elem.clone());
    let original_types = type_fn(&mut t, &m.fns[0], &m, Some(std::slice::from_ref(&tail_ty)));
    lower_list_destinations(&mut m);
    let lowered_types = type_fn(&mut t, &m.fns[0], &m, Some(std::slice::from_ref(&tail_ty)));

    let original = original_types.vars.get(&list).unwrap();
    let lowered = lowered_types.vars.get(&list).unwrap();
    assert!(
        t.is_equivalent(original, lowered),
        "type(MakeList(xs, tail)) == type(DestListFreeze(lower(MakeList(xs, tail)))): before {}, after {}",
        t.display(original),
        t.display(lowered)
    );
    let elem = t.list_element_type(lowered);
    assert!(
        t.is_subtype(&tail_elem, &elem),
        "lowered list element type should retain tail element evidence: {}",
        t.display(lowered)
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
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);
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
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);
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
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);
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
    //   else_b: return l   (l narrowed to any except [] here)
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
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);

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

    // In else_b's entry env, l should keep every value except the empty-list
    // shape. Non-list values are also definitely "not []".
    let else_env = ft.block_envs.get(&else_b).unwrap();
    let l_else = else_env.get(&l).unwrap();
    let any = t.any();
    let empty_list = t.empty_list();
    let not_empty_list = t.difference(any, empty_list);
    assert!(
        t.is_equivalent(l_else, &not_empty_list),
        "l in else-branch should exclude only the empty list: {}",
        t.display(l_else)
    );
}

#[test]
fn if_is_list_cons_narrows_only_then_branch_to_non_empty_list() {
    let mut b = FnBuilder::new(FnId(0), "f");
    let value = b.fresh_var();
    let entry = b.block(vec![value]);
    let cond = b.let_(entry, Prim::IsListCons(value));
    let then_b = b.block(vec![]);
    let else_b = b.block(vec![]);
    b.set_terminator(entry, Term::if_user(cond, then_b, else_b));
    b.set_terminator(then_b, Term::Return(value));
    b.set_terminator(else_b, Term::Return(value));
    let m = build_module(vec![b.build()]);
    let mut t = crate::types::ConcreteTypes;
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    let ft = fn_view(&mut t, &m, &mt, 0);

    let then_ty = ft.block_envs.get(&then_b).unwrap().get(&value).unwrap();
    let any = t.any();
    let nonempty_any = t.non_empty_list(any);
    assert!(
        t.is_equivalent(then_ty, &nonempty_any),
        "then branch should be a non-empty list: {}",
        t.display(then_ty)
    );

    let else_ty = ft.block_envs.get(&else_b).unwrap().get(&value).unwrap();
    assert!(
        !t.is_subtype(else_ty, &nonempty_any),
        "else branch must keep non-list values possible: {}",
        t.display(else_ty)
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
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);

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
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    let p00_t = fn_view(&mut t, &m, &mt, 0).vars.get(&p00).unwrap().clone();
    assert_eq!(
        t.as_int_singleton(&p00_t),
        Some(7),
        "got {}",
        t.display(&p00_t)
    );
}

#[test]
fn lowered_tuple_freeze_preserves_make_tuple_type() {
    let mut b = FnBuilder::new(FnId(0), "tuple_dp_type");
    let entry = b.block(vec![]);
    let one = b.let_(entry, Prim::Const(Const::Int(1)));
    let ok = b.let_(entry, Prim::Const(Const::Atom(7)));
    let tuple = b.let_(entry, Prim::MakeTuple(vec![one, ok]));
    b.set_terminator(entry, Term::Return(tuple));

    let original = build_module(vec![b.build()]);
    let mut lowered = original.clone();
    lower_tuple_destinations(&mut lowered);

    let mut t = crate::types::ConcreteTypes;
    let before = ty_for_var_in_fn(&mut t, &original, 0, tuple);
    let after = ty_for_var_in_fn(&mut t, &lowered, 0, tuple);
    assert!(
        t.is_equivalent(&before, &after),
        "type(MakeTuple(xs)) == type(DestFreeze(lower(MakeTuple(xs)))): before {}, after {}",
        t.display(&before),
        t.display(&after)
    );
}

#[test]
fn lowered_tuple_fields_project_variable_operand_types() {
    let mut b = FnBuilder::new(FnId(0), "tuple_dp_projection");
    let lo = b.fresh_var();
    let hi = b.fresh_var();
    let entry = b.block(vec![lo, hi]);
    let tuple = b.let_(entry, Prim::MakeTuple(vec![lo, hi]));
    let lo_field = b.let_(entry, Prim::TupleField(tuple, 0));
    let hi_field = b.let_(entry, Prim::TupleField(tuple, 1));
    b.set_terminator(entry, Term::Return(hi_field));

    let mut original = build_module(vec![b.build()]);
    let mut t = crate::types::ConcreteTypes;
    let int = t.int();
    let lo_ty = t.list(int.clone());
    let hi_ty = t.non_empty_list(int);
    let original_types = type_fn(
        &mut crate::types::ConcreteTypes,
        &original.fns[0],
        &original,
        Some(&[lo_ty.clone(), hi_ty.clone()]),
    );
    lower_tuple_destinations(&mut original);
    let lowered_types = type_fn(
        &mut crate::types::ConcreteTypes,
        &original.fns[0],
        &original,
        Some(&[lo_ty.clone(), hi_ty.clone()]),
    );

    let original_lo = original_types.vars.get(&lo_field).unwrap();
    let lowered_lo = lowered_types.vars.get(&lo_field).unwrap();
    let original_hi = original_types.vars.get(&hi_field).unwrap();
    let lowered_hi = lowered_types.vars.get(&hi_field).unwrap();
    assert!(
        t.is_equivalent(original_lo, lowered_lo),
        "lowered tuple field 0 should preserve variable operand type: before {}, after {}",
        t.display(original_lo),
        t.display(lowered_lo)
    );
    assert!(
        t.is_equivalent(original_hi, lowered_hi),
        "lowered tuple field 1 should preserve variable operand type: before {}, after {}",
        t.display(original_hi),
        t.display(lowered_hi)
    );
}

#[test]
fn malformed_tuple_token_reuse_falls_back_to_any() {
    let mut b = FnBuilder::new(FnId(0), "tuple_dp_malformed");
    let entry = b.block(vec![]);
    let dest = b.let_(
        entry,
        Prim::DestTupleBegin {
            token: InitTokenId(0),
            arity: 1,
        },
    );
    let one = b.let_(entry, Prim::Const(Const::Int(1)));
    b.let_(
        entry,
        Prim::DestTupleSet {
            dest,
            token: InitTokenId(0),
            index: 0,
            value: one,
            next: InitTokenId(1),
        },
    );
    let freeze = b.let_(
        entry,
        Prim::DestFreeze {
            dest,
            token: InitTokenId(0),
        },
    );
    b.set_terminator(entry, Term::Return(freeze));
    let m = build_module(vec![b.build()]);

    let mut t = crate::types::ConcreteTypes;
    let ty = ty_for_var_in_fn(&mut t, &m, 0, freeze);
    let any = t.any();
    assert!(
        t.is_equivalent(&ty, &any),
        "planner should conservatively fall back on tuple token reuse; got {}",
        t.display(&ty)
    );
}

// ---- .24.6 unreachable-arm diagnostics ----

#[test]
fn list_is_nil_on_int_var_flags_true_branch_unreachable() {
    // entry():
    //   five = 5
    //   c = IsEmptyList(five)    -- predicate over an int -> true branch empty
    //   if c then then_b else else_b
    // then_b: halt five    -- env[five] narrowed to int_lit(5) ∩ nil = empty
    // else_b: halt five    -- env[five] keeps int_lit(5), because 5 is not []
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
    let t = plan_module(&mut ct, &m, &crate::telemetry::NullTelemetry);
    let diags = collect_diagnostics(&mut ct, &m, &t, &crate::telemetry::NullTelemetry);
    assert_eq!(
        diags.len(),
        1,
        "expected one unreachable arm, got {:?}",
        diags
    );
    assert!(
        diags
            .as_slice()
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
    let t = plan_module(&mut ct, &m, &crate::telemetry::NullTelemetry);
    let diags = collect_diagnostics(&mut ct, &m, &t, &crate::telemetry::NullTelemetry);
    assert!(
        diags.as_slice().is_empty(),
        "expected no warnings, got {:?}",
        diags
    );
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
    let t = plan_module(&mut ct, &m, &crate::telemetry::NullTelemetry);
    let diags = collect_diagnostics(&mut ct, &m, &t, &crate::telemetry::NullTelemetry);
    // The dead-block id is mentioned in the diagnostic's notes (post-
    // .20.5 the message is the headline; details live in notes).
    let needle = format!("bb{}", dead_b.0);
    assert!(
        diags
            .as_slice()
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
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);
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

#[test]
fn lowered_make_map_preserves_static_field_type() {
    let mut b = FnBuilder::new(FnId(0), "map_dp_type");
    let entry = b.block(vec![]);
    let key_a = b.let_(entry, Prim::Const(Const::Atom(1)));
    let val_a = b.let_(entry, Prim::Const(Const::Int(11)));
    let key_b = b.let_(entry, Prim::Const(Const::Atom(2)));
    let val_b = b.let_(entry, Prim::Const(Const::Int(22)));
    let map = b.let_(entry, Prim::MakeMap(vec![(key_a, val_a), (key_b, val_b)]));
    let got = b.let_(entry, Prim::MapGet(map, key_b));
    b.set_terminator(entry, Term::Return(got));

    let original = build_module(vec![b.build()]);
    let mut lowered = original.clone();
    lower_map_destinations(&mut lowered);

    let mut t = crate::types::ConcreteTypes;
    let before = ty_for_var_in_fn(&mut t, &original, 0, map);
    let after = ty_for_var_in_fn(&mut t, &lowered, 0, map);
    assert!(
        t.is_equivalent(&before, &after),
        "type(MakeMap(static fields)) == type(DestMapFreeze(lower(MakeMap))): before {}, after {}",
        t.display(&before),
        t.display(&after)
    );
    let got_ty = ty_for_var_in_fn(&mut t, &lowered, 0, got);
    let val_b_ty = t.int_lit(22);
    assert!(
        t.is_subtype(&val_b_ty, &got_ty),
        "lowered map should retain static key lookup evidence: {}",
        t.display(&got_ty)
    );
}

#[test]
fn lowered_map_update_preserves_static_refinement() {
    let mut b = FnBuilder::new(FnId(0), "map_update_dp_type");
    let entry = b.block(vec![]);
    let key_a = b.let_(entry, Prim::Const(Const::Atom(1)));
    let val_a = b.let_(entry, Prim::Const(Const::Int(11)));
    let base = b.let_(entry, Prim::MakeMap(vec![(key_a, val_a)]));
    let key_b = b.let_(entry, Prim::Const(Const::Atom(2)));
    let val_b = b.let_(entry, Prim::Const(Const::Int(22)));
    let updated = b.let_(entry, Prim::MapUpdate(base, vec![(key_b, val_b)]));
    b.set_terminator(entry, Term::Return(updated));

    let original = build_module(vec![b.build()]);
    let mut lowered = original.clone();
    lower_map_destinations(&mut lowered);

    let mut t = crate::types::ConcreteTypes;
    let before = ty_for_var_in_fn(&mut t, &original, 0, updated);
    let after = ty_for_var_in_fn(&mut t, &lowered, 0, updated);
    assert!(
        t.is_equivalent(&before, &after),
        "lowered map update should preserve static-key refinement: before {}, after {}",
        t.display(&before),
        t.display(&after)
    );
}

#[test]
fn lowered_make_map_dynamic_key_is_map_top() {
    let mut b = FnBuilder::new(FnId(0), "map_dp_dynamic");
    let key = b.fresh_var();
    let entry = b.block(vec![key]);
    let value = b.let_(entry, Prim::Const(Const::Int(11)));
    let map = b.let_(entry, Prim::MakeMap(vec![(key, value)]));
    b.set_terminator(entry, Term::Return(map));

    let mut lowered = build_module(vec![b.build()]);
    lower_map_destinations(&mut lowered);

    let mut t = crate::types::ConcreteTypes;
    let map_ty = ty_for_var_in_fn(&mut t, &lowered, 0, map);
    let top = t.map_top();
    assert!(
        t.is_equivalent(&map_ty, &top),
        "dynamic-key destination map should conservatively widen to map_top, got {}",
        t.display(&map_ty)
    );
}

// ----- .20.8: type-rendered diagnostic prose -----

/// The unreachable-arm diagnostic carries two notes: the type the
/// variable had at the branch, and the type the narrowing demanded.
/// Both are rendered through the seam's diagnostic display, so a user
/// reading the diagnostic sees set-theoretic vocabulary the planner
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
    let t = plan_module(&mut ct, &m, &crate::telemetry::NullTelemetry);
    let diags = collect_diagnostics(&mut ct, &m, &t, &crate::telemetry::NullTelemetry);
    let d = diags
        .as_slice()
        .iter()
        .next()
        .expect("at least one diagnostic");
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
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);
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
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);
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
    // fz-ul4.29.3 removed the planner's old `closure_reachable` skip;
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
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    let nt = fn_view(&mut t, &m, &mt, 0).vars.get(&n).unwrap().clone();
    let any = t.any();
    assert!(
        t.is_equivalent(&nt, &any),
        "worker's n must stay at any (no direct callers), got {}",
        t.display(&nt)
    );
}

#[test]
fn closure_target_with_direct_caller_registers_only_typed_callsite_specs() {
    // fz-ul4.29.3: a fn that's both a MakeClosure target and called
    // directly with a typed arg gets a narrow spec keyed by the
    // direct caller's arg types.
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
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    // worker's narrow spec exists with n=int.
    let narrow_spec = module_plan_spec_ty(&mt, FnId(0), &[t.int_lit(42)])
        .or_else(|| module_plan_spec_ty(&mt, FnId(0), &[t.int()]))
        .expect("worker's narrow spec (from direct call) must be registered");
    let nt_narrow = narrow_spec.vars.get(&n).unwrap().clone();
    let int = t.int();
    assert!(
        t.is_subtype(&nt_narrow, &int),
        "worker's narrow-spec n must narrow to int, got {}",
        t.display(&nt_narrow)
    );
    assert!(
        module_plan_spec_ty(&mt, FnId(0), &[t.any()]).is_none(),
        "worker should not keep an any-key body when every callsite is typed; \
         specs: {:?}",
        mt.specs
            .keys()
            .filter(|key| key.fn_id == FnId(0))
            .collect::<Vec<_>>()
    );
}

#[test]
fn reachable_specs_do_not_seed_uninvoked_closure_targets() {
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
    let any_key = key_tys(vec![t.any()]);
    let int_key = key_tys(vec![t.int()]);
    let main_key = key_tys(vec![]);

    let mut reg = crate::frontend::spec_registry::SpecRegistry::new();
    let worker_any_sid = reg.register(&t, FnId(0), any_key.clone());
    let main_sid = reg.register(&t, FnId(1), main_key.clone());
    let worker_int_sid = reg.register(&t, FnId(0), int_key.clone());

    let mut specs = HashMap::new();
    specs.insert(value_spec_key(FnId(0), any_key), SpecPlan::default());
    specs.insert(value_spec_key(FnId(0), int_key), SpecPlan::default());
    specs.insert(value_spec_key(FnId(1), main_key), SpecPlan::default());
    let mt = ModulePlan {
        specs,
        spec_roles: HashMap::new(),
        effective_returns: HashMap::new(),
        any_key_specs: HashMap::new(),
        spec_precedence: HashMap::new(),
        fn_effects: HashMap::new(),
        dead_branches: HashMap::new(),
    };

    let reachable = reachable_specs(&mut t, &m, &reg, &mt, []);
    assert!(
        !reachable.contains(&worker_any_sid.0),
        "uninvoked closure target any-key spec should not be reachable; main_sid={:?}, reached={:?}",
        main_sid,
        reachable
    );
    assert!(
        !reachable.contains(&worker_int_sid.0),
        "uninvoked closure target narrow spec should not be reachable; main_sid={:?}, reached={:?}",
        main_sid,
        reachable
    );
}

#[test]
fn planned_program_materialization_reports_executable_body_folds() {
    use crate::telemetry::Value;

    let src = "fn check(x :: integer) do :is_int end\n\
               fn check(x) do :other end\n\
               fn main(), do: dbg(check(42))\n";
    let m = lower_src_for_plan(src);
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let cap = crate::telemetry::Capture::new();
    tel.attach(&["fz", "planner"], cap.handler());
    let mut t = crate::types::ConcreteTypes;
    let module_plan = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    let planned_program = materialize_program(&mut t, &m, &module_plan, &tel);

    let ev = cap
        .last(&["fz", "planner", "materialized"])
        .expect("planned-program materialization event");
    assert!(matches!(
        ev.metadata.get("role"),
        Some(Value::Str(role)) if role == "authoritative"
    ));
    let measurement = |name| match ev.measurements.get(name) {
        Some(Value::U64(n)) => *n,
        other => panic!("{name} missing or wrong type: {other:?}"),
    };
    let spec_slot_count = measurement("spec_slot_count");
    let planned_body_count = measurement("planned_body_count");
    let folded_prim_count = measurement("folded_prim_count");
    let folded_branch_count = measurement("folded_branch_count");
    let reachable_spec_count = measurement("reachable_spec_count");
    let reachable_specs = match ev.metadata.get("reachable_specs") {
        Some(Value::StrSeq(specs)) => specs,
        other => panic!("reachable_specs missing or wrong type: {other:?}"),
    };
    assert!(
        planned_body_count > 0,
        "materialization must own executable planned bodies"
    );
    assert!(
        spec_slot_count >= planned_body_count,
        "reserved SpecId slots are slot metadata, not optional planned bodies"
    );
    assert!(
        folded_prim_count > 0,
        "materialization must report per-spec prim folds: spec_slot_count={spec_slot_count} planned_body_count={planned_body_count} folded_prim_count={folded_prim_count} folded_branch_count={folded_branch_count}"
    );
    assert!(
        folded_branch_count > 0,
        "materialization must report per-spec branch folds: spec_slot_count={spec_slot_count} planned_body_count={planned_body_count} folded_prim_count={folded_prim_count} folded_branch_count={folded_branch_count}"
    );
    assert_eq!(
        reachable_specs.len(),
        reachable_spec_count as usize,
        "materialized reachable_specs metadata must identify every counted reachable spec"
    );

    let folded_body_event = cap
        .find(&["fz", "planner", "body_materialized"])
        .into_iter()
        .find(|ev| {
            matches!(
                ev.measurements.get("folded_prim_count"),
                Some(Value::U64(n)) if *n > 0
            ) && matches!(
                ev.measurements.get("folded_branch_count"),
                Some(Value::U64(n)) if *n > 0
            )
        })
        .expect("a planned body with per-spec prim and branch folds");
    let spec_id = match folded_body_event.measurements.get("spec_id") {
        Some(Value::U64(n)) => *n as u32,
        other => panic!("spec_id missing or wrong type: {other:?}"),
    };
    let planned_body = planned_program.executable_body(crate::fz_ir::SpecId(spec_id));
    let original_body = &m.fns[planned_body.fn_idx];
    assert!(
        count_if_terminators(&planned_body.body) < count_if_terminators(original_body),
        "planned body should not retain every branch from the source-shaped body"
    );
    assert!(
        count_fold_candidate_prims(&planned_body.body) < count_fold_candidate_prims(original_body),
        "planned body should not retain every singleton-foldable prim from the source-shaped body"
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
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);

    let main_any = module_plan_spec_ty(&mt, FnId(1), &[]);
    assert!(
        main_any.is_some(),
        "main (entry-point) must keep its any-key"
    );

    let add1_any = module_plan_spec_ty(&mt, FnId(0), &[t.any()]);
    assert!(
        add1_any.is_none(),
        "add1's any-key is dead (only caller passes int_lit(41)) → dropped"
    );
    let add1_narrow = module_plan_spec_ty(&mt, FnId(0), &[t.int_lit(41)]);
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
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);

    // The callsite passes `int_lit(41)`, which is a subtype of int. The
    // spec key carries exactly that type.
    let int41 = t.int_lit(41);
    let narrow = module_plan_spec_ty(&mt, FnId(0), std::slice::from_ref(&int41));
    assert!(
        narrow.is_some(),
        "add1 must have a specialization keyed on [int_lit(41)]; \
         specs keys present: {:?}",
        mt.specs.keys().filter(|key| key.fn_id == FnId(0)).count()
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
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);

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
) -> (crate::types::ConcreteTypes, Module, ModulePlan) {
    let toks = crate::parser::lexer::Lexer::new(src)
        .tokenize()
        .expect("lex");
    let prog = crate::parser::Parser::new(toks)
        .parse_program()
        .expect("parse");
    let mut t = crate::types::ConcreteTypes;
    let prog = crate::frontend::resolve::flatten_modules(&mut t, prog).expect("flatten");
    let ir = crate::ir_lower::lower_program(&mut t, &prog, &crate::telemetry::NullTelemetry)
        .expect("lower");
    let mt = plan_module(&mut t, &ir, tel);
    (t, ir, mt)
}

fn frontend_module(src: &str) -> Module {
    crate::test_support::lower_frontend_module(src)
}

fn frontend_plan(
    src: &str,
    tel: &dyn crate::telemetry::Telemetry,
) -> (crate::types::ConcreteTypes, Module, ModulePlan) {
    let mut t = crate::types::ConcreteTypes;
    let module = frontend_module(src);
    let plan = plan_module(&mut t, &module, tel);
    (t, module, plan)
}

#[test]
fn normalize_result_correspondence_key_widens_result_linked_state() {
    let src = r#"
@spec reducer(integer, integer) :: {:cont, integer}
fn reducer(_entry, acc), do: {:cont, acc}

@spec reduce_step([a], {:cont, b} | {:halt, b} | {:suspend, b}, (a, b) -> {:cont, b} | {:halt, b} | {:suspend, b}) :: {:done, b} | {:halted, b} | {:suspended, b, () -> any}
fn reduce_step(_list, {:cont, acc}, _reducer), do: {:done, acc}
fn reduce_step(_list, {:halt, acc}, _reducer), do: {:halted, acc}
fn reduce_step(_list, {:suspend, acc}, _reducer), do: {:suspended, acc, (fn () -> 0 end)}
"#;
    let (mut t, m, _mt) = pipeline(src, &crate::telemetry::NullTelemetry);
    let reduce_step = m.fn_by_name("reduce_step").expect("reduce_step fn");
    let reducer = m.fn_by_name("reducer").expect("reducer fn");
    let reducer_lit = t.closure_lit(reducer.id.into(), vec![], 2);
    let cont = t.atom_lit("cont");
    let halt = t.atom_lit("halt");
    let suspend = t.atom_lit("suspend");
    let acc = t.int_lit(1);
    let cont_state = t.tuple(&[cont.clone(), acc.clone()]);
    let halt_state = t.tuple(&[halt, acc.clone()]);
    let suspend_state = t.tuple(&[suspend, acc.clone()]);
    let cont_or_halt = t.union(cont_state, halt_state);
    let state = t.union(cont_or_halt, suspend_state);
    let int_ty = t.int();
    let list_int = t.list(int_ty);
    let key = super::fn_types::normalize_result_correspondence_key(
        &mut t,
        &m,
        reduce_step.id,
        vec![list_int, state.clone(), reducer_lit.clone()],
    );
    assert!(
        !t.is_equivalent(&key[1], &state),
        "state slot should widen under result-linked correspondence"
    );
    let clauses = t
        .callable_clauses(&key[2])
        .expect("normalized reducer should remain callable");
    assert_eq!(clauses.len(), 1);
    assert!(
        clauses[0].closure.is_some(),
        "recursive spec-key widening preserves closure identity; erasure is a separate type operation: {}",
        t.display(&key[2])
    );
}

#[test]
fn declared_reduce_while_return_uses_closure_return_witness() {
    let mut t = crate::types::ConcreteTypes;
    let entry_var = t.type_var(crate::types::TypeVarId(0));
    let acc_var = t.type_var(crate::types::TypeVarId(1));
    let cont = t.atom_lit("cont");
    let halt = t.atom_lit("halt");
    let reducer_ret = {
        let cont_tuple = t.tuple(&[cont, acc_var.clone()]);
        let halt_tuple = t.tuple(&[halt, acc_var.clone()]);
        t.union(cont_tuple, halt_tuple)
    };
    let enumerable_param = t.list(entry_var.clone());
    let reducer_param = t.arrow(&[entry_var, acc_var.clone()], reducer_ret);
    let reduce_spec = crate::specs::ResolvedSpec {
        params: vec![enumerable_param, acc_var.clone(), reducer_param],
        param_shapes: vec![
            crate::specs::ResolvedTypeShape::List(Box::new(crate::specs::ResolvedTypeShape::Var(
                crate::types::TypeVarId(0),
            ))),
            crate::specs::ResolvedTypeShape::Var(crate::types::TypeVarId(1)),
            crate::specs::ResolvedTypeShape::Arrow {
                params: vec![
                    crate::specs::ResolvedTypeShape::Var(crate::types::TypeVarId(0)),
                    crate::specs::ResolvedTypeShape::Var(crate::types::TypeVarId(1)),
                ],
                result: Box::new(crate::specs::ResolvedTypeShape::Union(vec![
                    crate::specs::ResolvedTypeShape::Tuple(vec![
                        crate::specs::ResolvedTypeShape::AtomLit("cont".to_string()),
                        crate::specs::ResolvedTypeShape::Var(crate::types::TypeVarId(1)),
                    ]),
                    crate::specs::ResolvedTypeShape::Tuple(vec![
                        crate::specs::ResolvedTypeShape::AtomLit("halt".to_string()),
                        crate::specs::ResolvedTypeShape::Var(crate::types::TypeVarId(1)),
                    ]),
                ])),
            },
        ],
        result: acc_var,
        result_shape: crate::specs::ResolvedTypeShape::Var(crate::types::TypeVarId(1)),
        constraints: HashMap::new(),
    };

    let reduce_id = FnId(1);
    let lambda_id = FnId(9);
    let mut reduce = FnBuilder::new(reduce_id, "reduce_while");
    let reduce_entry = reduce.block(vec![]);
    reduce.set_terminator(reduce_entry, Term::Return(Var(999)));
    let mut lambda = FnBuilder::new(lambda_id, "lambda");
    let lambda_entry = lambda.block(vec![Var(0), Var(1)]);
    lambda.set_terminator(lambda_entry, Term::Return(Var(1)));
    let mut m = build_module(vec![reduce.build(), lambda.build()]);
    m.declared_specs.insert(
        reduce_id,
        crate::specs::ResolvedSpecSet {
            arrows: vec![reduce_spec],
        },
    );

    let not_found = t.atom_lit("not_found");
    let found = t.atom_lit("found");
    let initial_acc = {
        let zero = t.int_lit(0);
        t.tuple(&[not_found.clone(), zero])
    };
    let list_int = {
        let int = t.int();
        t.list(int)
    };
    let reducer = t.closure_lit(lambda_id.into(), Vec::new(), 2);
    let arg_tys = vec![list_int, initial_acc.clone(), reducer];

    let reducer_return = {
        let int = t.int();
        let not_found_int = t.tuple(&[not_found, int.clone()]);
        let found_int = t.tuple(&[found.clone(), int]);
        let cont_tuple = {
            let cont = t.atom_lit("cont");
            t.tuple(&[cont, not_found_int])
        };
        let halt_tuple = {
            let halt = t.atom_lit("halt");
            t.tuple(&[halt, found_int])
        };
        t.union(cont_tuple, halt_tuple)
    };
    let lambda_key = SpecKey {
        fn_id: lambda_id,
        input: crate::types::key_slots_from_tys(vec![t.int(), initial_acc]),
        demand: super::fn_types::ReturnDemand::tuple_fields(2),
    };
    let effective_returns = HashMap::from([(lambda_key, reducer_return)]);
    let fact = declared_return_fact_for_test(
        &mut t,
        &m,
        reduce_id,
        reduce_id,
        &arg_tys,
        &effective_returns,
        None,
    )
    .expect("declared return fact");

    let int = t.int();
    let found_int = t.tuple(&[found, int]);
    assert!(
        t.is_subtype(&found_int, &fact.ty),
        "reduce_while declared result should include reducer halt payload, got {}",
        t.display(&fact.ty)
    );
}

#[test]
fn empty_list_call_only_reaches_empty_clause() {
    let (t, m, mt) = pipeline(
        r#"
fn classify([]), do: :empty
fn classify([_ | _]), do: :cons

fn main() do
  dbg(classify([]))
end
"#,
        &crate::telemetry::NullTelemetry,
    );
    let classify = m.fn_by_name("classify").expect("classify");
    let found = mt
        .effective_returns
        .iter()
        .find(|(key, _)| {
            key.fn_id == classify.id && crate::types::display_key_slots(&t, &key.input) == "[[]]"
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
  dbg(a)
  dbg(b)
end
"#,
        &crate::telemetry::NullTelemetry,
    );
    let ignore = m.fn_by_name("ignore").expect("ignore fn");
    assert_eq!(ignore.ignored_entry_params, vec![true, false]);

    let keys: Vec<_> = mt
        .specs
        .keys()
        .filter(|key| key.fn_id == ignore.id)
        .map(|key| key.input.clone())
        .collect();
    assert_eq!(
        keys.len(),
        1,
        "ignored arg variation should not fork specs: {keys:?}"
    );
    assert!(keys[0][0].is_none());
    assert!(keys[0][1].is_some());
}

/// fz-rh5.4 — pin upper bounds on deterministic planner-work counters.
/// Bounds are deliberately generous (~2× current observed); failures
/// force the question "is this regression or improvement?" rather
/// than reflex-bless. Tighten in the same commit that lands an
/// intentional improvement.
fn observe_planner_work(src: &str) -> (usize, usize, usize, usize) {
    use crate::telemetry::{Capture, ConfiguredTelemetry};
    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());
    let _ = pipeline(src, &tel);
    let ev = cap
        .last(&["fz", "planner", "planned"])
        .expect("fz.planner.planned event not emitted");
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
fn planner_planned_reports_activation_return_kernel_telemetry() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let _ = frontend_plan("fn id(x), do: x\nfn main(), do: id(1)", &tel);

    let ev = cap
        .last(&["fz", "planner", "planned"])
        .expect("fz.planner.planned event not emitted");
    assert!(matches!(
        ev.metadata.get("type_kernel"),
        Some(Value::Str(kernel)) if kernel == "activation"
    ));

    let measurement = |name| match ev.measurements.get(name) {
        Some(Value::U64(n)) => *n,
        other => panic!("{name} missing or wrong type: {other:?}"),
    };
    assert!(measurement("activation_return_fact_count") > 0);
    assert!(measurement("activation_return_key_count") > 0);
    assert!(measurement("activation_return_complete_entry_count") > 0);
    assert_eq!(measurement("activation_return_unresolved_entry_count"), 0);
    assert_eq!(measurement("activation_return_invalid_entry_count"), 0);
    let spec_count = measurement("spec_count");
    measurement("activation_return_known_count");
    measurement("activation_return_unresolved_count");
    measurement("activation_return_no_return_count");
    assert_eq!(measurement("activation_return_projected_count"), spec_count);
    assert_eq!(measurement("activation_return_projection_gap_count"), 0);
}

#[test]
fn planner_emits_activation_projection_telemetry_for_visible_specs() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let _ = frontend_plan(
        "fn choose(x), do: if true do x else 0 end\nfn main(), do: choose(1)",
        &tel,
    );

    let projection_events = cap.find(&["fz", "planner", "activation_projection"]);
    assert!(
        !projection_events.is_empty(),
        "planner must publish activation projection facts per visible spec"
    );

    let choose_events: Vec<_> = projection_events
        .iter()
        .filter(|event| {
            matches!(
                event.metadata.get("body_name"),
                Some(Value::Str(name)) if name == "choose"
            )
        })
        .collect();
    assert!(
        !choose_events.is_empty(),
        "expected at least one choose activation projection event"
    );
    let choose_event = choose_events
        .into_iter()
        .find(|event| {
            matches!(
                event.measurements.get("projected_dead_arm_count"),
                Some(Value::U64(1))
            )
        })
        .expect("choose activation projection event with a surfaced dead arm");

    let measurement = |name| match choose_event.measurements.get(name) {
        Some(Value::U64(n)) => *n,
        other => panic!("{name} missing or wrong type: {other:?}"),
    };
    assert_eq!(measurement("covered_activation_count"), 1);
    assert_eq!(measurement("covered_known_count"), 1);
    assert_eq!(measurement("exact_coverage"), 1);
    assert_eq!(measurement("projection_gap"), 0);
    assert_eq!(measurement("projected_dead_arm_count"), 1);

    assert!(matches!(
        choose_event.metadata.get("projection_kind"),
        Some(Value::Str(kind)) if kind == "exact"
    ));
    assert!(matches!(
        choose_event.metadata.get("projected_return_state"),
        Some(Value::Str(state)) if state.starts_with("known(")
    ));
    let covered_activations = match choose_event.metadata.get("covered_activations") {
        Some(Value::StrSeq(values)) => values,
        other => panic!("covered_activations missing or wrong type: {other:?}"),
    };
    assert_eq!(covered_activations.len(), 1);
    assert!(
        covered_activations[0].contains("choose"),
        "covered activation inventory should name the observed activation: {covered_activations:?}"
    );
    let projected_dead_arms = match choose_event.metadata.get("projected_dead_arms") {
        Some(Value::StrSeq(values)) => values,
        other => panic!("projected_dead_arms missing or wrong type: {other:?}"),
    };
    assert_eq!(
        projected_dead_arms.as_ref(),
        &["choose#b0:else".to_string()],
        "projection must surface observed dead matcher arms"
    );
}

#[test]
fn planner_projects_polymorphic_direct_call_activations_per_visible_spec() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let _ = frontend_plan(include_str!("../type_infer/fixtures/poly_id.fz"), &tel);

    let id_events: Vec<_> = cap
        .find(&["fz", "planner", "activation_projection"])
        .into_iter()
        .filter(|event| {
            matches!(
                event.metadata.get("body_name"),
                Some(Value::Str(name)) if name == "id"
            )
        })
        .collect();
    assert_eq!(
        id_events.len(),
        2,
        "poly_id should publish one visible id projection per concrete activation: {id_events:?}"
    );

    let mut projected_returns = Vec::new();
    for event in &id_events {
        let measurement = |name| match event.measurements.get(name) {
            Some(Value::U64(n)) => *n,
            other => panic!("{name} missing or wrong type: {other:?}"),
        };
        assert_eq!(measurement("covered_activation_count"), 1);
        assert_eq!(measurement("covered_known_count"), 1);
        assert_eq!(measurement("exact_coverage"), 1);
        assert_eq!(measurement("projection_gap"), 0);
        assert!(matches!(
            event.metadata.get("projection_kind"),
            Some(Value::Str(kind)) if kind == "exact"
        ));
        let projected = match event.metadata.get("projected_return_state") {
            Some(Value::Str(state)) => state.to_string(),
            other => panic!("projected_return_state missing or wrong type: {other:?}"),
        };
        projected_returns.push(projected);
    }
    projected_returns.sort();
    assert_eq!(
        projected_returns,
        vec!["known(:ok)".to_string(), "known(int)".to_string()],
        "id projections should preserve independent polymorphic returns"
    );
}

#[test]
fn planner_projects_polymorphic_named_ref_activations_per_visible_spec() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let _ = frontend_plan(
        include_str!("../type_infer/fixtures/poly_named_ref.fz"),
        &tel,
    );

    let id_events: Vec<_> = cap
        .find(&["fz", "planner", "activation_projection"])
        .into_iter()
        .filter(|event| {
            matches!(
                event.metadata.get("body_name"),
                Some(Value::Str(name)) if name == "id"
            )
        })
        .collect();
    let id_activation_events: Vec<_> = id_events
        .iter()
        .filter(|event| {
            matches!(
                event.metadata.get("spec_role"),
                Some(Value::Str(role)) if role == "activation"
            )
        })
        .collect();
    assert_eq!(
        id_activation_events.len(),
        2,
        "&id/1 should publish two activation projections plus, at most, a residual projection gap: {id_events:?}"
    );

    let mut projected_returns = Vec::new();
    for event in &id_activation_events {
        let spec_role = match event.metadata.get("spec_role") {
            Some(Value::Str(role)) => role.as_ref(),
            other => panic!("spec_role missing or wrong type: {other:?}"),
        };
        assert_eq!(
            spec_role, "activation",
            "id projections should be activation-covered"
        );
        let measurement = |name| match event.measurements.get(name) {
            Some(Value::U64(n)) => *n,
            other => panic!("{name} missing or wrong type: {other:?}"),
        };
        assert_eq!(measurement("covered_activation_count"), 1);
        assert_eq!(measurement("covered_known_count"), 1);
        assert_eq!(measurement("exact_coverage"), 1);
        assert_eq!(measurement("projection_gap"), 0);
        assert!(matches!(
            event.metadata.get("projection_kind"),
            Some(Value::Str(kind)) if kind == "exact"
        ));
        let projected = match event.metadata.get("projected_return_state") {
            Some(Value::Str(state)) => state.to_string(),
            other => panic!("projected_return_state missing or wrong type: {other:?}"),
        };
        projected_returns.push(projected);
    }
    projected_returns.sort();
    assert_eq!(
        projected_returns,
        vec!["known(:ok)".to_string(), "known(int)".to_string()],
        "named ref projections should preserve independent polymorphic returns"
    );
}

#[test]
fn compile_elides_named_ref_callable_fallback_when_calls_are_fully_resolved() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let mut t = crate::types::ConcreteTypes;
    let module = crate::test_support::lower_frontend_module(include_str!(
        "../type_infer/fixtures/poly_named_ref.fz"
    ));
    let _ = crate::ir_codegen::compile(&mut t, &module, &tel).expect("compile");

    let id_events: Vec<_> = cap
        .find(&["fz", "planner", "activation_projection"])
        .into_iter()
        .filter(|event| {
            matches!(
                event.metadata.get("body_name"),
                Some(Value::Str(name)) if name == "id"
            ) && matches!(
                event.metadata.get("role"),
                Some(Value::Str(role)) if role == "authoritative"
            )
        })
        .collect();

    assert!(
        id_events.iter().all(|event| {
            !matches!(
                event.metadata.get("spec_role"),
                Some(Value::Str(role)) if role == "callable_fallback"
            )
        }),
        "compile-time planner should not retain a callable fallback for a fully-resolved named ref: {id_events:?}"
    );
}

#[test]
fn planner_projects_captured_closure_activations_without_callable_fallback() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let _ = frontend_plan(
        include_str!("../type_infer/fixtures/poly_capture_ref.fz"),
        &tel,
    );

    let lambda_events: Vec<_> = cap
        .find(&["fz", "planner", "activation_projection"])
        .into_iter()
        .filter(|event| {
            matches!(
                event.metadata.get("body_name"),
                Some(Value::Str(name)) if name.starts_with("lambda_")
            )
        })
        .collect();
    let lambda_activation_events: Vec<_> = lambda_events
        .iter()
        .filter(|event| {
            matches!(
                event.metadata.get("spec_role"),
                Some(Value::Str(role)) if role == "activation"
            )
        })
        .collect();
    assert_eq!(
        lambda_activation_events.len(),
        2,
        "captured closure should publish two activation projections plus, at most, a residual projection gap: {lambda_events:?}"
    );

    let mut projected_returns = Vec::new();
    for event in &lambda_activation_events {
        let spec_role = match event.metadata.get("spec_role") {
            Some(Value::Str(role)) => role.as_ref(),
            other => panic!("spec_role missing or wrong type: {other:?}"),
        };
        assert_eq!(
            spec_role, "activation",
            "lambda projections should be activation-covered"
        );
        let measurement = |name| match event.measurements.get(name) {
            Some(Value::U64(n)) => *n,
            other => panic!("{name} missing or wrong type: {other:?}"),
        };
        assert_eq!(measurement("covered_activation_count"), 1);
        assert_eq!(measurement("covered_known_count"), 1);
        assert_eq!(measurement("exact_coverage"), 1);
        assert_eq!(measurement("projection_gap"), 0);
        assert!(matches!(
            event.metadata.get("projection_kind"),
            Some(Value::Str(kind)) if kind == "exact"
        ));
        let projected = match event.metadata.get("projected_return_state") {
            Some(Value::Str(state)) => state.to_string(),
            other => panic!("projected_return_state missing or wrong type: {other:?}"),
        };
        projected_returns.push(projected);
    }
    projected_returns.sort();
    assert_eq!(
        projected_returns,
        vec![
            "known({:ok, :right})".to_string(),
            "known({:ok, int})".to_string()
        ],
        "captured closure projections should preserve capture and argument facts"
    );
}

#[test]
fn planner_projects_named_ref_pattern_activations_and_dead_arms() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let _ = frontend_plan(
        include_str!("../type_infer/fixtures/poly_named_ref_pattern.fz"),
        &tel,
    );

    let pick_events: Vec<_> = cap
        .find(&["fz", "planner", "activation_projection"])
        .into_iter()
        .filter(|event| {
            matches!(
                event.metadata.get("body_name"),
                Some(Value::Str(name)) if name == "pick"
            )
        })
        .collect();
    let pick_activation_events: Vec<_> = pick_events
        .iter()
        .filter(|event| {
            matches!(
                event.metadata.get("spec_role"),
                Some(Value::Str(role)) if role == "activation"
            )
        })
        .collect();
    assert_eq!(
        pick_activation_events.len(),
        2,
        "&pick/1 should publish two activation projections plus, at most, a residual projection gap: {pick_events:?}"
    );

    let mut projected_returns = Vec::new();
    for event in &pick_activation_events {
        let spec_role = match event.metadata.get("spec_role") {
            Some(Value::Str(role)) => role.as_ref(),
            other => panic!("spec_role missing or wrong type: {other:?}"),
        };
        assert_eq!(
            spec_role, "activation",
            "pick projections should be activation-covered"
        );
        let measurement = |name| match event.measurements.get(name) {
            Some(Value::U64(n)) => *n,
            other => panic!("{name} missing or wrong type: {other:?}"),
        };
        assert_eq!(measurement("covered_activation_count"), 1);
        assert_eq!(measurement("covered_known_count"), 1);
        assert_eq!(measurement("exact_coverage"), 1);
        assert_eq!(measurement("projection_gap"), 0);
        assert!(
            measurement("projected_dead_arm_count") > 0,
            "pattern activation should project dead-arm evidence: {event:?}"
        );
        assert!(matches!(
            event.metadata.get("projection_kind"),
            Some(Value::Str(kind)) if kind == "exact"
        ));
        let projected = match event.metadata.get("projected_return_state") {
            Some(Value::Str(state)) => state.to_string(),
            other => panic!("projected_return_state missing or wrong type: {other:?}"),
        };
        projected_returns.push(projected);
    }
    projected_returns.sort();
    assert_eq!(
        projected_returns,
        vec!["known(:one)".to_string(), "known(:two)".to_string()],
        "named ref pattern projections should preserve per-activation matcher returns"
    );
}

#[test]
fn planner_projects_atom_pattern_dispatch_per_activation() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let _ = frontend_plan(
        include_str!("../type_infer/fixtures/match_atom_partition.fz"),
        &tel,
    );

    let pick_events: Vec<_> = cap
        .find(&["fz", "planner", "activation_projection"])
        .into_iter()
        .filter(|event| {
            matches!(
                event.metadata.get("body_name"),
                Some(Value::Str(name)) if name == "pick"
            )
        })
        .collect();
    assert_eq!(
        pick_events.len(),
        2,
        "direct atom calls should publish one visible pick projection per activation: {pick_events:?}"
    );

    let mut projected_returns = Vec::new();
    for event in &pick_events {
        let spec_role = match event.metadata.get("spec_role") {
            Some(Value::Str(role)) => role.as_ref(),
            other => panic!("spec_role missing or wrong type: {other:?}"),
        };
        assert_eq!(
            spec_role, "activation",
            "direct atom matcher projections should be activation-covered"
        );
        let measurement = |name| match event.measurements.get(name) {
            Some(Value::U64(n)) => *n,
            other => panic!("{name} missing or wrong type: {other:?}"),
        };
        assert_eq!(measurement("covered_activation_count"), 1);
        assert_eq!(measurement("covered_known_count"), 1);
        assert_eq!(measurement("exact_coverage"), 1);
        assert_eq!(measurement("projection_gap"), 0);
        assert!(
            measurement("projected_dead_arm_count") > 0,
            "matcher proof should surface dead-arm evidence per activation: {event:?}"
        );
        assert!(matches!(
            event.metadata.get("projection_kind"),
            Some(Value::Str(kind)) if kind == "exact"
        ));
        let projected = match event.metadata.get("projected_return_state") {
            Some(Value::Str(state)) => state.to_string(),
            other => panic!("projected_return_state missing or wrong type: {other:?}"),
        };
        projected_returns.push(projected);
    }
    projected_returns.sort();
    assert_eq!(
        projected_returns,
        vec!["known(:one)".to_string(), "known(:two)".to_string()],
        "direct atom matcher projections should preserve per-activation leaves"
    );
}

#[test]
fn planner_projects_list_pattern_dispatch_per_activation() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let _ = frontend_plan(
        include_str!("../type_infer/fixtures/match_list_partition.fz"),
        &tel,
    );

    let pick_events: Vec<_> = cap
        .find(&["fz", "planner", "activation_projection"])
        .into_iter()
        .filter(|event| {
            matches!(
                event.metadata.get("body_name"),
                Some(Value::Str(name)) if name == "pick"
            )
        })
        .collect();
    assert_eq!(
        pick_events.len(),
        2,
        "direct list calls should publish one visible pick projection per activation: {pick_events:?}"
    );

    let mut projected_returns = Vec::new();
    for event in &pick_events {
        let spec_role = match event.metadata.get("spec_role") {
            Some(Value::Str(role)) => role.as_ref(),
            other => panic!("spec_role missing or wrong type: {other:?}"),
        };
        assert_eq!(
            spec_role, "activation",
            "direct list matcher projections should be activation-covered"
        );
        let measurement = |name| match event.measurements.get(name) {
            Some(Value::U64(n)) => *n,
            other => panic!("{name} missing or wrong type: {other:?}"),
        };
        assert_eq!(measurement("covered_activation_count"), 1);
        assert_eq!(measurement("covered_known_count"), 1);
        assert_eq!(measurement("exact_coverage"), 1);
        assert_eq!(measurement("projection_gap"), 0);
        assert!(
            measurement("projected_dead_arm_count") > 0,
            "list matcher proof should surface dead-arm evidence per activation: {event:?}"
        );
        assert!(matches!(
            event.metadata.get("projection_kind"),
            Some(Value::Str(kind)) if kind == "exact"
        ));
        let projected = match event.metadata.get("projected_return_state") {
            Some(Value::Str(state)) => state.to_string(),
            other => panic!("projected_return_state missing or wrong type: {other:?}"),
        };
        projected_returns.push(projected);
    }
    projected_returns.sort();
    assert_eq!(
        projected_returns,
        vec!["known(:cons)".to_string(), "known(:empty)".to_string()],
        "direct list matcher projections should preserve per-activation leaves"
    );
}

#[test]
fn planner_projects_list_pattern_binding_per_activation() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let _ = frontend_plan(
        include_str!("../type_infer/fixtures/match_list_binding.fz"),
        &tel,
    );

    let pick_events: Vec<_> = cap
        .find(&["fz", "planner", "activation_projection"])
        .into_iter()
        .filter(|event| {
            matches!(
                event.metadata.get("body_name"),
                Some(Value::Str(name)) if name == "pick"
            )
        })
        .collect();
    assert_eq!(
        pick_events.len(),
        2,
        "list binding calls should publish one visible pick projection per activation: {pick_events:?}"
    );

    let mut projected_returns = Vec::new();
    for event in &pick_events {
        let spec_role = match event.metadata.get("spec_role") {
            Some(Value::Str(role)) => role.as_ref(),
            other => panic!("spec_role missing or wrong type: {other:?}"),
        };
        assert_eq!(
            spec_role, "activation",
            "list binding projections should be activation-covered"
        );
        let measurement = |name| match event.measurements.get(name) {
            Some(Value::U64(n)) => *n,
            other => panic!("{name} missing or wrong type: {other:?}"),
        };
        assert_eq!(measurement("covered_activation_count"), 1);
        assert_eq!(measurement("covered_known_count"), 1);
        assert_eq!(measurement("exact_coverage"), 1);
        assert_eq!(measurement("projection_gap"), 0);
        assert!(
            measurement("projected_dead_arm_count") > 0,
            "list binding matcher proof should surface dead-arm evidence per activation: {event:?}"
        );
        assert!(matches!(
            event.metadata.get("projection_kind"),
            Some(Value::Str(kind)) if kind == "exact"
        ));
        let projected = match event.metadata.get("projected_return_state") {
            Some(Value::Str(state)) => state.to_string(),
            other => panic!("projected_return_state missing or wrong type: {other:?}"),
        };
        projected_returns.push(projected);
    }
    projected_returns.sort();
    assert_eq!(
        projected_returns,
        vec!["known(:empty)".to_string(), "known(int)".to_string()],
        "list binding projections should preserve empty and head-bound returns"
    );
}

#[test]
fn planner_projects_tuple_pattern_binding_per_activation() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let _ = frontend_plan(
        include_str!("../type_infer/fixtures/match_tuple_binding.fz"),
        &tel,
    );

    let pick_events: Vec<_> = cap
        .find(&["fz", "planner", "activation_projection"])
        .into_iter()
        .filter(|event| {
            matches!(
                event.metadata.get("body_name"),
                Some(Value::Str(name)) if name == "pick"
            )
        })
        .collect();
    assert_eq!(
        pick_events.len(),
        2,
        "tuple binding calls should publish one visible pick projection per activation: {pick_events:?}"
    );

    let mut projected_returns = Vec::new();
    for event in &pick_events {
        let spec_role = match event.metadata.get("spec_role") {
            Some(Value::Str(role)) => role.as_ref(),
            other => panic!("spec_role missing or wrong type: {other:?}"),
        };
        assert_eq!(
            spec_role, "activation",
            "tuple binding projections should be activation-covered"
        );
        let measurement = |name| match event.measurements.get(name) {
            Some(Value::U64(n)) => *n,
            other => panic!("{name} missing or wrong type: {other:?}"),
        };
        assert_eq!(measurement("covered_activation_count"), 1);
        assert_eq!(measurement("covered_known_count"), 1);
        assert_eq!(measurement("exact_coverage"), 1);
        assert_eq!(measurement("projection_gap"), 0);
        assert!(
            measurement("projected_dead_arm_count") > 0,
            "tuple binding matcher proof should surface dead-arm evidence per activation: {event:?}"
        );
        assert!(matches!(
            event.metadata.get("projection_kind"),
            Some(Value::Str(kind)) if kind == "exact"
        ));
        let projected = match event.metadata.get("projected_return_state") {
            Some(Value::Str(state)) => state.to_string(),
            other => panic!("projected_return_state missing or wrong type: {other:?}"),
        };
        projected_returns.push(projected);
    }
    projected_returns.sort();
    assert_eq!(
        projected_returns,
        vec!["known(:error)".to_string(), "known(int)".to_string()],
        "tuple binding projections should preserve atom and payload-bound returns"
    );
}

#[test]
fn planner_projects_nested_pattern_binding_per_activation() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let _ = frontend_plan(
        include_str!("../type_infer/fixtures/match_nested_binding.fz"),
        &tel,
    );

    let pick_events: Vec<_> = cap
        .find(&["fz", "planner", "activation_projection"])
        .into_iter()
        .filter(|event| {
            matches!(
                event.metadata.get("body_name"),
                Some(Value::Str(name)) if name == "pick"
            )
        })
        .collect();
    assert_eq!(
        pick_events.len(),
        2,
        "nested binding calls should publish one visible pick projection per activation: {pick_events:?}"
    );

    let mut projected_returns = Vec::new();
    for event in &pick_events {
        let spec_role = match event.metadata.get("spec_role") {
            Some(Value::Str(role)) => role.as_ref(),
            other => panic!("spec_role missing or wrong type: {other:?}"),
        };
        assert_eq!(
            spec_role, "activation",
            "nested binding projections should be activation-covered"
        );
        let measurement = |name| match event.measurements.get(name) {
            Some(Value::U64(n)) => *n,
            other => panic!("{name} missing or wrong type: {other:?}"),
        };
        assert_eq!(measurement("covered_activation_count"), 1);
        assert_eq!(measurement("covered_known_count"), 1);
        assert_eq!(measurement("exact_coverage"), 1);
        assert_eq!(measurement("projection_gap"), 0);
        assert!(
            measurement("projected_dead_arm_count") > 0,
            "nested binding matcher proof should surface dead-arm evidence per activation: {event:?}"
        );
        assert!(matches!(
            event.metadata.get("projection_kind"),
            Some(Value::Str(kind)) if kind == "exact"
        ));
        let projected = match event.metadata.get("projected_return_state") {
            Some(Value::Str(state)) => state.to_string(),
            other => panic!("projected_return_state missing or wrong type: {other:?}"),
        };
        projected_returns.push(projected);
    }
    projected_returns.sort();
    assert_eq!(
        projected_returns,
        vec!["known(:error)".to_string(), "known(int)".to_string()],
        "nested binding projections should preserve atom and nested payload-bound returns"
    );
}

#[test]
fn planner_projects_nested_pattern_partition_per_activation() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let _ = frontend_plan(
        include_str!("../type_infer/fixtures/match_nested_partition.fz"),
        &tel,
    );

    let pick_events: Vec<_> = cap
        .find(&["fz", "planner", "activation_projection"])
        .into_iter()
        .filter(|event| {
            matches!(
                event.metadata.get("body_name"),
                Some(Value::Str(name)) if name == "pick"
            )
        })
        .collect();
    assert_eq!(
        pick_events.len(),
        3,
        "nested partition calls should publish one visible pick projection per activation: {pick_events:?}"
    );

    let mut projected_returns = Vec::new();
    for event in &pick_events {
        let spec_role = match event.metadata.get("spec_role") {
            Some(Value::Str(role)) => role.as_ref(),
            other => panic!("spec_role missing or wrong type: {other:?}"),
        };
        assert_eq!(
            spec_role, "activation",
            "nested partition projections should be activation-covered"
        );
        let measurement = |name| match event.measurements.get(name) {
            Some(Value::U64(n)) => *n,
            other => panic!("{name} missing or wrong type: {other:?}"),
        };
        assert_eq!(measurement("covered_activation_count"), 1);
        assert_eq!(measurement("covered_known_count"), 1);
        assert_eq!(measurement("exact_coverage"), 1);
        assert_eq!(measurement("projection_gap"), 0);
        assert!(
            measurement("projected_dead_arm_count") > 0,
            "nested partition matcher proof should surface dead-arm evidence per activation: {event:?}"
        );
        assert!(matches!(
            event.metadata.get("projection_kind"),
            Some(Value::Str(kind)) if kind == "exact"
        ));
        let projected = match event.metadata.get("projected_return_state") {
            Some(Value::Str(state)) => state.to_string(),
            other => panic!("projected_return_state missing or wrong type: {other:?}"),
        };
        projected_returns.push(projected);
    }
    projected_returns.sort();
    assert_eq!(
        projected_returns,
        vec![
            "known(:empty)".to_string(),
            "known(:error)".to_string(),
            "known(int)".to_string()
        ],
        "nested partition projections should preserve all sibling matcher leaves"
    );
}

#[test]
fn planner_projects_tuple_tag_partition_per_activation() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let _ = frontend_plan(
        include_str!("../type_infer/fixtures/match_tuple_tag_partition.fz"),
        &tel,
    );

    let pick_events: Vec<_> = cap
        .find(&["fz", "planner", "activation_projection"])
        .into_iter()
        .filter(|event| {
            matches!(
                event.metadata.get("body_name"),
                Some(Value::Str(name)) if name == "pick"
            )
        })
        .collect();
    assert_eq!(
        pick_events.len(),
        2,
        "tuple tag calls should publish one visible pick projection per activation: {pick_events:?}"
    );

    let mut projected_returns = Vec::new();
    for event in &pick_events {
        let spec_role = match event.metadata.get("spec_role") {
            Some(Value::Str(role)) => role.as_ref(),
            other => panic!("spec_role missing or wrong type: {other:?}"),
        };
        assert_eq!(
            spec_role, "activation",
            "tuple tag projections should be activation-covered"
        );
        let measurement = |name| match event.measurements.get(name) {
            Some(Value::U64(n)) => *n,
            other => panic!("{name} missing or wrong type: {other:?}"),
        };
        assert_eq!(measurement("covered_activation_count"), 1);
        assert_eq!(measurement("covered_known_count"), 1);
        assert_eq!(measurement("exact_coverage"), 1);
        assert_eq!(measurement("projection_gap"), 0);
        assert!(
            measurement("projected_dead_arm_count") > 0,
            "tuple tag matcher proof should surface dead-arm evidence per activation: {event:?}"
        );
        assert!(matches!(
            event.metadata.get("projection_kind"),
            Some(Value::Str(kind)) if kind == "exact"
        ));
        let projected = match event.metadata.get("projected_return_state") {
            Some(Value::Str(state)) => state.to_string(),
            other => panic!("projected_return_state missing or wrong type: {other:?}"),
        };
        projected_returns.push(projected);
    }
    projected_returns.sort();
    assert_eq!(
        projected_returns,
        vec!["known(:bad)".to_string(), "known(int)".to_string()],
        "tuple tag projections should preserve the matching payload returns"
    );
}

#[test]
fn planner_projects_tuple_arity_partition_per_activation() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let _ = frontend_plan(
        include_str!("../type_infer/fixtures/match_tuple_arity_partition.fz"),
        &tel,
    );

    let pick_events: Vec<_> = cap
        .find(&["fz", "planner", "activation_projection"])
        .into_iter()
        .filter(|event| {
            matches!(
                event.metadata.get("body_name"),
                Some(Value::Str(name)) if name == "pick"
            )
        })
        .collect();
    assert_eq!(
        pick_events.len(),
        3,
        "tuple arity calls should publish one visible pick projection per activation: {pick_events:?}"
    );

    let mut projected_returns = Vec::new();
    for event in &pick_events {
        let spec_role = match event.metadata.get("spec_role") {
            Some(Value::Str(role)) => role.as_ref(),
            other => panic!("spec_role missing or wrong type: {other:?}"),
        };
        assert_eq!(
            spec_role, "activation",
            "tuple arity projections should be activation-covered"
        );
        let measurement = |name| match event.measurements.get(name) {
            Some(Value::U64(n)) => *n,
            other => panic!("{name} missing or wrong type: {other:?}"),
        };
        assert_eq!(measurement("covered_activation_count"), 1);
        assert_eq!(measurement("covered_known_count"), 1);
        assert_eq!(measurement("exact_coverage"), 1);
        assert_eq!(measurement("projection_gap"), 0);
        assert!(
            measurement("projected_dead_arm_count") > 0,
            "tuple arity matcher proof should surface dead-arm evidence per activation: {event:?}"
        );
        assert!(matches!(
            event.metadata.get("projection_kind"),
            Some(Value::Str(kind)) if kind == "exact"
        ));
        let projected = match event.metadata.get("projected_return_state") {
            Some(Value::Str(state)) => state.to_string(),
            other => panic!("projected_return_state missing or wrong type: {other:?}"),
        };
        projected_returns.push(projected);
    }
    projected_returns.sort();
    assert_eq!(
        projected_returns,
        vec![
            "known(:other)".to_string(),
            "known(int)".to_string(),
            "known({int, int})".to_string()
        ],
        "tuple arity projections should preserve each matching shape"
    );
}

#[test]
fn planner_projects_guard_partition_per_activation() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let _ = frontend_plan(
        include_str!("../type_infer/fixtures/match_guard_partition.fz"),
        &tel,
    );

    let pick_events: Vec<_> = cap
        .find(&["fz", "planner", "activation_projection"])
        .into_iter()
        .filter(|event| {
            matches!(
                event.metadata.get("body_name"),
                Some(Value::Str(name)) if name == "pick"
            )
        })
        .collect();
    assert_eq!(
        pick_events.len(),
        1,
        "guarded calls should collapse witness activations into one semantic pick projection: {pick_events:?}"
    );

    let event = &pick_events[0];
    let spec_role = match event.metadata.get("spec_role") {
        Some(Value::Str(role)) => role.as_ref(),
        other => panic!("spec_role missing or wrong type: {other:?}"),
    };
    assert_eq!(
        spec_role, "activation",
        "guarded projections should stay activation-covered"
    );
    let measurement = |name| match event.measurements.get(name) {
        Some(Value::U64(n)) => *n,
        other => panic!("{name} missing or wrong type: {other:?}"),
    };
    assert_eq!(measurement("covered_activation_count"), 2);
    assert_eq!(measurement("covered_known_count"), 2);
    assert_eq!(measurement("exact_coverage"), 1);
    assert_eq!(measurement("projection_gap"), 0);
    assert!(
        measurement("projected_dead_arm_count") > 0,
        "guard matcher proof should preserve shared dead-arm evidence on the semantic spec: {event:?}"
    );
    assert!(matches!(
        event.metadata.get("projection_kind"),
        Some(Value::Str(kind)) if kind == "exact"
    ));
    assert!(matches!(
        event.metadata.get("projected_return_state"),
        Some(Value::Str(state)) if state == "known(int | :fallback)"
    ));
    let covered_activations = match event.metadata.get("covered_activations") {
        Some(Value::StrSeq(values)) => values,
        other => panic!("covered_activations missing or wrong type: {other:?}"),
    };
    assert_eq!(
        covered_activations.len(),
        2,
        "semantic guard projection should inventory both witness activations"
    );
    assert!(
        covered_activations
            .iter()
            .any(|entry| entry.contains("=> known(int)")),
        "expected refined witness return in the covered activation inventory: {covered_activations:?}"
    );
    assert!(
        covered_activations
            .iter()
            .any(|entry| entry.contains("=> known(:fallback)")),
        "expected fallback witness return in the covered activation inventory: {covered_activations:?}"
    );
}

#[test]
fn planner_projects_map_pattern_binding_per_activation() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let _ = frontend_plan(
        include_str!("../type_infer/fixtures/match_map_binding.fz"),
        &tel,
    );

    let pick_events: Vec<_> = cap
        .find(&["fz", "planner", "activation_projection"])
        .into_iter()
        .filter(|event| {
            matches!(
                event.metadata.get("body_name"),
                Some(Value::Str(name)) if name == "pick"
            )
        })
        .collect();
    assert_eq!(
        pick_events.len(),
        2,
        "map binding fixture should publish one visible pick projection per reachable semantic input: {pick_events:?}"
    );

    let mut projected_returns = Vec::new();
    for event in &pick_events {
        let spec_role = match event.metadata.get("spec_role") {
            Some(Value::Str(role)) => role.as_ref(),
            other => panic!("spec_role missing or wrong type: {other:?}"),
        };
        assert_eq!(
            spec_role, "activation",
            "map binding projections should be activation-covered"
        );
        let measurement = |name| match event.measurements.get(name) {
            Some(Value::U64(n)) => *n,
            other => panic!("{name} missing or wrong type: {other:?}"),
        };
        assert_eq!(measurement("covered_activation_count"), 1);
        assert_eq!(measurement("covered_known_count"), 1);
        assert_eq!(measurement("exact_coverage"), 1);
        assert_eq!(measurement("projection_gap"), 0);
        assert!(
            measurement("projected_dead_arm_count") > 0,
            "map binding matcher proof should surface dead-arm evidence per activation: {event:?}"
        );
        assert!(matches!(
            event.metadata.get("projection_kind"),
            Some(Value::Str(kind)) if kind == "exact"
        ));
        let projected = match event.metadata.get("projected_return_state") {
            Some(Value::Str(state)) => state.to_string(),
            other => panic!("projected_return_state missing or wrong type: {other:?}"),
        };
        projected_returns.push(projected);
    }
    projected_returns.sort();
    assert_eq!(
        projected_returns,
        vec!["known(:none)".to_string(), "known(int)".to_string()],
        "map binding projections should preserve the map-hit payload and the explicit atom arm"
    );
}

#[test]
fn planner_projects_fold_tail_entry_with_known_int_return() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let _ = frontend_plan(include_str!("../type_infer/fixtures/fold_tail.fz"), &tel);

    let myreduce_events: Vec<_> = cap
        .find(&["fz", "planner", "activation_projection"])
        .into_iter()
        .filter(|event| {
            matches!(
                event.metadata.get("body_name"),
                Some(Value::Str(name)) if name == "myreduce"
            )
        })
        .collect();
    assert_eq!(
        myreduce_events.len(),
        1,
        "tail fold should produce one reachable semantic projection for myreduce: {myreduce_events:?}"
    );

    let event = &myreduce_events[0];
    let measurement = |name| match event.measurements.get(name) {
        Some(Value::U64(n)) => *n,
        other => panic!("{name} missing or wrong type: {other:?}"),
    };
    assert_eq!(measurement("covered_activation_count"), 1);
    assert_eq!(measurement("covered_known_count"), 1);
    assert_eq!(measurement("exact_coverage"), 1);
    assert_eq!(measurement("projection_gap"), 0);
    assert!(matches!(
        event.metadata.get("projected_return_state"),
        Some(Value::Str(state)) if state == "known(int)"
    ));
}

#[test]
fn planner_projects_enum_reduce_runtime_graph_from_activation_facts() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let mut t = crate::types::ConcreteTypes;
    let module = crate::test_support::linked_runtime_module(include_str!(
        "../type_infer/fixtures/enum_reduce.fz"
    ));
    let _ = plan_module(&mut t, &module, &tel);

    let events = cap
        .find(&["fz", "planner", "activation_projection"])
        .into_iter()
        .filter(|event| {
            matches!(
                event.metadata.get("body_name"),
                Some(Value::Str(name)) if name == "Enum.reduce" || name == "Enumerable.List.reduce"
            )
        })
        .collect::<Vec<_>>();
    assert!(
        !events.is_empty(),
        "linked Enum.reduce graph should publish projection facts for runtime reducers"
    );

    let mut enum_reduce_known_int = false;
    let mut list_reduce_known_done_int = false;
    for event in &events {
        let body_name = match event.metadata.get("body_name") {
            Some(Value::Str(name)) => name.as_ref(),
            other => panic!("body_name missing or wrong type: {other:?}"),
        };
        let spec_role = match event.metadata.get("spec_role") {
            Some(Value::Str(role)) => role.as_ref(),
            other => panic!("spec_role missing or wrong type: {other:?}"),
        };
        if spec_role != "activation" {
            continue;
        }
        let measurement = |name| match event.measurements.get(name) {
            Some(Value::U64(n)) => *n,
            other => panic!("{name} missing or wrong type: {other:?}"),
        };
        assert_eq!(measurement("covered_activation_count"), 1);
        assert_eq!(measurement("covered_known_count"), 1);
        assert_eq!(measurement("exact_coverage"), 1);
        assert_eq!(measurement("projection_gap"), 0);
        assert!(matches!(
            event.metadata.get("projection_kind"),
            Some(Value::Str(kind)) if kind == "exact"
        ));
        let projected = match event.metadata.get("projected_return_state") {
            Some(Value::Str(state)) => state.as_ref(),
            other => panic!("projected_return_state missing or wrong type: {other:?}"),
        };
        if body_name == "Enum.reduce" && projected == "known(int)" {
            enum_reduce_known_int = true;
        }
        if body_name == "Enumerable.List.reduce" && projected == "known({:done, int})" {
            list_reduce_known_done_int = true;
        }
    }

    assert!(
        enum_reduce_known_int,
        "Enum.reduce should have an activation-covered known int projection: {events:?}"
    );
    assert!(
        list_reduce_known_done_int,
        "Enumerable.List.reduce should have an activation-covered {{:done, int}} projection: {events:?}"
    );
}

#[test]
fn planner_projects_enum_reduce_operator_refs_through_kernel_specs() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let mut t = crate::types::ConcreteTypes;
    let graph = crate::test_support::linked_runtime_graph_with_telemetry(
        &mut t,
        include_str!("../type_infer/fixtures/enum_reduce_operator_ref.fz"),
        &tel,
    );
    let runtime_body_ids = graph
        .module
        .fns
        .iter()
        .filter(|f| {
            f.name == "main"
                || f.name == "Enum.reduce"
                || f.name == "Enumerable.List.reduce"
                || f.name == "Kernel.+"
        })
        .map(|f| f.id.0)
        .collect::<std::collections::HashSet<_>>();
    let _ = crate::ir_codegen::compile_planned(&mut t, &graph.module, &graph.module_plan, &tel)
        .expect("compile");

    let events = cap
        .find(&["fz", "planner", "activation_projection"])
        .into_iter()
        .filter(|event| {
            matches!(
                event.metadata.get("body_fn_id"),
                Some(Value::U64(fn_id)) if runtime_body_ids.contains(&(*fn_id as u32))
            ) && matches!(
                event.metadata.get("role"),
                Some(Value::Str(role)) if role == "authoritative"
            )
        })
        .collect::<Vec<_>>();
    assert!(
        !events.is_empty(),
        "operator-ref Enum.reduce graph should publish projection facts for the entry, wrappers, and reducer target"
    );

    let mut main_known_tuple = false;
    let mut enum_reduce_known_int = false;
    let mut list_reduce_known_done_int = false;
    let mut kernel_plus_known_int = false;

    for event in &events {
        let body_name = match event.metadata.get("body_name") {
            Some(Value::Str(name)) => name.as_ref(),
            other => panic!("body_name missing or wrong type: {other:?}"),
        };
        let spec_role = match event.metadata.get("spec_role") {
            Some(Value::Str(role)) => role.as_ref(),
            other => panic!("spec_role missing or wrong type: {other:?}"),
        };
        if spec_role == "callable_fallback" {
            panic!(
                "authoritative compile-time planner should not retain a callable fallback for the operator-ref reducer: {event:?}"
            );
        }
        if spec_role != "activation" && spec_role != "entry" {
            continue;
        }
        let measurement = |name| match event.measurements.get(name) {
            Some(Value::U64(n)) => *n,
            other => panic!("{name} missing or wrong type: {other:?}"),
        };
        if spec_role == "activation" {
            assert_eq!(
                measurement("covered_known_count"),
                measurement("covered_activation_count")
            );
            assert_eq!(measurement("exact_coverage"), 1);
            assert_eq!(measurement("projection_gap"), 0);
        }
        assert!(matches!(
            event.metadata.get("projection_kind"),
            Some(Value::Str(kind)) if kind == "exact"
        ));
        let projected = match event.metadata.get("projected_return_state") {
            Some(Value::Str(state)) => state.as_ref(),
            other => panic!("projected_return_state missing or wrong type: {other:?}"),
        };
        if body_name == "main" && projected == "known({int, int})" {
            main_known_tuple = true;
        }
        if body_name == "Enum.reduce" && projected == "known(int)" {
            enum_reduce_known_int = true;
        }
        if body_name == "Enumerable.List.reduce" && projected == "known({:done, int})" {
            list_reduce_known_done_int = true;
        }
        if body_name == "Kernel.+" && projected == "known(int)" {
            kernel_plus_known_int = true;
        }
    }

    assert!(
        main_known_tuple,
        "main should project the tuple of both reduced ints: {events:?}"
    );
    assert!(
        enum_reduce_known_int,
        "Enum.reduce should have an activation-covered known int projection in the operator-ref fixture: {events:?}"
    );
    assert!(
        list_reduce_known_done_int,
        "Enumerable.List.reduce should project {{:done, int}} for the operator-ref fixture: {events:?}"
    );
    assert!(
        kernel_plus_known_int,
        "Kernel.+ should survive only as the exact int reducer target in the operator-ref fixture: {events:?}"
    );
}

#[test]
fn planner_projects_enum_reduce_range_runtime_graph_from_activation_facts() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let mut t = crate::types::ConcreteTypes;
    let module = crate::test_support::linked_runtime_module(include_str!(
        "../type_infer/fixtures/enum_reduce_range.fz"
    ));
    let _ = plan_module(&mut t, &module, &tel);

    let events = cap
        .find(&["fz", "planner", "activation_projection"])
        .into_iter()
        .filter(|event| {
            matches!(
                event.metadata.get("body_name"),
                Some(Value::Str(name)) if name == "Enum.reduce" || name == "Enumerable.Range.reduce"
            )
        })
        .collect::<Vec<_>>();
    assert!(
        !events.is_empty(),
        "linked Enum.reduce range graph should publish projection facts for runtime reducers"
    );

    let mut enum_reduce_known_int = false;
    let mut range_reduce_known_done_int = false;
    for event in &events {
        let body_name = match event.metadata.get("body_name") {
            Some(Value::Str(name)) => name.as_ref(),
            other => panic!("body_name missing or wrong type: {other:?}"),
        };
        let spec_role = match event.metadata.get("spec_role") {
            Some(Value::Str(role)) => role.as_ref(),
            other => panic!("spec_role missing or wrong type: {other:?}"),
        };
        if spec_role != "activation" {
            continue;
        }
        let measurement = |name| match event.measurements.get(name) {
            Some(Value::U64(n)) => *n,
            other => panic!("{name} missing or wrong type: {other:?}"),
        };
        assert_eq!(measurement("covered_activation_count"), 1);
        assert_eq!(measurement("covered_known_count"), 1);
        assert_eq!(measurement("exact_coverage"), 1);
        assert_eq!(measurement("projection_gap"), 0);
        assert!(matches!(
            event.metadata.get("projection_kind"),
            Some(Value::Str(kind)) if kind == "exact"
        ));
        let projected = match event.metadata.get("projected_return_state") {
            Some(Value::Str(state)) => state.as_ref(),
            other => panic!("projected_return_state missing or wrong type: {other:?}"),
        };
        if body_name == "Enum.reduce" && projected == "known(int)" {
            enum_reduce_known_int = true;
        }
        if body_name == "Enumerable.Range.reduce" && projected == "known({:done, int})" {
            range_reduce_known_done_int = true;
        }
    }

    assert!(
        enum_reduce_known_int,
        "Enum.reduce over Range should have an activation-covered known int projection: {events:?}"
    );
    assert!(
        range_reduce_known_done_int,
        "Enumerable.Range.reduce should have an activation-covered {{:done, int}} projection: {events:?}"
    );
}

#[test]
fn planner_projects_plain_spawn_child_through_callable_boundary() {
    let signals = crate::test_support::runtime_graph_planner_activation_projection_signals(
        include_str!("../type_infer/fixtures/spawn_plain.fz"),
    );

    let child = signals
        .iter()
        .find(|signal| signal.body_name == "child")
        .unwrap_or_else(|| panic!("expected child activation projection event: {signals:?}"));

    assert_eq!(child.role, "authoritative");
    assert_eq!(child.spec_role, "activation");
    assert_eq!(child.projection_kind, "exact");
    assert_eq!(child.projected_return_state, "known(nil)");
    assert_eq!(child.covered_activation_count, 1);
    assert_eq!(child.covered_known_count, 1);
    assert!(child.exact_coverage);
    assert!(!child.projection_gap);
}

#[test]
fn planner_emits_return_fixpoint_step_telemetry() {
    use crate::telemetry::{Capture, ConfiguredTelemetry};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let _ = frontend_plan("fn main(), do: 1 + 1", &tel);

    let ev = cap
        .last(&["fz", "planner", "return_fixpoint_step"])
        .expect("fz.planner.return_fixpoint_step event not emitted");
    assert!(matches!(
        ev.measurements.get("visit"),
        Some(crate::telemetry::Value::U64(_))
    ));
    assert!(matches!(
        ev.measurements.get("dep_count"),
        Some(crate::telemetry::Value::U64(_))
    ));
    assert!(matches!(
        ev.metadata.get("spec_key"),
        Some(crate::telemetry::Value::Str(_))
    ));
    assert!(matches!(
        ev.metadata.get("deps"),
        Some(crate::telemetry::Value::StrSeq(_))
    ));
    assert!(matches!(
        ev.metadata.get("new_ret"),
        Some(crate::telemetry::Value::Str(_))
    ));
}

#[test]
fn planner_work_bounds_ast_eval() {
    let src = std::fs::read_to_string("fixtures/ast_eval/input.fz").expect("read ast_eval fixture");
    let (pops, walks, typefns, specs) = observe_planner_work(&src);
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
fn planner_work_bounds_fib_tailrec() {
    let src =
        std::fs::read_to_string("fixtures/fib_tailrec/input.fz").expect("read fib_tailrec fixture");
    let (pops, walks, typefns, specs) = observe_planner_work(&src);
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
fn main(), do: dbg(sum([1, 2, 3, 4, 5]))
"#,
        &crate::telemetry::NullTelemetry,
    );
    let returns = mt.effective_returns.clone();
    let sum_fn = m.fns.iter().find(|f| f.name == "sum").unwrap();
    // At least one of sum's specs has a non-trivial return.
    let int = t.int();
    let any_int = returns
        .iter()
        .any(|(key, d)| key.fn_id == sum_fn.id && t.is_subtype(d, &int) && !t.is_empty(d));
    assert!(
        any_int,
        "expected at least one sum spec with return ⊆ int, got: {:?}",
        returns
            .iter()
            .filter(|(key, _)| key.fn_id == sum_fn.id)
            .collect::<Vec<_>>()
    );
    // CRUCIAL: no spec should claim return = singleton 0 (the
    // base case alone). That would mean cycle-cut leaked through.
    for (key, d) in &returns {
        if key.fn_id != sum_fn.id {
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

#[test]
fn cont_key_from_slot0_places_slot0_captures_and_padding() {
    let mut t = crate::types::ConcreteTypes;
    let slot0 = t.int_lit(7);
    let captured_a = Var(10);
    let captured_b = Var(11);
    let mut env = HashMap::new();
    let float = t.float();
    let ok = t.atom_lit("ok");
    env.insert(captured_a, float.clone());
    env.insert(captured_b, ok.clone());
    let any = t.any();

    let key = super::reachable::cont_key_from_slot0(
        &any,
        4,
        slot0.clone(),
        &[captured_a, captured_b],
        &env,
    );

    assert!(t.is_equivalent(&key[0], &slot0));
    assert!(t.is_equivalent(&key[1], &float));
    assert!(t.is_equivalent(&key[2], &ok));
    assert!(t.is_equivalent(&key[3], &any));
}

#[test]
fn cont_key_from_slot0_handles_zero_arity_continuation() {
    let mut t = crate::types::ConcreteTypes;
    let any = t.any();
    let int = t.int();
    let key = super::reachable::cont_key_from_slot0(&any, 0, int, &[Var(1)], &HashMap::new());
    assert!(key.is_empty());
}

/// Direct-Call slot 0 reflects the callee's narrowed return type,
/// not `any` — confirms .29.12.1 actually drives narrow Cont SpecId
/// resolution at call-sites where the planner has specialized the
/// callee.
#[test]
fn cont_slot0_narrows_to_callee_return_for_direct_call() {
    let (mut t, m, mt) = pipeline(
        r#"
fn add1(n), do: n + 1
fn main(), do: dbg(add1(40) + 2)
"#,
        &crate::telemetry::NullTelemetry,
    );
    let main = m.fns.iter().find(|f| f.name == "main").unwrap();
    let main_ft = mt.specs.get(&value_spec_key(main.id, vec![])).unwrap();
    let mut narrow_found = false;
    for blk in &main.blocks {
        if let Term::Call { .. } = &blk.terminator {
            let s0 = cont_slot0_descr(&mut t, blk, main_ft, &m, &mt);
            // add1's planner-specialized return for arg int_lit(40) is
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
/// `MakeClosure(double, [])`. The planner propagates
/// `callable_capabilities[f] = KnownFn(double)` into apply2's spec;
/// .29.10.2 registers double's narrow
/// spec for the typed arg from apply2's CallClosure; the CallClosure
/// is rewritten into a direct `Call(double, …)`.
#[test]
fn higher_order_callee_registers_narrow_spec_without_any_key_fallback() {
    let (mut t, m, mt) = pipeline(
        r#"
fn double(x), do: x * 2
fn apply2(f, x), do: f.(x)
fn main() do
  dbg(apply2(double, 21))
end
"#,
        &crate::telemetry::NullTelemetry,
    );
    let double = m.fns.iter().find(|f| f.name == "double").unwrap();
    let any_key = key_tys(vec![t.any()]);
    assert!(
        !mt.specs
            .contains_key(&value_spec_key(double.id, any_key.clone())),
        "expected double's any-key body to be absent when every callsite is typed; \
         registered specs for double: {:?}",
        mt.specs
            .keys()
            .filter(|key| key.fn_id == double.id)
            .collect::<Vec<_>>()
    );
    // Narrow spec from the direct-call path also exists.
    let narrow_count = mt
        .specs
        .keys()
        .filter(|key| {
            key.fn_id == double.id
                && key.demand.is_value()
                && !key
                    .input
                    .iter()
                    .all(|d| slot_ty(d).is_some_and(|ty| t.is_top(ty)))
        })
        .count();
    assert!(
        narrow_count >= 1,
        "expected ≥1 narrow spec for double from the direct-call path; \
         registered specs for double: {:?}",
        mt.specs
            .keys()
            .filter(|key| key.fn_id == double.id)
            .collect::<Vec<_>>()
    );
}

/// fz-ul4.29.12.6 — a fn whose every IR callsite has typed coverage
/// should NOT have its any-key spec registered in `module_plan.specs`.
/// `add` here is only called directly with `[int_lit(1), int_lit(2)]`;
/// no callsite queries with `[any, any]`, so the any-key body is dead.
#[test]
fn fn_with_only_typed_callsites_drops_any_key() {
    let (mut t, m, mt) = pipeline(
        r#"
fn add(a, b), do: a + b
fn main(), do: dbg(add(1, 2))
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
        !mt.specs
            .contains_key(&value_spec_key(add.id, any_key.clone())),
        "expected add's any-key to be dropped (no [any, any] callsite); \
         registered specs for add: {:?}",
        mt.specs
            .keys()
            .filter(|key| key.fn_id == add.id)
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
fn main(), do: dbg(42)
"#,
        &crate::telemetry::NullTelemetry,
    );
    let main = m.fns.iter().find(|f| f.name == "main").unwrap();
    let any_key: Vec<KeySlot> = vec![];
    assert!(
        mt.specs.contains_key(&value_spec_key(main.id, any_key)),
        "main must keep its any-key (entry-point)"
    );
}

/// fz-ul4.29.12.5 — a `Term::Receive` cont with a typed capture must
/// have a narrow spec registered (slot 0 = `any` per the opaque-
/// sender rule, slot 1+ narrowed from the caller's env). .29.12.1's
/// `emit_receive` resolves through subsumption against this spec to
/// pick a narrow cont SpecId for `fz_alloc_frame`; this test pins
/// the planner precondition.
#[test]
fn receive_cont_with_typed_capture_gets_narrow_spec() {
    let (t, m, mt) = pipeline(
        r#"
fn waiter(tag) do
  m = receive()
  dbg(m)
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
        for spec_key in mt.specs.keys() {
            if spec_key.fn_id != cont_id {
                continue;
            }
            let key = &spec_key.input;
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
            .filter(|(key, _)| m
                .fns
                .iter()
                .any(|f| f.id == key.fn_id && f.name.contains("waiter")))
            .map(|(key, _)| (key.fn_id, key.input.clone()))
            .collect::<Vec<_>>()
    );
}

/// fz-ul4.29.12.4 — spawn/1 now lives in runtime.fz, so there is no
/// compiler-synthesized fz_spawn_thunk between the wrapper and the user
/// closure. The spawned lambda stays reachable through the wrapper's real
/// closure call, not because `MakeClosure` invents an any-key body.
#[test]
fn spawn_wrapper_receives_known_closure_capability() {
    let (_t, m, mt) = frontend_plan(
        include_str!("../../fixtures/spawn_with_captures/input.fz"),
        &crate::telemetry::NullTelemetry,
    );
    assert!(
        !m.fns.iter().any(|f| f.name == "fz_spawn_thunk"),
        "spawn lowering must not synthesize fz_spawn_thunk"
    );
    let spawn = m
        .fns
        .iter()
        .find(|f| f.name == "Kernel.spawn" && f.block(f.entry).params.len() == 1)
        .expect("Kernel.spawn/1 prelude fn missing");
    let spawn_ft = mt
        .specs
        .iter()
        .find(|(key, _)| key.fn_id == spawn.id)
        .map(|(_, ft)| ft)
        .expect("Kernel.spawn/1 spec exists");
    let spawn_param = spawn.block(spawn.entry).params[0];
    assert!(
        matches!(
            spawn_ft.callable_capabilities.get(&spawn_param),
            Some(super::fn_types::CallableCapability::KnownClosure { .. })
        ),
        "Kernel.spawn/1 should receive a KnownClosure capability: {:?}",
        spawn_ft.callable_capabilities
    );
}

/// fz-ul4.29.12.2 — capture-specific refinements are ordinary call-site specs,
/// not a second closure-handle registry. Constructing a closure does not keep
/// an any-key body alive by itself.
#[test]
fn make_closure_with_distinct_captures_uses_lambda_specs_not_handles() {
    let (mut t, m, mt) = pipeline(
        r#"
fn add_to(x), do: fn (y) -> x + y end
fn main() do
  f = add_to(7)
  g = add_to(3.5)
  dbg(f.(1))
  dbg(g.(2.0))
end
"#,
        &crate::telemetry::NullTelemetry,
    );
    let lambda_body_specs = lambda_value_specs(&m, &mt);
    assert!(
        !lambda_body_specs.is_empty(),
        "expected lambda specs, got specs {:?}",
        mt.specs.keys().collect::<Vec<_>>()
    );
    assert!(
        lambda_any_key_specs(&mut t, &m, &mt).is_empty(),
        "expected no lambda any-key body specs, got {:?}",
        lambda_body_specs
    );
    assert!(
        mt.specs
            .keys()
            .any(|key| m.fn_by_id(key.fn_id).name.starts_with("lambda_")
                && key.demand.is_value()
                && !key
                    .input
                    .iter()
                    .all(|slot| slot_ty(slot).is_some_and(|ty| t.is_top(ty)))),
        "expected at least one call-site lambda specialization, got lambda specs {:?}",
        mt.specs
            .keys()
            .filter(|key| m.fn_by_id(key.fn_id).name.starts_with("lambda_"))
            .collect::<Vec<_>>()
    );
}

/// fz-rh5.1 — at a `CallClosure` whose closure operand resolves
/// via `closure_lit` (not a known callable capability), the continuation's slot 0
/// must be the lambda's narrow return type — NOT `any()`.
///
/// Pre-fz-5j5.3, continuation slot 0 and call-edge discovery computed
/// closure-literal call results through different paths. One path kept the
/// lambda's narrow return; the other fell back to `any`. Under the old
/// whole-graph-rebuild planner the disagreement was invisible; under
/// fz-5j5.3's worklist + reachability sweep split, keys diverged and cont
/// specs went stale.
///
/// This test pins the post-fix behavior: a cont after a CallClosure
/// on a closure_lit-typed value has slot 0 = the lambda's narrow return.
#[test]
fn cont_slot0_after_closure_lit_callclosure_is_narrow_not_any() {
    let (t, m, mt) = pipeline(
        r#"
fn add_to(x), do: fn (y) -> x + y end
fn main() do
  f = add_to(7)
  r = f.(1)
  dbg(r + 100)
end
"#,
        &crate::telemetry::NullTelemetry,
    );

    // The cont after `f(1)` receives an `int`. Find the k_ cont fn
    // whose key starts with an int type (the lambda's return).
    let k_specs: Vec<&Vec<KeySlot>> = mt
        .specs
        .iter()
        .filter(|(key, _)| {
            m.fns
                .iter()
                .find(|f| f.id == key.fn_id)
                .is_some_and(|f| f.name.starts_with("k_"))
        })
        .map(|(key, _)| &key.input)
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
/// the planner's opaque-callee rule.
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
  r = f.(x)
  r + 1
end
fn main() do
  inc = fn (n) -> n + 1 end
  z = apply(inc, 3)
  dbg(z)
end
"#,
        &crate::telemetry::NullTelemetry,
    );
    let apply_fn = m.fns.iter().find(|f| f.name == "apply").unwrap();
    let caller_ft = mt
        .specs
        .iter()
        .find(|(key, _)| key.fn_id == apply_fn.id)
        .map(|(_, ft)| ft)
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

// ---- fz-ul4.29.10.1 — callable capability propagation ----

/// A zero-capture `MakeClosure(F, [])` (synthesized by ir_lower when
/// a bare top-level fn name is used as a value) populates
/// `callable_capabilities[v] = KnownFn(F)` on the Let-bound var.
#[test]
fn known_fn_capability_from_makeclosure_zero_captures() {
    let (_t, m, mt) = pipeline(
        r#"
fn double(x), do: x * 2
fn apply2(f, x), do: f.(x)
fn main() do
  dbg(apply2(double, 21))
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
        .find(|(key, _)| key.fn_id == main.id)
        .map(|(_, ft)| ft)
        .expect("main spec exists");
    assert_eq!(
        main_ft.callable_capabilities.get(&v),
        Some(&CallableCapability::KnownFn(double.id)),
        "zero-capture MakeClosure should populate KnownFn capability"
    );
}

/// A `MakeClosure` with captures is a real closure value, not a
/// fn-as-value. It records a stateful closure capability, not `KnownFn`.
#[test]
fn known_fn_capability_not_set_for_captures() {
    let (_t, m, mt) = pipeline(
        r#"
fn main() do
  k = 7
  f = fn (n) -> n + k end
  dbg(f.(3))
end
"#,
        &crate::telemetry::NullTelemetry,
    );
    let main = m.fns.iter().find(|f| f.name == "main").unwrap();
    let main_ft = mt
        .specs
        .iter()
        .find(|(key, _)| key.fn_id == main.id)
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
    match main_ft.callable_capabilities.get(&v) {
        Some(CallableCapability::KnownClosure { fn_id, captures }) => {
            assert!(!captures.is_empty(), "captured closure should record state");
            let lambda = m.fn_by_id(*fn_id);
            assert!(
                lambda.name.contains("lambda") || lambda.name.contains("anon"),
                "expected synthesized lambda target, got {}",
                lambda.name
            );
        }
        other => panic!("captured MakeClosure should record KnownClosure, got {other:?}"),
    }
}

/// `apply2(double, 21)` — in apply2's specialized SpecPlan, the
/// `f` entry param has `callable_capabilities[f_param] = KnownFn(double)`,
/// propagated from main's callsite.
#[test]
fn known_fn_capability_propagates_via_direct_call() {
    let (_t, m, mt) = pipeline(
        r#"
fn double(x), do: x * 2
fn apply2(f, x), do: f.(x)
fn main() do
  dbg(apply2(double, 21))
end
"#,
        &crate::telemetry::NullTelemetry,
    );
    let apply2 = m.fns.iter().find(|f| f.name == "apply2").unwrap();
    let double = m.fns.iter().find(|f| f.name == "double").unwrap();
    let apply2_entry = apply2.block(apply2.entry);
    let f_param = apply2_entry.params[0]; // first param is `f`
    let mut saw_capability = false;
    for (key, ft) in &mt.specs {
        if key.fn_id != apply2.id {
            continue;
        }
        if ft.callable_capabilities.get(&f_param) == Some(&CallableCapability::KnownFn(double.id)) {
            saw_capability = true;
        }
    }
    assert!(
        saw_capability,
        "expected apply2's spec to carry callable_capabilities[f] = KnownFn(double)"
    );
}

#[test]
fn callable_capability_opaque_for_multi_target_join() {
    let mut id_a = FnBuilder::new(FnId(1), "id_a");
    let a_x = id_a.fresh_var();
    let a_entry = id_a.block(vec![a_x]);
    id_a.set_terminator(a_entry, Term::Return(a_x));

    let mut id_b = FnBuilder::new(FnId(2), "id_b");
    let b_x = id_b.fresh_var();
    let b_entry = id_b.block(vec![b_x]);
    id_b.set_terminator(b_entry, Term::Return(b_x));

    let mut main = FnBuilder::new(FnId(0), "main");
    let cond = main.fresh_var();
    let entry = main.block(vec![cond]);
    let then_b = main.block(vec![]);
    let else_b = main.block(vec![]);
    let join = main.fresh_var();
    let join_b = main.block(vec![join]);
    let a = main.let_(
        then_b,
        Prim::MakeClosure(crate::fz_ir::CallsiteIdent::synthetic(), FnId(1), vec![]),
    );
    main.set_terminator(then_b, Term::Goto(join_b, vec![a]));
    let b = main.let_(
        else_b,
        Prim::MakeClosure(crate::fz_ir::CallsiteIdent::synthetic(), FnId(2), vec![]),
    );
    main.set_terminator(else_b, Term::Goto(join_b, vec![b]));
    main.set_terminator(entry, Term::if_user(cond, then_b, else_b));
    main.set_terminator(join_b, Term::Return(join));

    let m = build_module(vec![main.build(), id_a.build(), id_b.build()]);
    let mut t = crate::types::ConcreteTypes;
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    let main_ft = mt.any_spec_for(FnId(0)).expect("main spec exists");

    assert_eq!(
        main_ft.callable_capabilities.get(&join),
        Some(&CallableCapability::OpaqueCallable),
        "join of distinct closure targets should be an opaque callable capability"
    );
}

// ---- fz-ul4.29.10.2 — narrow F-spec from known-target CallClosure ----

// ---- fz-ul4.29.10.3 — IR rewrite of known-target closures ----

/// `rewrite_known_target_closures` replaces `Term::CallClosure(v, …)`
/// with `Term::Call(F, …)` when every spec of the enclosing FnIr
/// agrees that `callable_capabilities[v] = KnownFn(F)`.
#[test]
fn closure_call_rewritten_to_direct_call() {
    let (mut t, mut m, _mt) = pipeline(
        r#"
fn double(x), do: x * 2
fn apply_plus1(f, x) do
  r = f.(x)
  r + 1
end
fn main() do
  dbg(apply_plus1(double, 21))
end
"#,
        &crate::telemetry::NullTelemetry,
    );
    let caps = crate::ir_planner::plan_callable_capabilities(&mut t, &m);
    rewrite_known_target_closures(&mut t, &mut m, &caps);
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
    let (mut t, mut m, _mt) = pipeline(
        r#"
fn double(x), do: x * 2
fn apply2(f, x), do: f.(x)
fn main() do
  apply2(double, 21)
end
"#,
        &crate::telemetry::NullTelemetry,
    );
    let caps = crate::ir_planner::plan_callable_capabilities(&mut t, &m);
    rewrite_known_target_closures(&mut t, &mut m, &caps);
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
/// With `KnownFn(double)` propagated from main, the planner's
/// queried-set walk should register `(double, [int_lit(21)])` as a
/// narrow spec for double — alongside its any-key (which .29.10.3
/// will drop). This guarantees a narrow spec exists for the IR
/// rewrite to dispatch into.
#[test]
fn callclosure_with_known_fn_capability_registers_narrow_spec() {
    let (t, m, mt) = pipeline(
        r#"
fn double(x), do: x * 2
fn apply2(f, x), do: f.(x)
fn main() do
  dbg(apply2(double, 21))
end
"#,
        &crate::telemetry::NullTelemetry,
    );
    let double = m.fns.iter().find(|f| f.name == "double").unwrap();
    let mut saw_narrow = false;
    for spec_key in mt.specs.keys() {
        if spec_key.fn_id != double.id {
            continue;
        }
        let key = &spec_key.input;
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
         apply2's CallClosure with callable_capabilities[f] = KnownFn(double); \
         registered specs for double: {:?}",
        mt.specs
            .iter()
            .filter(|(key, _)| key.fn_id == double.id)
            .map(|(key, _)| key.input.clone())
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
    let mut er: HashMap<SpecKey, crate::types::Ty> = HashMap::new();
    let key = vec![t.int_lit(21)];
    let int = t.int();
    er.insert(value_spec_key(fid(7), key_tys(key)), int.clone());
    let arg_tys = [t.int_lit(21)];
    let r = resolve_closure_return(&mut t, &closure, &er, &arg_tys).unwrap();
    assert!(t.is_equivalent(&r, &int));
}

#[test]
fn resolve_closure_return_singleton_miss_returns_none() {
    // Singleton with no matching effective_returns entry → None (defer).
    let er: HashMap<SpecKey, crate::types::Ty> = HashMap::new();
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
    let mut er: HashMap<SpecKey, crate::types::Ty> = HashMap::new();
    let key = vec![t.int_lit(10), t.int_lit(20), t.int_lit(12)];
    let int42 = t.int_lit(42);
    er.insert(value_spec_key(fid(8), key_tys(key)), int42);
    let arg_tys = [t.int_lit(12)];
    let r = resolve_closure_return(&mut t, &closure, &er, &arg_tys).unwrap();
    assert_eq!(t.as_int_singleton(&r), Some(42));
}

#[test]
fn resolve_closure_return_plain_arrow_uses_sig_ret() {
    // Lit-free arrow: ret comes straight from sig.ret (matches
    // arrow_join_return).
    let er: HashMap<SpecKey, crate::types::Ty> = HashMap::new();
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
    let mut er: HashMap<SpecKey, crate::types::Ty> = HashMap::new();
    let key = vec![t.int_lit(21)];
    let int = t.int();
    let ok = t.atom_lit("ok");
    er.insert(value_spec_key(fid(7), key_tys(key.clone())), int.clone());
    er.insert(value_spec_key(fid(8), key_tys(key)), ok.clone());
    let arg_tys = [t.int_lit(21)];
    let r = resolve_closure_return(&mut t, &closure, &er, &arg_tys).unwrap();
    let expected = t.union(int, ok);
    assert!(t.is_equivalent(&r, &expected));
}

#[test]
fn resolve_closure_return_union_one_miss_defers() {
    // Two clauses; one has a registered spec, the other doesn't. The
    // helper conservatively defers (returns None) so the planner's
    // fixpoint can re-try after the missing spec is registered.
    let mut t = crate::types::ConcreteTypes;
    let a = t.closure_lit(fid(7).into(), vec![], 1);
    let b = t.closure_lit(fid(8).into(), vec![], 1);
    let closure = t.union(a, b);
    let mut er: HashMap<SpecKey, crate::types::Ty> = HashMap::new();
    let key = t.int_lit(21);
    let int = t.int();
    er.insert(value_spec_key(fid(7), key_tys(vec![key])), int);
    // No entry for (8, _) → defer.
    let arg_tys = [t.int_lit(21)];
    let r = resolve_closure_return(&mut t, &closure, &er, &arg_tys);
    assert_eq!(r, None);
}

#[test]
fn resolve_closure_return_empty_funcs_is_any() {
    // Type with no funcs at all: arrow_join_return-style any default.
    let er: HashMap<SpecKey, crate::types::Ty> = HashMap::new();
    let mut t = crate::types::ConcreteTypes;
    let closure = t.none();
    let r = resolve_closure_return(&mut t, &closure, &er, &[]).unwrap();
    let any = t.any();
    assert!(t.is_equivalent(&r, &any));
}

#[test]
fn resolve_closure_return_saturated_arrow_is_any() {
    // `any()` has funcs = [Conj::top()] — pos empty, no narrowing.
    let er: HashMap<SpecKey, crate::types::Ty> = HashMap::new();
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
/// projection used by reducer / ir_inline / planner to share one
/// callsite vocabulary.
#[test]
fn callsite_id_round_trip() {
    use crate::fz_ir::{BlockId, CallsiteId, EmitSlot};

    let mut t = crate::types::ConcreteTypes;
    let any = t.any();
    let three = t.int_lit(3);
    let spec_key = value_spec_key(FnId(7), key_tys(vec![any, three]));
    let _ = BlockId(2); // older positional fixture data; ident is now intrinsic.
    let test_ident = crate::fz_ir::CallsiteIdent::synthetic();
    let site = EmitterSite {
        caller: spec_key.clone(),
        ident: test_ident.clone(),
        slot: EmitSlot::ClosureCall,
    };

    let cid: CallsiteId = emitter_site_callsite_id(&site);
    assert_eq!(cid.caller, FnId(7));
    assert_eq!(cid.ident, test_ident);
    assert_eq!(cid.slot, EmitSlot::ClosureCall);

    let round = callsite_with_spec_key(cid, spec_key);
    assert_eq!(round, site);
}

/// fz-uwq.3/.11 — `plan_module` populates `SpecPlan.call_edges` with
/// the per-spec dispatch target for each Direct callsite. Build a
/// trivial 2-fn module (main → id), assert the dispatch entry exists
/// at main's spec keyed by `id` plus the literal arg type.
#[test]
fn planner_publishes_dispatches_for_direct_call() {
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
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);

    let cid = CallsiteId {
        caller: FnId(1),
        ident: tc_ident,
        slot: EmitSlot::Direct,
    };
    let main_spec = mt
        .specs
        .get(&value_spec_key(FnId(1), vec![]))
        .expect("main's empty-key spec must exist");
    let target = main_spec
        .local_call_target(&cid)
        .expect("call_edges should record main's Direct call to id");
    assert_eq!(target.fn_id, FnId(0));
    assert_eq!(target.input.len(), 1);
    let Some(ty) = &target.input[0] else {
        panic!(
            "direct dispatch arg should be typed, got {:?}",
            target.input[0]
        );
    };
    assert_eq!(t.as_int_singleton(ty), Some(42));
}

#[test]
fn planner_publishes_dispatches_for_closure_lit_call() {
    use crate::fz_ir::{CallsiteId, EmitSlot};

    let src = r#"
fn each(_, []), do: nil
fn each(f, [h | t]) do
  f.(h)
  each(f, t)
end

fn main() do
  k = 10
  each(fn(x) -> dbg(x + k) end, [1, 2, 3])
end
"#;
    let m = lower_src_for_plan(src);
    let mut t = crate::types::ConcreteTypes;
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    let mut saw_closure_lit_call = false;

    for (caller_key, ft) in &mt.specs {
        let caller = m.fn_by_id(caller_key.fn_id);
        for blk in &caller.blocks {
            let Term::CallClosure {
                ident,
                closure,
                args: _,
                ..
            } = &blk.terminator
            else {
                continue;
            };
            let Some(closure_ty) = ft.vars.get(closure) else {
                continue;
            };
            let Some(lit) = t.closure_lit_parts(closure_ty) else {
                continue;
            };

            let callsite = CallsiteId::new(caller.id, ident, EmitSlot::ClosureCall);
            let target = ft.local_call_target(&callsite).unwrap_or_else(|| {
                panic!(
                    "expected ClosureCall target for {:?}; available call_edges: {:?}",
                    callsite,
                    ft.call_edges.keys().collect::<Vec<_>>()
                )
            });
            let body_fid: FnId = lit.target.into();
            assert_eq!(target.fn_id, body_fid);
            assert!(
                m.fn_by_id(body_fid).name.starts_with("lambda_"),
                "closure-literal call should target the synthesized lambda body, got {}",
                m.fn_by_id(body_fid).name
            );

            let capture_ty =
                target.input.first().and_then(slot_ty).unwrap_or_else(|| {
                    panic!("target key should include capture slot: {target:?}")
                });
            assert_eq!(t.as_int_singleton(capture_ty), Some(10));
            let arg_ty =
                target.input.get(1).and_then(slot_ty).unwrap_or_else(|| {
                    panic!("target key should include argument slot: {target:?}")
                });
            let int_ty = t.int();
            assert!(
                t.is_equivalent(arg_ty, &int_ty),
                "recursive closure-call argument should widen to int, got {}",
                t.display(arg_ty)
            );
            saw_closure_lit_call = true;
        }
    }

    assert!(
        saw_closure_lit_call,
        "expected at least one typed CallClosure over a singleton closure literal"
    );
}

#[test]
fn planner_selects_static_protocol_impl_as_call_edge() {
    use crate::fz_ir::{CallsiteId, EmitSlot};

    let src = r#"
defprotocol Collectable do
  fn id(value)
end

defimpl Collectable, for: List do
  fn id(value), do: value
end

fn main(), do: Collectable.id([1])
"#;
    let toks = crate::parser::lexer::Lexer::new(src)
        .tokenize()
        .expect("lex");
    let parsed = crate::parser::Parser::new(toks)
        .parse_program()
        .expect("parse");
    let mut t = crate::types::ConcreteTypes;
    let resolved = crate::frontend::resolve::flatten_modules(&mut t, parsed).expect("resolve");
    let ir = crate::ir_lower::lower_program(&mut t, &resolved, &crate::telemetry::NullTelemetry)
        .expect("lower");
    let mt = plan_module(&mut t, &ir, &crate::telemetry::NullTelemetry);

    let main = ir.fn_by_name("main").expect("main");
    let Term::TailCall { ident, .. } = &main.block(main.entry).terminator else {
        panic!("expected protocol call in tail position");
    };
    let cid = CallsiteId {
        caller: main.id,
        ident: ident.clone(),
        slot: EmitSlot::Direct,
    };
    let main_spec = mt
        .specs
        .get(&value_spec_key(main.id, vec![]))
        .expect("main spec");
    let target = main_spec
        .local_call_target(&cid)
        .expect("protocol dispatch should publish a direct impl call edge");
    let target_fn = ir.fn_by_id(target.fn_id);
    assert_eq!(target_fn.name, "Collectable.List.id");
}

#[test]
fn planner_keeps_external_module_calls_at_provider_boundary() {
    use crate::fz_ir::{CallsiteId, EmitSlot};
    use crate::ir_planner::fn_types::CallEdgeTarget;

    let mut t = crate::types::ConcreteTypes;
    let tel = crate::telemetry::NullTelemetry;
    let math = crate::frontend::compile_source_with_types(
        &mut t,
        "defmodule Math do\n  fn add(x, y), do: x + y\nend\n".to_string(),
        "math.fz".to_string(),
        &tel,
    )
    .unwrap_or_else(|err| panic!("math frontend: {:?}", err.diagnostics));
    let math_name = crate::modules::identity::ModuleName::from_segments(vec!["Math".to_string()]);
    let math_interface = math
        ._prog
        .module_interfaces
        .get(&math_name)
        .cloned()
        .expect("Math interface");

    let mut interfaces = crate::frontend::resolve::InterfaceTable::new();
    interfaces.insert(math_name, math_interface);
    let user = crate::frontend::compile_source_with_interface_table(
        &mut t,
        "defmodule User do\n  import Math, only: [add: 2]\n  fn run(), do: add(20, 22) + 1\nend\nfn main(), do: User.run()\n".to_string(),
        "user.fz".to_string(),
        interfaces,
        &tel,
    )
    .unwrap_or_else(|err| panic!("user frontend: {:?}", err.diagnostics));

    let edge = user
        .module
        .external_call_edges
        .first()
        .expect("lowering should record the imported Math.add callsite");
    let run = user.module.fn_by_name("User.run").expect("User.run");
    assert_eq!(edge.callsite.caller, run.id);

    let run_spec = user
        .module_plan
        .specs
        .values()
        .find(|spec| spec.call_edges.contains_key(&edge.callsite))
        .expect("User.run spec should carry the direct external edge");
    let direct = run_spec
        .call_edges
        .get(&edge.callsite)
        .expect("direct call edge");
    assert!(
        matches!(&direct.target, CallEdgeTarget::External { target, .. }
            if target.module.to_string() == "Math" && target.name == "add")
    );

    let cont_callsite = CallsiteId::new(run.id, &edge.callsite.ident, EmitSlot::Cont);
    assert!(
        run_spec.local_call_target(&cont_callsite).is_some(),
        "external calls still need a local continuation dispatch"
    );
    assert!(
        !user.module_plan.specs.values().any(|spec| {
            spec.call_edges.values().any(|edge| {
                edge.local_target()
                    .map(|target| {
                        user.module
                            .fn_by_id(target.fn_id)
                            .name
                            .starts_with("__external__.")
                    })
                    .unwrap_or(false)
            })
        }),
        "external boundary calls must not be planned through the synthetic stub body"
    );
}

#[test]
fn planner_publishes_cont_dispatches_for_non_tail_calls_in_enum_take_drop_split() {
    use crate::fz_ir::{CallsiteId, EmitSlot, Term};

    let src = include_str!("../../fixtures/enum_take_drop_split/input.fz");
    let mut t = crate::types::ConcreteTypes;
    let compiled = crate::frontend::compile_source_with_types(
        &mut t,
        src.to_string(),
        "enum_take_drop_split_input.fz".to_string(),
        &crate::telemetry::NullTelemetry,
    )
    .unwrap_or_else(|err| panic!("frontend compile: {:?}", err.diagnostics));
    let m = compiled.module;
    let mt = compiled.module_plan;

    for (spec_key, spec) in &mt.specs {
        let body = m.fn_by_id(spec_key.fn_id);
        for block in &body.blocks {
            let Term::Call {
                ident,
                continuation: _,
                ..
            } = &block.terminator
            else {
                continue;
            };
            let cont_callsite = CallsiteId::new(body.id, ident, EmitSlot::Cont);
            assert!(
                spec.local_call_target(&cont_callsite).is_some(),
                "missing Cont dispatch for {} spec {:?} at {:?}; available call_edges: {:?}",
                body.name,
                spec_key,
                cont_callsite,
                spec.call_edges.keys().collect::<Vec<_>>()
            );
        }
    }
}

#[test]
fn declared_return_fact_handles_enum_count_on_range_in_runtime_graph() {
    let src = include_str!("../../fixtures/enum_take_drop_split/input.fz");
    let mut t = crate::types::ConcreteTypes;
    let tel = crate::telemetry::NullTelemetry;
    let providers = crate::modules::pipeline::ProviderInputs::new(
        crate::modules::artifact_store::DEFAULT_ARTIFACT_ROOT.to_string(),
        Vec::new(),
    );
    let frontend = crate::modules::pipeline::compile_source_with_providers(
        &mut t,
        src.to_string(),
        "enum_take_drop_split_input.fz".to_string(),
        &providers,
        &tel,
    )
    .unwrap_or_else(|err| panic!("frontend result: {err}"));
    let checked = crate::modules::pipeline::checked_module_for_mode(
        &mut t,
        frontend,
        &tel,
        crate::modules::pipeline::CompileMode::Normal,
    )
    .unwrap_or_else(|err| panic!("checked module: {err}"));
    let prepared = crate::modules::pipeline::prepare_execution_graph(
        &mut t,
        checked,
        &providers,
        &tel,
        crate::modules::pipeline::CompileMode::Normal,
    )
    .unwrap_or_else(|err| panic!("execution graph: {err}"));
    let module = prepared.module;

    let callee = module.fn_by_name("Enum.count").expect("Enum.count").id;
    let range = t.opaque_of("impl-target::Range");
    let fact = declared_return_fact_for_test(
        &mut t,
        &module,
        callee,
        callee,
        &[range],
        &std::collections::HashMap::new(),
        None,
    )
    .expect("declared return fact for Enum.count(range)");
    let int = t.int();
    assert!(
        t.is_subtype(&fact.ty, &int) && t.is_subtype(&int, &fact.ty),
        "Enum.count(range) declared return should be integer, got {}",
        t.display(&fact.ty)
    );
}

#[test]
fn runtime_graph_mixed_enum_take_calls_plan_range_specialization() {
    let src = r#"
fn main() do
  xs = [1, 2, 3, 4, 5]
  range = 1..5
  dbg(Enum.take(xs, 3))
  dbg(Enum.take(xs, 0))
  dbg(Enum.take(xs, 9))
  dbg(Enum.take(xs, -2))
  dbg(Enum.take(range, -2))
end
"#;
    let mut t = crate::types::ConcreteTypes;
    let tel = crate::telemetry::NullTelemetry;
    let providers = crate::modules::pipeline::ProviderInputs::new(
        crate::modules::artifact_store::DEFAULT_ARTIFACT_ROOT.to_string(),
        Vec::new(),
    );
    let frontend = crate::modules::pipeline::compile_source_with_providers(
        &mut t,
        src.to_string(),
        "mixed_enum_take_input.fz".to_string(),
        &providers,
        &tel,
    )
    .unwrap_or_else(|err| panic!("frontend result: {err}"));
    let checked = crate::modules::pipeline::checked_module_for_mode(
        &mut t,
        frontend,
        &tel,
        crate::modules::pipeline::CompileMode::Normal,
    )
    .unwrap_or_else(|err| panic!("checked module: {err}"));
    let prepared = crate::modules::pipeline::prepare_execution_graph(
        &mut t,
        checked,
        &providers,
        &tel,
        crate::modules::pipeline::CompileMode::Normal,
    )
    .unwrap_or_else(|err| panic!("execution graph: {err}"));
    let module = prepared.module;
    let plan = super::plan_module(&mut t, &module, &tel);
    let take = module.fn_by_name("Enum.take").expect("Enum.take");
    let range = t.opaque_of("impl-target::Range");

    let matching_specs = plan
        .specs
        .keys()
        .filter(|key| {
            key.fn_id == take.id
                && key
                    .input
                    .first()
                    .and_then(|slot| slot.as_ref())
                    .is_some_and(|ty| t.is_equivalent(ty, &range))
        })
        .collect::<Vec<_>>();
    assert!(
        !matching_specs.is_empty(),
        "mixed Enum.take calls must keep a range specialization; external_edges={:?}; Enum.take specs: {:?}; call edges: {:?}",
        module.external_call_edges,
        plan.specs
            .keys()
            .filter(|key| key.fn_id == take.id)
            .collect::<Vec<_>>(),
        plan.specs
            .iter()
            .flat_map(|(caller, spec)| spec
                .call_edges
                .values()
                .filter_map(move |edge| edge.local_target().map(|target| (caller, target))))
            .filter(|(_, target)| target.fn_id == take.id)
            .collect::<Vec<_>>(),
    );
}

#[test]
fn declared_return_fact_handles_enum_reduce_with_runtime_graph_reducer() {
    let src = include_str!("../../fixtures/enum_take_drop_split/input.fz");
    let mut t = crate::types::ConcreteTypes;
    let tel = crate::telemetry::NullTelemetry;
    let providers = crate::modules::pipeline::ProviderInputs::new(
        crate::modules::artifact_store::DEFAULT_ARTIFACT_ROOT.to_string(),
        Vec::new(),
    );
    let frontend = crate::modules::pipeline::compile_source_with_providers(
        &mut t,
        src.to_string(),
        "enum_take_drop_split_input.fz".to_string(),
        &providers,
        &tel,
    )
    .unwrap_or_else(|err| panic!("frontend result: {err}"));
    let checked = crate::modules::pipeline::checked_module_for_mode(
        &mut t,
        frontend,
        &tel,
        crate::modules::pipeline::CompileMode::Normal,
    )
    .unwrap_or_else(|err| panic!("checked module: {err}"));
    let prepared = crate::modules::pipeline::prepare_execution_graph(
        &mut t,
        checked,
        &providers,
        &tel,
        crate::modules::pipeline::CompileMode::Normal,
    )
    .unwrap_or_else(|err| panic!("execution graph: {err}"));
    let module = prepared.module;
    let plan = super::plan_module(&mut t, &module, &tel);

    let drop_positive = module
        .fn_by_name("Enum.drop_positive")
        .expect("Enum.drop_positive");
    let drop_positive_key = plan
        .specs
        .keys()
        .find(|key| key.fn_id == drop_positive.id)
        .cloned()
        .expect("drop_positive spec key");
    let drop_positive_spec = plan
        .specs
        .get(&drop_positive_key)
        .expect("drop_positive spec");
    let block = &drop_positive.blocks[0];
    let crate::fz_ir::Term::Call { callee, args, .. } = &block.terminator else {
        panic!("drop_positive entry should call Enum.reduce");
    };
    let env = super::diagnostics::env_after_block_stmts(&mut t, &module, drop_positive_spec, block);
    let arg_tys = args
        .iter()
        .map(|arg| env.get(arg).cloned().unwrap_or_else(|| t.any()))
        .collect::<Vec<_>>();
    let fact = declared_return_fact_for_test(
        &mut t,
        &module,
        drop_positive.id,
        *callee,
        &arg_tys,
        &plan.effective_returns,
        None,
    )
    .expect("declared return fact for Enum.reduce in drop_positive");
    let none = t.none();
    assert!(
        !t.is_equivalent(&fact.ty, &none),
        "Enum.reduce in drop_positive should have a non-bottom declared return, got {} from args {:?}",
        t.display(&fact.ty),
        arg_tys.iter().map(|ty| t.display(ty)).collect::<Vec<_>>()
    );
}

#[test]
fn declared_return_fact_handles_take_positive_reduce_while_in_runtime_graph() {
    let src = include_str!("../../fixtures/enum_take_drop_split/input.fz");
    let mut t = crate::types::ConcreteTypes;
    let tel = crate::telemetry::NullTelemetry;
    let providers = crate::modules::pipeline::ProviderInputs::new(
        crate::modules::artifact_store::DEFAULT_ARTIFACT_ROOT.to_string(),
        Vec::new(),
    );
    let frontend = crate::modules::pipeline::compile_source_with_providers(
        &mut t,
        src.to_string(),
        "enum_take_drop_split_input.fz".to_string(),
        &providers,
        &tel,
    )
    .unwrap_or_else(|err| panic!("frontend result: {err}"));
    let checked = crate::modules::pipeline::checked_module_for_mode(
        &mut t,
        frontend,
        &tel,
        crate::modules::pipeline::CompileMode::Normal,
    )
    .unwrap_or_else(|err| panic!("checked module: {err}"));
    let prepared = crate::modules::pipeline::prepare_execution_graph(
        &mut t,
        checked,
        &providers,
        &tel,
        crate::modules::pipeline::CompileMode::Normal,
    )
    .unwrap_or_else(|err| panic!("execution graph: {err}"));
    let module = prepared.module;
    let plan = super::plan_module(&mut t, &module, &tel);

    let take_positive = module
        .fn_by_name("Enum.take_positive")
        .expect("Enum.take_positive");
    let int = t.int();
    let zero = t.int_lit(0);
    let nonzero = t.difference(int, zero);
    let specs = plan
        .specs
        .iter()
        .filter(|(key, _)| {
            key.fn_id == take_positive.id
                && matches!(key.input.get(1), Some(Some(ty)) if t.is_equivalent(ty, &nonzero))
        })
        .collect::<Vec<_>>();
    assert!(
        !specs.is_empty(),
        "expected at least one take_positive nonzero-amount spec, got {:?}",
        plan.specs
            .keys()
            .filter(|key| key.fn_id == take_positive.id)
            .map(|key| key
                .input
                .iter()
                .map(|slot| slot.as_ref().map(|ty| t.display(ty)))
                .collect::<Vec<_>>())
            .collect::<Vec<_>>()
    );
    let block = &take_positive.blocks[0];
    let crate::fz_ir::Term::Call { callee, args, .. } = &block.terminator else {
        panic!("take_positive entry should call Enum.reduce_while");
    };
    let complete = plan
        .specs
        .keys()
        .cloned()
        .collect::<std::collections::HashSet<_>>();
    for (spec_key, spec) in specs {
        let env = super::diagnostics::env_after_block_stmts(&mut t, &module, spec, block);
        let arg_tys = args
            .iter()
            .map(|arg| env.get(arg).cloned().unwrap_or_else(|| t.any()))
            .collect::<Vec<_>>();
        let fact = declared_return_fact_for_test(
            &mut t,
            &module,
            take_positive.id,
            *callee,
            &arg_tys,
            &plan.effective_returns,
            Some(&complete),
        )
        .unwrap_or_else(|| {
            let callee_fn = module.fn_by_id(*callee);
            let declared_set = module.declared_specs.get(callee);
            let declared = declared_set
                .map(|set| {
                    set.arrows
                        .iter()
                        .map(|arrow| format!("{:?}", arrow))
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default();
            let first_match = declared_set
                .and_then(|set| set.arrows.first())
                .map(|arrow| {
                    format!(
                        "{:?}",
                        crate::specs::instantiate_match(
                            &mut t,
                            &arrow.params,
                            &arrow.result,
                            &arrow.constraints,
                            &arg_tys,
                        )
                    )
                })
                .unwrap_or_else(|| "no declared arrow".to_string());
            let callback_return = t
                .callable_clauses(&arg_tys[2])
                .and_then(|clauses| clauses.into_iter().find_map(|clause| clause.closure))
                .map(|closure| {
                    let mut key = closure.captures.clone();
                    key.extend([arg_tys[0].clone(), arg_tys[1].clone()]);
                    let target_fn: crate::fz_ir::FnId = closure.target.into();
                    let target = module.fn_by_id(target_fn);
                    let spec_key = super::fn_types::fixed_point_spec_key_for_arity(
                        &mut t,
                        &module,
                        &std::collections::HashSet::new(),
                        &super::fn_types::FixedPointSlotSummaries::new(),
                        take_positive.id,
                        target_fn,
                        key,
                        target.block(target.entry).params.len(),
                        Some(super::fn_types::ReturnDemand::value()),
                    );
                    format!(
                        "target={} key={:?} return={}",
                        target.name,
                        spec_key.input
                            .iter()
                            .map(|slot| slot.as_ref().map(|ty| t.display(ty)))
                            .collect::<Vec<_>>(),
                        plan.effective_returns
                            .get(&spec_key)
                            .map(|ty| t.display(ty))
                            .unwrap_or_else(|| "<missing>".to_string())
                    )
                })
                .unwrap_or_else(|| "<no closure lit>".to_string());
            panic!(
                "declared return fact for Enum.reduce_while in take_positive should exist for input {:?}; callee={} arg_tys={:?} first_match={} callback_return={} declared={:?}",
                spec_key
                    .input
                    .iter()
                    .map(|slot| slot.as_ref().map(|ty| t.display(ty)))
                    .collect::<Vec<_>>(),
                callee_fn.name,
                arg_tys.iter().map(|ty| t.display(ty)).collect::<Vec<_>>(),
                first_match,
                callback_return,
                declared
            )
        });
        let none = t.none();
        assert!(
            !t.is_equivalent(&fact.ty, &none),
            "Enum.reduce_while in take_positive should have a non-bottom declared return for input {:?}, got {} (complete={} reads={:?}) from args {:?}",
            spec_key
                .input
                .iter()
                .map(|slot| slot.as_ref().map(|ty| t.display(ty)))
                .collect::<Vec<_>>(),
            t.display(&fact.ty),
            fact.complete,
            fact.reads,
            arg_tys.iter().map(|ty| t.display(ty)).collect::<Vec<_>>()
        );
    }
}

#[test]
fn runtime_graph_reduce_helper_clause_carries_function_correspondence() {
    let src = "defmodule Probe do\n\
      @spec reduce_cont([a], b, (a, b) -> {:cont, b} | {:halt, b} | {:suspend, b}) :: {:done, b} | {:halted, b} | {:suspended, b, () -> any}\n\
      fn reduce_cont([], acc, _reducer), do: {:done, acc}\n\
      fn reduce_cont([head | tail], acc, reducer) do\n\
        reduce_step(tail, reducer.(head, acc), reducer)\n\
      end\n\
      @spec reduce_step([a], {:cont, b} | {:halt, b} | {:suspend, b}, (a, b) -> {:cont, b} | {:halt, b} | {:suspend, b}) :: {:done, b} | {:halted, b} | {:suspended, b, () -> any}\n\
      fn reduce_step(list, {:cont, acc}, reducer), do: reduce_cont(list, acc, reducer)\n\
      fn reduce_step(_list, {:halt, acc}, _reducer), do: {:halted, acc}\n\
      fn reduce_step(list, {:suspend, acc}, reducer) do\n\
        {:suspended, acc, (fn () -> reduce_cont(list, acc, reducer) end)}\n\
      end\n\
    end";
    let toks = crate::parser::lexer::Lexer::new(src)
        .tokenize()
        .expect("lex");
    let prog = crate::parser::Parser::new(toks)
        .parse_program()
        .expect("parse");
    let mut t = crate::types::ConcreteTypes;
    let prog = crate::frontend::resolve::flatten_modules(&mut t, prog).expect("resolve");
    let module = crate::ir_lower::lower_program(&mut t, &prog, &crate::telemetry::NullTelemetry)
        .expect("lower");
    let matches = module
        .fns
        .iter()
        .filter(|f| f.name == "fn_clause_1")
        .map(|f| {
            let params = f.block(f.entry).params.len();
            let groups = module
                .function_correspondence
                .get(&f.id)
                .cloned()
                .unwrap_or_default();
            (f.id, params, groups)
        })
        .collect::<Vec<_>>();
    assert!(
        !matches.is_empty(),
        "expected at least one fn_clause_1, got names {:?}",
        module
            .fns
            .iter()
            .map(|f| f.name.clone())
            .collect::<Vec<_>>()
    );
    assert!(
        matches
            .iter()
            .any(|(_, params, groups)| *params == 5 && !groups.is_empty()),
        "expected a 5-param fn_clause_1 with correspondence, got {:?}",
        matches
    );
    assert!(
        matches.iter().any(|(_, params, groups)| {
            *params == 5
                && groups.iter().any(|group| {
                    group.occurrences.iter().any(|occ| {
                        matches!(
                            occ,
                            crate::specs::StructuralOccurrence::Param { param_index: 0, .. }
                        )
                    }) && group
                        .occurrences
                        .iter()
                        .any(|occ| matches!(occ, crate::specs::StructuralOccurrence::Result { .. }))
                })
        }),
        "expected a 5-param fn_clause_1 group to tie param 0 to result, got {:?}",
        matches
    );
}

// ---- fz-t1m.1.1 — protocol callback spec compatibility ----

/// An impl callback whose declared `@spec` is set-theoretically disjoint from
/// the protocol's declared callback spec (here: result `atom` vs `integer`) is
/// rejected during resolve.
#[test]
fn protocol_impl_callback_disjoint_spec_is_rejected() {
    let src = r#"
defprotocol P do
  @spec to_thing(t(a)) :: integer
  fn to_thing(value)
end

defimpl P, for: List do
  @spec to_thing(value) :: atom
  fn to_thing(value), do: :ok
end

fn main(), do: P.to_thing([1])
"#;
    let toks = crate::parser::lexer::Lexer::new(src)
        .tokenize()
        .expect("lex");
    let parsed = crate::parser::Parser::new(toks)
        .parse_program()
        .expect("parse");
    let mut t = crate::types::ConcreteTypes;
    let err = crate::frontend::resolve::flatten_modules(&mut t, parsed)
        .expect_err("disjoint callback result spec must be rejected");
    let crate::frontend::resolve::ResolveError::ProtocolError { msg, .. } = err else {
        panic!("expected ProtocolError, got {err:?}");
    };
    assert!(
        msg.contains("to_thing/1") && msg.contains("incompatible"),
        "unexpected message: {msg}"
    );
}

/// A compatible impl callback spec (result `integer`, matching the protocol)
/// resolves without error; free type variables in callback positions never
/// produce a false positive.
#[test]
fn protocol_impl_callback_compatible_spec_is_accepted() {
    let src = r#"
defprotocol P do
  @spec to_thing(t(a)) :: integer
  fn to_thing(value)
end

defimpl P, for: List do
  @spec to_thing(value) :: integer
  fn to_thing(value), do: 1
end

fn main(), do: P.to_thing([1])
"#;
    let toks = crate::parser::lexer::Lexer::new(src)
        .tokenize()
        .expect("lex");
    let parsed = crate::parser::Parser::new(toks)
        .parse_program()
        .expect("parse");
    let mut t = crate::types::ConcreteTypes;
    crate::frontend::resolve::flatten_modules(&mut t, parsed)
        .expect("compatible callback spec must resolve");
}

// ---- fz-t1m.1.3 — no-implementation diagnostic at dispatch ----

fn plan_protocol_src(
    src: &str,
) -> (
    crate::types::ConcreteTypes,
    crate::fz_ir::Module,
    crate::ir_planner::ModulePlan,
) {
    let toks = crate::parser::lexer::Lexer::new(src)
        .tokenize()
        .expect("lex");
    let parsed = crate::parser::Parser::new(toks)
        .parse_program()
        .expect("parse");
    let mut t = crate::types::ConcreteTypes;
    let resolved = crate::frontend::resolve::flatten_modules(&mut t, parsed).expect("resolve");
    let ir = crate::ir_lower::lower_program(&mut t, &resolved, &crate::telemetry::NullTelemetry)
        .expect("lower");
    let mt = plan_module(&mut t, &ir, &crate::telemetry::NullTelemetry);
    (t, ir, mt)
}

/// Calling a protocol callback on a receiver whose type is disjoint from every
/// implementing target emits a dedicated no-implementation diagnostic that names
/// the protocol, the receiver type, and the known implementors.
#[test]
fn protocol_call_on_unimplemented_receiver_emits_no_impl_diagnostic() {
    let src = r#"
defprotocol P do
  fn each(value)
end

defimpl P, for: List do
  fn each(value), do: value
end

fn main(), do: P.each(42)
"#;
    let (mut t, m, mt) = plan_protocol_src(src);
    let diags =
        crate::ir_planner::collect_diagnostics(&mut t, &m, &mt, &crate::telemetry::NullTelemetry);
    let d = diags
        .as_slice()
        .iter()
        .find(|d| d.code == crate::diag::codes::TYPE_PROTOCOL_NO_IMPL)
        .unwrap_or_else(|| {
            panic!(
                "expected a type/protocol-no-impl diagnostic; got: {:?}",
                diags
                    .as_slice()
                    .iter()
                    .map(|d| (d.code, &d.message))
                    .collect::<Vec<_>>(),
            )
        });
    assert!(
        d.message.contains("protocol `P`") && d.message.contains("receiver type"),
        "diag should name the protocol and receiver; got: {}",
        d.message
    );
    assert!(
        d.notes
            .iter()
            .any(|n| n.contains("known implementors") && n.contains("List")),
        "diag should list known implementors including List; got notes: {:?}",
        d.notes
    );
}

/// Calling the same protocol callback on a receiver the protocol does implement
/// (a list) emits no no-implementation diagnostic.
#[test]
fn protocol_call_on_implemented_receiver_emits_no_diagnostic() {
    let src = r#"
defprotocol P do
  fn each(value)
end

defimpl P, for: List do
  fn each(value), do: value
end

fn main(), do: P.each([1])
"#;
    let (mut t, m, mt) = plan_protocol_src(src);
    let diags =
        crate::ir_planner::collect_diagnostics(&mut t, &m, &mt, &crate::telemetry::NullTelemetry);
    assert!(
        !diags
            .as_slice()
            .iter()
            .any(|d| d.code == crate::diag::codes::TYPE_PROTOCOL_NO_IMPL),
        "no no-impl diag should fire when an impl matches; got: {:?}",
        diags
            .as_slice()
            .iter()
            .map(|d| (d.code, &d.message))
            .collect::<Vec<_>>(),
    );
}

// ---- fz-t1m.1.5 — closed-domain protocol switch dispatch ----

/// A protocol call whose receiver is a closed union of two implementing
/// targets (`7 | list(int)`, covered by `Integer` and `List`) is rewritten
/// from a single stub call into a `TypeTest`/`If` cascade with one direct
/// call per impl. After the rewrite the dispatching fn calls the concrete
/// impls — never the `__protocol__` stub.
#[test]
fn closed_union_protocol_receiver_rewrites_to_typetest_cascade() {
    let src = r#"
defprotocol Sizer do
  fn size(value)
end

defimpl Sizer, for: Integer do
  fn size(value), do: 1
end

defimpl Sizer, for: List do
  fn size(value), do: 2
end

fn describe(value), do: Sizer.size(value)

fn main() do
  case [7, [1, 2, 3]] do
    [a, b] -> describe(a) + describe(b)
    _ -> 0
  end
end
"#;
    let (mut t, mut m, mt) = plan_protocol_src(src);
    crate::ir_planner::rewrite_closed_union_protocol_dispatch(&mut t, &mut m, &mt);

    let describe = m.fn_by_name("describe").expect("describe fn");

    // The dispatch fn no longer calls a protocol stub directly.
    let still_calls_stub = describe.blocks.iter().any(|b| match &b.terminator {
        crate::fz_ir::Term::Call { callee, .. } | crate::fz_ir::Term::TailCall { callee, .. } => {
            m.protocol_call_targets.contains_key(callee)
        }
        _ => false,
    });
    assert!(
        !still_calls_stub,
        "after the rewrite, describe must not call the __protocol__ stub"
    );

    // It tests the receiver's type at least once...
    let has_type_test = describe.blocks.iter().any(|b| {
        b.stmts.iter().any(|crate::fz_ir::Stmt::Let(_, prim)| {
            matches!(prim, crate::fz_ir::Prim::TypeTest(..))
        })
    });
    assert!(
        has_type_test,
        "rewrite must emit a TypeTest on the receiver"
    );

    // ...and dispatches to two distinct concrete impl fns.
    let mut impl_callees: Vec<crate::fz_ir::FnId> = describe
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            crate::fz_ir::Term::Call { callee, .. }
            | crate::fz_ir::Term::TailCall { callee, .. } => Some(*callee),
            _ => None,
        })
        .collect();
    impl_callees.sort();
    impl_callees.dedup();
    assert_eq!(
        impl_callees.len(),
        2,
        "closed union over Integer and List must produce two direct-call arms; got {:?}",
        impl_callees
            .iter()
            .map(|id| &m.fn_by_id(*id).name)
            .collect::<Vec<_>>()
    );
}

/// A single-target receiver (a plain list, only `List` implements `Sizer`)
/// is left untouched — ordinary single dispatch, no cascade.
#[test]
fn single_target_protocol_receiver_is_not_rewritten() {
    let src = r#"
defprotocol Sizer do
  fn size(value)
end

defimpl Sizer, for: List do
  fn size(value), do: 2
end

fn describe(value), do: Sizer.size(value)

fn main(), do: describe([1, 2, 3])
"#;
    let (mut t, mut m, mt) = plan_protocol_src(src);
    let before = m.fn_by_name("describe").unwrap().blocks.len();
    crate::ir_planner::rewrite_closed_union_protocol_dispatch(&mut t, &mut m, &mt);
    let after = m.fn_by_name("describe").unwrap().blocks.len();
    assert_eq!(
        before, after,
        "a single-target receiver must not grow a switch cascade"
    );
}

// ---- fz-t1m.1.6 — open/erased protocol dispatch (cascade + fallthrough) ----

/// A receiver that overlaps some impls but is not fully covered — here
/// `integer | list(int) | atom`, where only `Integer` and `List` implement
/// `Sizer` (the atom is residual) — is rewritten into a cascade that tests
/// every implementing arm and falls through to the original stub for a value
/// matching none. The dispatch fn keeps a call to the `__protocol__` stub (the
/// fallthrough), unlike the fully-covered closed-union case.
#[test]
fn open_protocol_receiver_rewrites_to_cascade_with_stub_fallthrough() {
    let src = r#"
defprotocol Sizer do
  fn size(value)
end

defimpl Sizer, for: Integer do
  fn size(value), do: 1
end

defimpl Sizer, for: List do
  fn size(value), do: 2
end

fn describe(value), do: Sizer.size(value)

fn main() do
  case [7, [1, 2, 3], :other] do
    [a, b, c] -> describe(a) + describe(b)
    _ -> 0
  end
end
"#;
    let (mut t, mut m, mt) = plan_protocol_src(src);
    crate::ir_planner::rewrite_closed_union_protocol_dispatch(&mut t, &mut m, &mt);

    let describe = m.fn_by_name("describe").expect("describe fn");

    // Two distinct impl arms are emitted...
    let mut impl_callees: Vec<crate::fz_ir::FnId> = describe
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            crate::fz_ir::Term::Call { callee, .. }
            | crate::fz_ir::Term::TailCall { callee, .. } => {
                (!m.protocol_call_targets.contains_key(callee)).then_some(*callee)
            }
            _ => None,
        })
        .collect();
    impl_callees.sort();
    impl_callees.dedup();
    assert_eq!(
        impl_callees.len(),
        2,
        "Integer and List arms must be emitted; got {:?}",
        impl_callees
    );

    // ...and a stub fallthrough survives for the residual (atom) arm.
    let keeps_stub_fallthrough = describe.blocks.iter().any(|b| match &b.terminator {
        crate::fz_ir::Term::Call { callee, .. } | crate::fz_ir::Term::TailCall { callee, .. } => {
            m.protocol_call_targets.contains_key(callee)
        }
        _ => false,
    });
    assert!(
        keeps_stub_fallthrough,
        "an open receiver must keep the stub call as the no-match fallthrough"
    );
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
    // `TypeTest` guard; the planner's narrowing then pins the param to
    // `A::t` along the pass-branch entry block. Without the
    // annotation, the param would be `any` and the `.value` accessor
    // would fall through to the generic map-lookup result. The
    // top-level `main` exists only to seed the planner entry — without
    // a caller, `A.get/1` has no registered spec.
    let src = r#"
defmodule A do
  @type t :: opaque resource(integer)

  fn make(), do: make_resource(7, &dbg/1)
  fn get(h :: t), do: h.value
end

fn main() do
  h = A.make()
  A.get(h)
end
"#;
    let (mut t, m, mt) = pipeline(src, &crate::telemetry::NullTelemetry);
    let f = m.fn_by_name("A.get").expect("A.get exists post-lower");
    let ft = mt.any_spec_for(f.id).unwrap_or_else(|| {
        let keys: Vec<_> = mt.specs.keys().filter(|key| key.fn_id == f.id).collect();
        panic!("no spec for A.get/1; have keys: {:?}", keys);
    });
    // The fn body lowers `h.value` to a `Prim::MapGet(h, :value)`
    // (TypeTest dispatch wraps it in a few blocks). Find that stmt's
    // result var and check its inferred type — it must be a subtype
    // of integer once the planner reads `m.opaque_inners["A::t"]`.
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

#[test]
fn struct_field_projects_declared_underlying_tuple_slot() {
    let mut b = FnBuilder::new(FnId(0), "Range.first");
    let range = b.fresh_var();
    let entry = b.block(vec![range]);
    let first = b.let_(entry, Prim::StructField(range, "first".to_string()));
    b.set_terminator(entry, Term::Return(first));
    let mut m = build_module(vec![b.build()]);
    m.struct_schemas.insert(
        "Range".to_string(),
        vec!["first".to_string(), "last".to_string(), "step".to_string()],
    );
    let mut ct = crate::types::ConcreteTypes;
    let int = ct.int();
    let inner = ct.tuple(&[int.clone(), int.clone(), int]);
    m.opaque_inners
        .insert("impl-target::Range".to_string(), inner);

    let arg = ct.opaque_of("impl-target::Range");
    let ft = type_fn(&mut ct, &m.fns[0], &m, Some(&[arg]));
    let got = ft.vars.get(&first).expect("StructField result type");
    let int = ct.int();
    assert!(
        ct.is_subtype(got, &int),
        "Range.first field should type as integer, got `{}`",
        ct.display(got)
    );
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

    // Drive the planner under a narrow spec that pins `h` to A::t.
    let narrow_key_ty = vec![ct.opaque_of("A::t")];
    let ft = type_fn(&mut ct, &m.fns[0], &m, Some(&narrow_key_ty));
    // Register the spec so collect_diagnostics picks it up.
    let mut mt = crate::ir_planner::plan_module(&mut ct, &m, &crate::telemetry::NullTelemetry);
    mt.specs
        .insert(value_spec_key(FnId(0), key_tys(narrow_key_ty)), ft);

    let diags =
        crate::ir_planner::collect_diagnostics(&mut ct, &m, &mt, &crate::telemetry::NullTelemetry);
    let visibility = diags
        .as_slice()
        .iter()
        .find(|d| d.code == crate::diag::codes::TYPE_OPAQUE_VISIBILITY)
        .unwrap_or_else(|| {
            panic!(
                "expected a type/opaque-visibility diagnostic; got: {:?}",
                diags
                    .as_slice()
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
    let diags =
        crate::ir_planner::collect_diagnostics(&mut t, &m, &mt, &crate::telemetry::NullTelemetry);
    assert!(
        !diags
            .as_slice()
            .iter()
            .any(|d| d.code == crate::diag::codes::TYPE_OPAQUE_VISIBILITY),
        "no opaque-visibility diag should fire from inside the declaring module; got: {:?}",
        diags
            .as_slice()
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
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    let bs_t = fn_view(&mut t, &m, &mt, 0).vars.get(&bs).unwrap().clone();
    let str_t = t.str_t();
    assert!(
        t.is_equivalent(&bs_t, &str_t),
        "expected MakeBitstring to type as str_t(); got {}",
        t.display(&bs_t),
    );
}

// fz-axu.11 (L3) — string literals lower to a `utf8`-branded
// const bitstring through ir_lower. End-to-end shape: the planner
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
    let toks = crate::parser::lexer::Lexer::new(src)
        .tokenize()
        .expect("lex");
    let prog = crate::parser::Parser::new(toks)
        .parse_program()
        .expect("parse");
    let mut ct = crate::types::ConcreteTypes;
    let prog = crate::frontend::resolve::flatten_modules(&mut ct, prog).expect("resolve");
    let m = crate::ir_lower::lower_program(&mut ct, &prog, &crate::telemetry::NullTelemetry)
        .expect("lower");
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
    let mt = plan_module(&mut ct, &m, &crate::telemetry::NullTelemetry);
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
    let mt = plan_module(&mut ct, &m, &crate::telemetry::NullTelemetry);
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
    let mt = plan_module(&mut t, &m, &crate::telemetry::NullTelemetry);
    let bs_t = fn_view(&mut t, &m, &mt, 0).vars.get(&bs).unwrap().clone();
    let str_t = t.str_t();
    assert!(
        t.is_equivalent(&bs_t, &str_t),
        "expected ConstBitstring to type as str_t(); got {}",
        t.display(&bs_t),
    );
}

// ----- fz-l4c: planner rejects arithmetic on opaque-integer types -----

#[test]
fn opaque_arithmetic_pid_plus_int_rejected() {
    let src = "fn main(), do: self() + 1";
    let (mut t, m, mt) = pipeline(src, &crate::telemetry::NullTelemetry);
    let diags =
        crate::ir_planner::collect_diagnostics(&mut t, &m, &mt, &crate::telemetry::NullTelemetry);
    let d = diags
        .as_slice()
        .iter()
        .find(|d| d.code == crate::diag::codes::TYPE_OPAQUE_ARITHMETIC)
        .unwrap_or_else(|| {
            panic!(
                "expected a type/opaque-arithmetic diagnostic; got: {:?}",
                diags
                    .as_slice()
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
    let diags =
        crate::ir_planner::collect_diagnostics(&mut t, &m, &mt, &crate::telemetry::NullTelemetry);
    assert!(
        diags
            .as_slice()
            .iter()
            .any(|d| d.code == crate::diag::codes::TYPE_OPAQUE_ARITHMETIC),
        "expected type/opaque-arithmetic on make_ref() + 1; got: {:?}",
        diags
            .as_slice()
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
    let diags =
        crate::ir_planner::collect_diagnostics(&mut t, &m, &mt, &crate::telemetry::NullTelemetry);
    assert!(
        !diags
            .as_slice()
            .iter()
            .any(|d| d.code == crate::diag::codes::TYPE_OPAQUE_ARITHMETIC),
        "equality must not raise type/opaque-arithmetic; got: {:?}",
        diags
            .as_slice()
            .iter()
            .map(|d| (d.code, &d.message))
            .collect::<Vec<_>>(),
    );
}

#[test]
fn plain_int_arithmetic_still_passes() {
    let src = "fn main(), do: 1 + 1";
    let (mut t, m, mt) = pipeline(src, &crate::telemetry::NullTelemetry);
    let diags =
        crate::ir_planner::collect_diagnostics(&mut t, &m, &mt, &crate::telemetry::NullTelemetry);
    assert!(
        !diags
            .as_slice()
            .iter()
            .any(|d| d.code == crate::diag::codes::TYPE_OPAQUE_ARITHMETIC),
        "plain int arithmetic must not raise the diagnostic; got: {:?}",
        diags
            .as_slice()
            .iter()
            .map(|d| (d.code, &d.message))
            .collect::<Vec<_>>(),
    );
}

/// Compile `src` to IR and run `rewrite_known_target_closures` (devirtualize
/// + constant-closure value elimination), returning the rewritten module.
fn rewrite_closures(src: &str) -> Module {
    let fe = crate::frontend::compile_source(src.to_string(), "closures-test.fz".to_string())
        .unwrap_or_else(|e| panic!("frontend: {:?}", e.diagnostics));
    let mut working = fe.module.clone();
    let mut t = crate::types::ConcreteTypes;
    let caps = crate::ir_planner::plan_callable_capabilities(&mut t, &working);
    crate::ir_planner::rewrite_known_target_closures(&mut t, &mut working, &caps);
    working
}

fn count_make_closures_in_fns(m: &Module, names: &[&str]) -> usize {
    names
        .iter()
        .filter_map(|name| m.fn_by_name(name))
        .flat_map(|f| f.blocks.iter())
        .flat_map(|b| b.stmts.iter())
        .filter(|Stmt::Let(_, prim)| matches!(prim, Prim::MakeClosure(_, _, _)))
        .count()
}

fn fn_arity(m: &Module, name: &str) -> usize {
    let f = m.fn_by_name(name).expect("fn present");
    f.block(f.entry).params.len()
}

/// A module-wide-constant, zero-capture closure threaded through a recursive
/// HOF is erased entirely: the `MakeClosure` disappears and the threaded
/// parameter slot is removed from the HOF's arity. This is what frees
/// `Enum.sort`'s comparator from the lazy-continuation gate.
#[test]
fn rewrite_erases_threaded_constant_closure() {
    let src = "fn merge([], right, _s), do: right\n\
               fn merge(left, [], _s), do: left\n\
               fn merge([lh | lt], [rh | rt], s) do\n\
                 if s.(lh, rh) do\n\
                   [lh | merge(lt, [rh | rt], s)]\n\
                 else\n\
                   [rh | merge([lh | lt], rt, s)]\n\
                 end\n\
               end\n\
               fn main(), do: merge([1, 3], [2, 4], fn (a, b) -> a <= b end)";
    let after = rewrite_closures(src);
    assert_eq!(
        count_make_closures_in_fns(&after, &["main", "merge"]),
        0,
        "the constant comparator's MakeClosure must be erased"
    );
    assert_eq!(
        fn_arity(&after, "merge"),
        2,
        "merge's threaded comparator parameter must be removed (3 -> 2)"
    );
}

/// Two distinct lambdas flowing into the same HOF parameter make it
/// non-constant (`KnownFn` capabilities disagree across specs), so the closure value
/// is NOT erased — the static-closure machinery must still see it. Guards
/// against over-eager elimination.
#[test]
fn rewrite_keeps_non_constant_closure() {
    let src = "fn f(x), do: x + 1\n\
               fn g(x), do: x * 2\n\
               fn apply(h, x), do: h.(x)\n\
               fn main() do\n\
                 apply(f, 1)\n\
                 apply(g, 2)\n\
               end";
    let after = rewrite_closures(src);
    assert!(
        count_make_closures_in_fns(&after, &["main"]) >= 1,
        "a non-constant closure value must survive the rewrite"
    );
    assert_eq!(
        fn_arity(&after, "apply"),
        2,
        "apply's parameters must be untouched when its closure is non-constant"
    );
}

/// A zero-capture closure and a captured closure flowing through the same HOF
/// parameter disagree. Treating only `KnownFn` facts as evidence would rewrite
/// both call sites to the zero-capture target and silently drop the captured
/// closure's behavior.
#[test]
fn rewrite_keeps_known_fn_when_other_specs_have_captured_closure() {
    let src = "fn f(x), do: x + 1\n\
               fn apply(h, x), do: h.(x)\n\
               fn via_capture(n), do: apply(fn x -> x + n end, 2)\n\
               fn main() do\n\
                 apply(f, 1)\n\
                 via_capture(10)\n\
               end";
    let after = rewrite_closures(src);
    assert!(
        count_make_closures_in_fns(&after, &["via_capture"]) >= 1,
        "captured closure disagreement must keep a real closure value"
    );
    assert_eq!(
        fn_arity(&after, "apply"),
        2,
        "apply's callable parameter must remain when any spec carries captured closure state"
    );
}
