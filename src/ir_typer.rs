//! Flow-insensitive type inference over `fz_ir::Module`.
//!
//! Produces a `Var -> Descr` map per `FnIr`, walking blocks to fixed-point.
//! Block parameters join via union of incoming `Goto` args (the only IR
//! terminator that passes args; `If` carries none, and `Call`/`TailCall` route
//! to separate `FnIr`s via continuations). Entry-block params start at
//! `Descr::any()` — call-site narrowing arrives in fz-ul4.11.24.7.
//!
//! Consumers are not yet wired (per fz-ul4.11.24.2 scope). The result is
//! attached to `CompiledModule.types` and downstream tickets plug it into
//! ir_codegen (.11.24.4, .11.24.5) and exhaustiveness (.11.24.6). Pattern
//! narrowing on IR pattern ops lands in .11.24.3.

use crate::fz_ir::{
    BinOp, BuiltinId, BuiltinKind, Const, FnIr, Module, Prim, Stmt, Term, UnOp, Var, VecKindIr,
};
use crate::types::{Descr, MapKey};
use std::collections::HashMap;

/// Per-fn `Var -> Descr` map. Indexed by position in `Module.fns`, not by
/// `FnId.0` — see `type_module`.
pub type ModuleTypes = Vec<HashMap<Var, Descr>>;

pub fn type_module(m: &Module) -> ModuleTypes {
    m.fns.iter().map(|f| type_fn(f, m)).collect()
}

fn type_fn(f: &FnIr, m: &Module) -> HashMap<Var, Descr> {
    let mut types: HashMap<Var, Descr> = HashMap::new();

    // Entry-block params: fn parameters. Top until .11.24.7 narrows via
    // call-site observation. Non-entry block params start at `none` and grow
    // via Goto-arg union.
    for b in &f.blocks {
        let init = if b.id == f.entry { Descr::any() } else { Descr::none() };
        for &p in &b.params {
            types.insert(p, init.clone());
        }
    }

    loop {
        let mut changed = false;

        for b in &f.blocks {
            // Stmt-level: each Let var derives from its Prim under current map.
            for stmt in &b.stmts {
                let Stmt::Let(v, prim) = stmt;
                let new_t = type_prim(prim, &types, m);
                let old = types.get(v).cloned().unwrap_or_else(Descr::none);
                if !new_t.is_equiv(&old) {
                    types.insert(*v, new_t);
                    changed = true;
                }
            }

            // Block-param propagation via Goto. If terminators carry no args;
            // Call/TailCall continuations target separate FnIrs whose param
            // typing is the calling fn's frame's concern (.11.24.7).
            if let Term::Goto(target, args) = &b.terminator {
                let target_b = f.block(*target);
                for (i, &arg) in args.iter().enumerate() {
                    let Some(&param) = target_b.params.get(i) else { continue };
                    let arg_t = types.get(&arg).cloned().unwrap_or_else(Descr::any);
                    let param_t = types.get(&param).cloned().unwrap_or_else(Descr::none);
                    let unioned = param_t.union(&arg_t);
                    if !unioned.is_equiv(&param_t) {
                        types.insert(param, unioned);
                        changed = true;
                    }
                }
            }
        }

        if !changed { break; }
    }

    types
}

fn type_prim(prim: &Prim, types: &HashMap<Var, Descr>, m: &Module) -> Descr {
    match prim {
        Prim::Const(c) => type_const(c),

        Prim::BinOp(op, a, b) => {
            let at = lookup(types, *a);
            let bt = lookup(types, *b);
            type_binop(*op, &at, &bt)
        }
        Prim::UnOp(op, v) => {
            let vt = lookup(types, *v);
            match op {
                UnOp::Neg => numeric_result(&vt, &vt),
                UnOp::Not => Descr::bool_t(),
            }
        }

        Prim::MakeTuple(vs) => {
            let elems: Vec<Descr> = vs.iter().map(|v| lookup(types, *v)).collect();
            Descr::tuple_of(elems)
        }
        Prim::TupleField(_, _) => Descr::any(), // .11.24.3 narrows via tuple_projections

        Prim::MakeList(els, tail) => {
            let mut elem = Descr::none();
            for v in els { elem = elem.union(&lookup(types, *v)); }
            if let Some(t) = tail {
                let tt = lookup(types, *t);
                elem = elem.union(&crate::typer::list_element_type(&tt));
            }
            Descr::list_of(elem)
        }
        Prim::ListCons(h, t) => {
            let ht = lookup(types, *h);
            let tt = lookup(types, *t);
            Descr::list_of(ht.union(&crate::typer::list_element_type(&tt)))
        }
        Prim::ListHead(l) => crate::typer::list_element_type(&lookup(types, *l)),
        Prim::ListTail(l) => {
            let lt = lookup(types, *l);
            Descr::list_of(crate::typer::list_element_type(&lt))
        }
        Prim::ListIsNil(_) => Descr::bool_t(),

        Prim::MakeMap(entries) => {
            // If every key is a constant-derived MapKey, build a precise MapSig.
            // Otherwise fall back to map_top (the typer pass is flow-insensitive
            // here; a smarter pass could chase Var -> Const).
            let mut fields = std::collections::BTreeMap::new();
            let mut all_static = true;
            for (k, v) in entries {
                let vt = lookup(types, *v);
                match var_as_map_key(*k, types) {
                    Some(mk) => { fields.insert(mk, vt); }
                    None => { all_static = false; break; }
                }
            }
            if all_static && !entries.is_empty() {
                Descr::map_of(fields)
            } else if entries.is_empty() {
                Descr::map_of([])
            } else {
                Descr::map_top()
            }
        }
        Prim::MapUpdate(base, _) => lookup(types, *base),
        Prim::MapGet(_, _) => Descr::any().union(&Descr::nil()),

        Prim::MakeVec(kind, _) => match kind {
            VecKindIr::I64 => Descr::vec_i64(),
            VecKindIr::F64 => Descr::vec_f64(),
            VecKindIr::U8 => Descr::vec_u8(),
            VecKindIr::Bit => Descr::vec_bit(),
        },
        Prim::MakeBitstring(_) => Descr::vec_u8().union(&Descr::vec_bit()),

        Prim::MakeClosure(fn_id, _) => {
            // Arrow over the target fn's entry-block param count. Each arg is
            // Top; the return is Top until .11.24.7 hooks specialize_return.
            let callee = m.fn_by_id(*fn_id);
            let entry = callee.block(callee.entry);
            let arity = entry.params.len();
            let args: Vec<Descr> = std::iter::repeat_n(Descr::any(), arity).collect();
            Descr::arrow(args, Descr::any())
        }

        Prim::Builtin(bid, _) => type_builtin(*bid),

        // Reader and struct ops: conservative Top until later tickets refine.
        Prim::AllocStruct(_, _) => Descr::any(),
        Prim::BitReaderInit(_) => Descr::any(),
        Prim::BitReadField { .. } => Descr::any(),
        Prim::BitReaderDone(_) => Descr::bool_t(),
    }
}

fn type_const(c: &Const) -> Descr {
    match c {
        Const::Int(n) => Descr::int_lit(*n),
        Const::Float(f) => Descr::float_lit(*f),
        Const::Str(s) => Descr::str_lit(s.clone()),
        // Atoms are interned u32 in the IR. The typer cares only about
        // distinctness of singletons, so we tag the name with the id.
        Const::Atom(id) => Descr::atom_lit(format!("a{}", id)),
        Const::Nil => Descr::nil(),
        // true/false in fz are atoms, not a separate bool type — singleton
        // here mirrors what `Const::Atom` does for user atoms.
        Const::True => Descr::atom_lit("true"),
        Const::False => Descr::atom_lit("false"),
    }
}

fn type_binop(op: BinOp, a: &Descr, b: &Descr) -> Descr {
    use BinOp::*;
    match op {
        Add | Sub | Mul | Div | Mod => numeric_result(a, b),
        Eq | Neq | Lt | Le | Gt | Ge => Descr::bool_t(),
        And | Or => a.union(b),
    }
}

fn numeric_result(a: &Descr, b: &Descr) -> Descr {
    let int = Descr::int();
    let float = Descr::float();
    let both_int = a.is_subtype(&int) && b.is_subtype(&int);
    let both_float = a.is_subtype(&float) && b.is_subtype(&float);
    if both_int { int }
    else if both_float { float }
    else { int.union(&float) }
}

fn type_builtin(bid: BuiltinId) -> Descr {
    match BuiltinKind::from_id(bid) {
        Some(BuiltinKind::Print) => Descr::nil(),
        Some(BuiltinKind::Assert)
        | Some(BuiltinKind::AssertEq)
        | Some(BuiltinKind::AssertNeq) => Descr::nil(),
        Some(BuiltinKind::VecGet) => Descr::int().union(&Descr::float()),
        None => Descr::any(),
    }
}

fn lookup(types: &HashMap<Var, Descr>, v: Var) -> Descr {
    types.get(&v).cloned().unwrap_or_else(Descr::any)
}

/// If `v`'s Descr is a singleton literal convertible to a MapKey
/// (atom/int/str), return it. Used to construct precise MapSigs at MakeMap.
fn var_as_map_key(v: Var, types: &HashMap<Var, Descr>) -> Option<MapKey> {
    let d = types.get(&v)?;
    if !d.ints.cofinite && d.ints.set.len() == 1 {
        return Some(MapKey::Int(*d.ints.set.iter().next().unwrap()));
    }
    if !d.atoms.cofinite && d.atoms.set.len() == 1 {
        return Some(MapKey::Atom(d.atoms.set.iter().next().unwrap().clone()));
    }
    if !d.strs.cofinite && d.strs.set.len() == 1 {
        return Some(MapKey::Str(d.strs.set.iter().next().unwrap().clone()));
    }
    None
}

// ----------------------------------------------------------------------
// Tests
// ----------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{
        BinOp, Block, BlockId, Const, FnBuilder, FnId, ModuleBuilder, Prim, Term, Var,
    };

    fn build_module(fns: Vec<crate::fz_ir::FnIr>) -> Module {
        let mut mb = ModuleBuilder::new();
        for f in fns { mb.add_fn(f); }
        mb.build()
    }

    #[test]
    fn const_int_typed_as_singleton() {
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let v = b.let_(entry, Prim::Const(Const::Int(42)));
        b.set_terminator(entry, Term::Halt(v));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        assert!(mt[0].get(&v).unwrap().is_equiv(&Descr::int_lit(42)));
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
        // x is `any` (entry param), so add result is conservative int|float.
        let sum_t = mt[0].get(&sum).cloned().unwrap();
        assert!(sum_t.is_equiv(&Descr::int().union(&Descr::float())),
            "got {}", sum_t);
    }

    #[test]
    fn add_two_int_lits_yields_int_top() {
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let a = b.let_(entry, Prim::Const(Const::Int(1)));
        let bv = b.let_(entry, Prim::Const(Const::Int(2)));
        let sum = b.let_(entry, Prim::BinOp(BinOp::Add, a, bv));
        b.set_terminator(entry, Term::Return(sum));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        // Both operands subtype of int — result narrows to int_top
        // (not a singleton; the typer doesn't constant-fold).
        assert!(mt[0].get(&sum).unwrap().is_equiv(&Descr::int()));
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
        let lt = mt[0].get(&l).cloned().unwrap();
        // Element type is the union of the three int literals (subtype of int).
        let elem = crate::typer::list_element_type(&lt);
        assert!(elem.is_subtype(&Descr::int()),
            "list elem should be int-subtype: {}", elem);
        assert!(!elem.is_empty(), "list elem is empty");
    }

    #[test]
    fn make_tuple_preserves_elem_descrs() {
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let one = b.let_(entry, Prim::Const(Const::Int(1)));
        let ok = b.let_(entry, Prim::Const(Const::Atom(7)));
        let t = b.let_(entry, Prim::MakeTuple(vec![one, ok]));
        b.set_terminator(entry, Term::Return(t));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        let tt = mt[0].get(&t).cloned().unwrap();
        let expected = Descr::tuple_of([Descr::int_lit(1), Descr::atom_lit("a7")]);
        assert!(tt.is_equiv(&expected), "got {}, expected {}", tt, expected);
    }

    #[test]
    fn make_map_with_static_keys_is_precise() {
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let k = b.let_(entry, Prim::Const(Const::Atom(1))); // singleton :a1
        let v = b.let_(entry, Prim::Const(Const::Int(5)));
        let mp = b.let_(entry, Prim::MakeMap(vec![(k, v)]));
        b.set_terminator(entry, Term::Return(mp));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        let mt_d = mt[0].get(&mp).cloned().unwrap();
        let expected = Descr::map_of([(MapKey::Atom("a1".into()), Descr::int_lit(5))]);
        assert!(mt_d.is_equiv(&expected), "got {}, expected {}", mt_d, expected);
    }

    #[test]
    fn vec_lit_typed_per_kind() {
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let one = b.let_(entry, Prim::Const(Const::Int(1)));
        let v = b.let_(entry, Prim::MakeVec(VecKindIr::I64, vec![one]));
        b.set_terminator(entry, Term::Return(v));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        assert!(mt[0].get(&v).unwrap().is_equiv(&Descr::vec_i64()));
    }

    #[test]
    fn goto_joins_param_types_across_predecessors() {
        // Build: entry forks to bb1 or bb2 via If; both Goto bb3 with
        // different-typed args. bb3's param Descr must be the union.
        let mut b = FnBuilder::new(FnId(0), "join");
        let entry = b.block(vec![]);
        let zero = b.let_(entry, Prim::Const(Const::Int(0)));
        // Use the int-literal as the If discriminant. The typer doesn't model
        // truthiness yet — that's fine for testing the join.
        let bb1 = b.block(vec![]);
        let bb2 = b.block(vec![]);
        let joined = Var(99); // pre-pick the param id
        let bb3 = b.block(vec![joined]);
        b.set_terminator(entry, Term::If(zero, bb1, bb2));

        let one = b.let_(bb1, Prim::Const(Const::Int(1)));
        b.set_terminator(bb1, Term::Goto(bb3, vec![one]));

        let two = b.let_(bb2, Prim::Const(Const::Int(2)));
        b.set_terminator(bb2, Term::Goto(bb3, vec![two]));

        b.set_terminator(bb3, Term::Return(joined));

        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        let join_t = mt[0].get(&joined).cloned().unwrap();
        let expected = Descr::int_lit(1).union(&Descr::int_lit(2));
        assert!(join_t.is_equiv(&expected),
            "join Descr should be int_lit(1) ∪ int_lit(2): got {}", join_t);

        // Sanity: bb1/bb2/bb3 referenced to silence dead-code unused warnings.
        let _ = (bb1, bb2, bb3, Block { id: BlockId(0), params: vec![], stmts: vec![], terminator: Term::Halt(Var(0)) });
    }

    #[test]
    fn entry_block_params_are_top() {
        let mut b = FnBuilder::new(FnId(0), "id");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        b.set_terminator(entry, Term::Return(x));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        assert!(mt[0].get(&x).unwrap().is_equiv(&Descr::any()));
    }

    #[test]
    fn make_closure_typed_as_arrow_of_callee_arity() {
        // Callee: fn add1(n) — arity 1.
        let mut b1 = FnBuilder::new(FnId(0), "add1");
        let n = b1.fresh_var();
        let e1 = b1.block(vec![n]);
        b1.set_terminator(e1, Term::Return(n));

        // Caller: makes a closure referring to add1.
        let mut b2 = FnBuilder::new(FnId(1), "caller");
        let e2 = b2.block(vec![]);
        let c = b2.let_(e2, Prim::MakeClosure(FnId(0), vec![]));
        b2.set_terminator(e2, Term::Return(c));

        let m = build_module(vec![b1.build(), b2.build()]);
        let mt = type_module(&m);
        let ct = mt[1].get(&c).cloned().unwrap();
        let expected = Descr::arrow([Descr::any()], Descr::any());
        assert!(ct.is_equiv(&expected), "got {}, expected {}", ct, expected);
    }
}
