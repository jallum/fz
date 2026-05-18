//! fz-jg5.4 (RED.3) — Reducer pass scaffold (single-clause inline).
//!
//! A `Module → Module` pass that walks each function, folds literals
//! into Var environments, and rewrites calls whose return value is
//! statically known.
//!
//! Scope at RED.3:
//! - Fold every `Prim` via `reducer::fold_prim`. When a Var has a
//!   scalar-literal Descr, record it.
//! - Fold `Term::If(cond, T, E)` when `cond` is a bool literal.
//! - Rewrite `Term::TailCall(callee, args)` to `Term::Return(lit)` when
//!   the callee is a single-block, no-inner-call fn AND all args have
//!   scalar-literal Descrs that walk to a scalar-literal return.
//! - Rewrite `Term::Call(callee, args, cont)` to a `Term::TailCall(cont,
//!   [lit, ...captures])` under the same conditions.
//!
//! Out of scope (lands in later RED tickets):
//! - Recursive call reduction (RED.4).
//! - Closure_lit reduction (RED.5).
//! - Tuple / list return values (need MakeTuple / cons rewriting).

use crate::fz_ir::{Block, BlockId, Const, FnId, FnIr, Module, Prim, Stmt, Term, Var};
use crate::reducer::{
    as_atom_lit, as_bool_lit, as_float_lit, as_int_lit, as_str_lit, fold_prim, is_literal,
    is_nil_only,
};
use crate::types::Descr;
use std::collections::HashMap;

/// Helper: get a `&mut Block` by id within an `FnIr`. FnIr exposes
/// `block(&self)` but not the mutable variant — fz_ir's `block_mut` is
/// private to `FnBuilder`. Inline the lookup here.
fn block_mut(f: &mut FnIr, id: BlockId) -> &mut Block {
    f.blocks
        .iter_mut()
        .find(|b| b.id == id)
        .expect("unknown block")
}

/// Allocate a fresh `Var` for `f` whose id exceeds every existing Var in
/// the fn body. Mirrors the `max_var + 1` pattern used by ir_inline.
fn fresh_var(f: &FnIr) -> Var {
    let mut m: u32 = 0;
    for b in &f.blocks {
        for p in &b.params {
            m = m.max(p.0);
        }
        for stmt in &b.stmts {
            let Stmt::Let(v, _) = stmt;
            m = m.max(v.0);
        }
    }
    Var(m + 1)
}

/// Reduce every function in `m`. Idempotent: running twice is the same
/// as running once (within the limits of v1's single-callsite scope).
pub fn reduce_module(m: &mut Module) {
    let fn_ids: Vec<FnId> = m.fns.iter().map(|f| f.id).collect();
    // Single sweep: each fn's body is reduced in place. RED.3 does not
    // iterate to a fixpoint across fns; later tickets may.
    for fid in fn_ids {
        reduce_fn(m, fid);
    }
}

fn reduce_fn(m: &mut Module, fid: FnId) {
    let Some(&fn_idx) = m.fn_idx.get(&fid) else {
        return;
    };
    let block_ids: Vec<BlockId> = m.fns[fn_idx].blocks.iter().map(|b| b.id).collect();
    for bid in block_ids {
        reduce_block(m, fn_idx, bid);
    }
}

fn reduce_block(m: &mut Module, fn_idx: usize, bid: BlockId) {
    // Build a per-block env of Var → literal Descr by folding each stmt.
    let mut env: HashMap<Var, Descr> = HashMap::new();
    let atom_names = m.atom_names.clone();
    {
        let block = m.fns[fn_idx].block(bid);
        for stmt in &block.stmts {
            let Stmt::Let(v, prim) = stmt;
            if let Some(d) = fold_prim(prim, &env, &atom_names) {
                env.insert(*v, d);
            }
        }
    }

    // Now consider the terminator.
    let term = m.fns[fn_idx].block(bid).terminator.clone();
    let new_term = reduce_terminator(m, fn_idx, bid, &term, &env);
    if let Some(nt) = new_term {
        block_mut(&mut m.fns[fn_idx], bid).terminator = nt;
    }
}

fn reduce_terminator(
    m: &mut Module,
    fn_idx: usize,
    bid: BlockId,
    term: &Term,
    env: &HashMap<Var, Descr>,
) -> Option<Term> {
    match term {
        // fz-jg5.4: if-fold (named explicit rule per FINDINGS.md).
        Term::If(cond, t, e) => {
            let cd = env.get(cond)?;
            let b = as_bool_lit(cd)?;
            Some(Term::Goto(if b { *t } else { *e }, vec![]))
        }
        Term::TailCall { callee, args, .. } => {
            let lit = try_reduce_call(m, *callee, args, env)?;
            let new_var = fresh_var(&m.fns[fn_idx]);
            let const_val = literal_to_const(&lit, m)?;
            block_mut(&mut m.fns[fn_idx], bid)
                .stmts
                .push(Stmt::Let(new_var, Prim::Const(const_val)));
            Some(Term::Return(new_var))
        }
        Term::Call {
            callee,
            args,
            continuation,
        } => {
            let lit = try_reduce_call(m, *callee, args, env)?;
            let new_var = fresh_var(&m.fns[fn_idx]);
            let const_val = literal_to_const(&lit, m)?;
            block_mut(&mut m.fns[fn_idx], bid)
                .stmts
                .push(Stmt::Let(new_var, Prim::Const(const_val)));
            let mut tail_args = vec![new_var];
            tail_args.extend(continuation.captured.iter().copied());
            Some(Term::TailCall {
                callee: continuation.fn_id,
                args: tail_args,
                is_back_edge: false,
            })
        }
        _ => None,
    }
}

/// Try to compute the literal return of `callee(args)` under the caller's
/// `env`. Returns `Some(literal_descr)` on success. Restricted in RED.3 to:
///   - single block
///   - terminator is `Term::Return`
///   - no Prim::Call / Prim::Extern in stmts (no inner calls)
///   - all args resolve to literal Descrs in `env`
///   - every stmt's Prim folds via `fold_prim`
///   - returned Var has a scalar-literal Descr (Tuple/List defer to later
///     tickets that handle structural literals)
fn try_reduce_call(
    m: &Module,
    callee: FnId,
    args: &[Var],
    env: &HashMap<Var, Descr>,
) -> Option<Descr> {
    let callee_fn: &FnIr = m.fn_by_id(callee);
    if callee_fn.blocks.len() != 1 {
        return None;
    }
    let block: &Block = &callee_fn.blocks[0];
    if !matches!(block.terminator, Term::Return(_)) {
        return None;
    }
    // Reject any stmt that has a side-effecting / call-like prim.
    for stmt in &block.stmts {
        let Stmt::Let(_, prim) = stmt;
        if matches!(
            prim,
            Prim::Extern(..)
                | Prim::MakeMap(..)
                | Prim::MapUpdate(..)
                | Prim::MakeBitstring(..)
                | Prim::BitReaderInit(..)
                | Prim::BitReadField { .. }
                | Prim::BitReaderDone(..)
                | Prim::AllocStruct(..)
        ) {
            return None;
        }
    }
    // Build a callee-local env from arg Descrs.
    let entry = callee_fn.block(callee_fn.entry);
    if entry.params.len() != args.len() {
        return None;
    }
    let mut callee_env: HashMap<Var, Descr> = HashMap::new();
    for (p, a) in entry.params.iter().zip(args.iter()) {
        let d = env.get(a)?.clone();
        if !is_scalar_literal(&d) {
            return None;
        }
        callee_env.insert(*p, d);
    }
    // Fold every stmt.
    for stmt in &block.stmts {
        let Stmt::Let(v, prim) = stmt;
        let d = fold_prim(prim, &callee_env, &m.atom_names)?;
        callee_env.insert(*v, d);
    }
    let Term::Return(rv) = &block.terminator else {
        return None;
    };
    let d = callee_env.get(rv)?.clone();
    if is_scalar_literal(&d) { Some(d) } else { None }
}

/// Scalar-literal predicate. Tuples/lists/closure_lits are out of scope
/// for RED.3 because rewriting a Call to a tuple result requires inserting
/// `MakeTuple` of sub-Const lets in the caller; that lands in a follow-on.
fn is_scalar_literal(d: &Descr) -> bool {
    if !is_literal(d) {
        return false;
    }
    // Tuple / closure_lit literals are "structural" — defer.
    if d.tuples.iter().any(|c| !c.pos.is_empty())
        || d.funcs.iter().any(|c| !c.pos.is_empty())
    {
        return false;
    }
    true
}

/// Convert a scalar-literal Descr back to a `Const`. Atoms are interned in
/// `m.atom_names`, allocating a new slot if necessary.
fn literal_to_const(d: &Descr, m: &mut Module) -> Option<Const> {
    if let Some(n) = as_int_lit(d) {
        return Some(Const::Int(n));
    }
    if let Some(fb) = as_float_lit(d) {
        return Some(Const::Float(fb.get()));
    }
    if is_nil_only(d) {
        return Some(Const::Nil);
    }
    if let Some(b) = as_bool_lit(d) {
        return Some(if b { Const::True } else { Const::False });
    }
    if let Some(name) = as_atom_lit(d) {
        let id = match m.atom_names.iter().position(|n| n == name) {
            Some(i) => i as u32,
            None => {
                let i = m.atom_names.len() as u32;
                m.atom_names.push(name.to_string());
                i
            }
        };
        return Some(Const::Atom(id));
    }
    if let Some(s) = as_str_lit(d) {
        return Some(Const::Str(s.to_string()));
    }
    None
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{BinOp, Const, FnBuilder, FnId, ModuleBuilder, Prim, Term};

    /// Build `fn id(x), do: x` and a `main()` that calls `id(42)`.
    /// After reduction, the TailCall in main should become a Return of 42.
    #[test]
    fn reduces_identity_call_with_int_literal() {
        let mut id_b = FnBuilder::new(FnId(0), "id");
        let x = id_b.fresh_var();
        let entry = id_b.block(vec![x]);
        id_b.set_terminator(entry, Term::Return(x));

        let mut main_b = FnBuilder::new(FnId(1), "main");
        let m_entry = main_b.block(vec![]);
        let c42 = main_b.let_(m_entry, Prim::Const(Const::Int(42)));
        main_b.set_terminator(
            m_entry,
            Term::TailCall {
                callee: FnId(0),
                args: vec![c42],
                is_back_edge: false,
            },
        );

        let mut mb = ModuleBuilder::new();
        mb.add_fn(id_b.build());
        mb.add_fn(main_b.build());
        let mut m = mb.build();
        reduce_module(&mut m);

        // main's terminator should now be Return of a freshly bound int_lit(42).
        let main_fn = m.fns.iter().find(|f| f.name == "main").unwrap();
        let block = &main_fn.blocks[0];
        match &block.terminator {
            Term::Return(v) => {
                // Find the stmt that bound `v`.
                let bound = block
                    .stmts
                    .iter()
                    .find_map(|Stmt::Let(bv, prim)| if bv == v { Some(prim) } else { None });
                match bound {
                    Some(Prim::Const(Const::Int(n))) => assert_eq!(*n, 42),
                    other => panic!("expected Const(Int(42)), got {:?}", other),
                }
            }
            other => panic!("expected Return, got {:?}", other),
        }
    }

    /// `fn double(x), do: x * 2` called with `Const(Int(21))`: should reduce
    /// to Return of 42.
    #[test]
    fn reduces_double_with_int_literal() {
        let mut d_b = FnBuilder::new(FnId(0), "double");
        let x = d_b.fresh_var();
        let entry = d_b.block(vec![x]);
        let c2 = d_b.let_(entry, Prim::Const(Const::Int(2)));
        let product = d_b.let_(entry, Prim::BinOp(BinOp::Mul, x, c2));
        d_b.set_terminator(entry, Term::Return(product));

        let mut main_b = FnBuilder::new(FnId(1), "main");
        let m_entry = main_b.block(vec![]);
        let c21 = main_b.let_(m_entry, Prim::Const(Const::Int(21)));
        main_b.set_terminator(
            m_entry,
            Term::TailCall {
                callee: FnId(0),
                args: vec![c21],
                is_back_edge: false,
            },
        );

        let mut mb = ModuleBuilder::new();
        mb.add_fn(d_b.build());
        mb.add_fn(main_b.build());
        let mut m = mb.build();
        reduce_module(&mut m);

        let main_fn = m.fns.iter().find(|f| f.name == "main").unwrap();
        let block = &main_fn.blocks[0];
        match &block.terminator {
            Term::Return(v) => {
                let bound = block
                    .stmts
                    .iter()
                    .find_map(|Stmt::Let(bv, prim)| if bv == v { Some(prim) } else { None });
                match bound {
                    Some(Prim::Const(Const::Int(n))) => assert_eq!(*n, 42),
                    other => panic!("expected Const(Int(42)), got {:?}", other),
                }
            }
            other => panic!("expected Return, got {:?}", other),
        }
    }

    /// A call whose argument is NOT a literal stays as a TailCall.
    #[test]
    fn does_not_reduce_call_with_opaque_arg() {
        let mut id_b = FnBuilder::new(FnId(0), "id");
        let x = id_b.fresh_var();
        let entry = id_b.block(vec![x]);
        id_b.set_terminator(entry, Term::Return(x));

        let mut main_b = FnBuilder::new(FnId(1), "main");
        let p = main_b.fresh_var();
        let m_entry = main_b.block(vec![p]); // main(p) — p is opaque
        main_b.set_terminator(
            m_entry,
            Term::TailCall {
                callee: FnId(0),
                args: vec![p],
                is_back_edge: false,
            },
        );

        let mut mb = ModuleBuilder::new();
        mb.add_fn(id_b.build());
        mb.add_fn(main_b.build());
        let mut m = mb.build();
        reduce_module(&mut m);

        let main_fn = m.fns.iter().find(|f| f.name == "main").unwrap();
        match &main_fn.blocks[0].terminator {
            Term::TailCall { callee, .. } => assert_eq!(callee.0, 0),
            other => panic!("expected unchanged TailCall, got {:?}", other),
        }
    }

    /// `Term::If(cond, T, E)` with cond bound to Const(True) → Goto(T).
    #[test]
    fn folds_if_on_literal_true_to_goto() {
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let t_blk = b.block(vec![]);
        let e_blk = b.block(vec![]);
        let cond = b.let_(entry, Prim::Const(Const::True));
        b.set_terminator(entry, Term::If(cond, t_blk, e_blk));
        let nil = b.let_(t_blk, Prim::Const(Const::Nil));
        b.set_terminator(t_blk, Term::Return(nil));
        let nil2 = b.let_(e_blk, Prim::Const(Const::Nil));
        b.set_terminator(e_blk, Term::Return(nil2));

        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        let mut m = mb.build();
        reduce_module(&mut m);

        match &m.fns[0].block(entry).terminator {
            Term::Goto(tgt, args) if *tgt == t_blk && args.is_empty() => {}
            other => panic!("expected Goto(t_blk, []), got {:?}", other),
        }
    }

    /// A callee that itself has a Call in its body is NOT reducible at RED.3.
    #[test]
    fn does_not_reduce_callee_with_inner_call() {
        // f(x) = id(x) — body has a TailCall, so RED.3 should NOT fold it.
        let mut id_b = FnBuilder::new(FnId(0), "id");
        let x_id = id_b.fresh_var();
        let id_entry = id_b.block(vec![x_id]);
        id_b.set_terminator(id_entry, Term::Return(x_id));

        let mut f_b = FnBuilder::new(FnId(1), "f");
        let x_f = f_b.fresh_var();
        let f_entry = f_b.block(vec![x_f]);
        f_b.set_terminator(
            f_entry,
            Term::TailCall {
                callee: FnId(0),
                args: vec![x_f],
                is_back_edge: false,
            },
        );

        let mut main_b = FnBuilder::new(FnId(2), "main");
        let m_entry = main_b.block(vec![]);
        let c5 = main_b.let_(m_entry, Prim::Const(Const::Int(5)));
        main_b.set_terminator(
            m_entry,
            Term::TailCall {
                callee: FnId(1),
                args: vec![c5],
                is_back_edge: false,
            },
        );

        let mut mb = ModuleBuilder::new();
        mb.add_fn(id_b.build());
        mb.add_fn(f_b.build());
        mb.add_fn(main_b.build());
        let mut m = mb.build();
        reduce_module(&mut m);

        // main should still TailCall f (RED.3 doesn't fold across calls).
        let main_fn = m.fns.iter().find(|f| f.name == "main").unwrap();
        match &main_fn.blocks[0].terminator {
            Term::TailCall { callee, .. } => assert_eq!(callee.0, 1),
            other => panic!("expected unchanged TailCall to f, got {:?}", other),
        }
    }
}
