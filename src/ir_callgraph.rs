//! Static call-graph utilities over `fz_ir::Module`.
//!
//! One source of truth for "what counts as a call edge." Consumers:
//! ir_typer (SCC analysis for bottom-up spec discovery), and
//! pattern_check's survivor gate (reachable-from-roots BFS).
//!
//! Reachability is a property of the call graph, not the type lattice.
//! `reachable_fns` is a pure forward BFS — no type information consumed.

use crate::fz_ir::{FnId, Module, Prim, Stmt, Term};
use crate::types_seam::{Ty, Types};
use std::collections::{HashMap, HashSet};

/// Build the static call graph for the module.
///
/// Edges captured:
///   - direct `Term::Call` / `Term::TailCall` callee
///   - continuation `fn_id` from `Term::Call` / `Term::CallClosure` /
///     `Term::Receive`
///   - `Prim::MakeClosure(fn_id, ...)` target lambda
///
/// Edges skipped: `Term::Return` / `Term::Halt` (no static edge),
/// unresolved `CallClosure` / `TailCallClosure` targets (dynamic
/// dispatch — closure target is handled separately via MakeClosure
/// edges, which mark every fn that could be reached through opaque
/// dispatch).
pub fn build_call_graph(m: &Module) -> HashMap<FnId, HashSet<FnId>> {
    let mut g: HashMap<FnId, HashSet<FnId>> = HashMap::new();
    for f in &m.fns {
        let edges = g.entry(f.id).or_default();
        for b in &f.blocks {
            for stmt in &b.stmts {
                let Stmt::Let(_, prim) = stmt;
                if let Prim::MakeClosure(_, lam_fn_id, _) = prim {
                    edges.insert(*lam_fn_id);
                }
            }
            match &b.terminator {
                Term::Call {
                    ident: _,
                    callee,
                    continuation,
                    ..
                } => {
                    edges.insert(*callee);
                    edges.insert(continuation.fn_id);
                }
                Term::TailCall { callee, .. } => {
                    edges.insert(*callee);
                }
                Term::CallClosure { continuation, .. } => {
                    edges.insert(continuation.fn_id);
                }
                Term::TailCallClosure { .. } => {}
                Term::Receive {
                    continuation,
                    ident: _,
                } => {
                    edges.insert(continuation.fn_id);
                }
                // fz-70q.3 — clause body / guard / after fns reached via
                // selective-receive dispatch (matcher hit → trampoline).
                // Same shape as the Receive cont edge: backends need
                // them in the spec discovery + reachability graph or
                // codegen never sees a body FuncId.
                Term::ReceiveMatched { clauses, after, .. } => {
                    for c in clauses {
                        edges.insert(c.body);
                        if let Some(g) = c.guard {
                            edges.insert(g);
                        }
                    }
                    if let Some(a) = after {
                        edges.insert(a.body);
                    }
                }
                _ => {}
            }
        }
    }
    g
}

/// Root set for forward reachability: `main` seeded with an any-keyed
/// arg vector. Matches what the typer's worklist uses to begin spec
/// discovery, so reachability questions answered here line up with
/// the typer's notion of which fns are "entered" from program start.
pub fn entry_seeds<T: Types<Ty = Ty>>(t: &mut T, m: &Module) -> Vec<(FnId, Vec<Ty>)> {
    let mut seeds = Vec::new();
    if let Some(main) = m.fns.iter().find(|f| f.name == "main") {
        let n_params = main.block(main.entry).params.len();
        seeds.push((main.id, t.any_vec(n_params)));
    }
    seeds
}

/// Set of FnIds forward-reachable from `entry_seeds` over
/// `build_call_graph`. Pure call-graph BFS — no types consumed.
///
/// Use this when you want to ask "after reduction, which fns still
/// have call paths leading to them from program entry?" — e.g. the
/// pattern-check survivor gate.
///
/// Distinct from `ir_typer::reachable_specs(..)`, which is a
/// SpecId-level analysis used by codegen for trap-stub gating.
pub fn reachable_fns<T: Types<Ty = Ty>>(t: &mut T, m: &Module) -> HashSet<FnId> {
    let graph = build_call_graph(m);
    let mut reached: HashSet<FnId> = HashSet::new();
    let mut work: Vec<FnId> = Vec::new();
    for (fid, _) in entry_seeds(t, m) {
        if reached.insert(fid) {
            work.push(fid);
        }
    }
    while let Some(v) = work.pop() {
        if let Some(succs) = graph.get(&v) {
            for &w in succs {
                if reached.insert(w) {
                    work.push(w);
                }
            }
        }
    }
    reached
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{Cont, FnBuilder, FnId, Module, Prim, Term, Var};

    fn finish(builders: Vec<FnBuilder>) -> Module {
        let mut m = Module::new();
        for (idx, b) in builders.into_iter().enumerate() {
            let f = b.build();
            m.fn_idx.insert(f.id, idx);
            m.fns.push(f);
        }
        m
    }

    fn fn_halting(id: u32, name: &str) -> FnBuilder {
        let mut b = FnBuilder::new(FnId(id), name);
        let v0 = b.fresh_var();
        let entry = b.block(vec![]);
        // Halt needs *some* Var; use a fresh one bound to nothing.
        // FnBuilder::block initialises the terminator to Halt(Var(0)),
        // which is fine as a placeholder for tests that don't care
        // about the halted value.
        let _ = v0;
        b.set_terminator(entry, Term::Halt(Var(0)));
        b
    }

    fn fn_tail_calling(id: u32, name: &str, target: u32) -> FnBuilder {
        let mut b = FnBuilder::new(FnId(id), name);
        let entry = b.block(vec![]);
        b.set_terminator(
            entry,
            Term::TailCall {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee: FnId(target),
                args: vec![],
                is_back_edge: false,
            },
        );
        b
    }

    fn reach(m: &Module) -> HashSet<FnId> {
        let mut t = crate::types_seam::ConcreteTypes;
        reachable_fns(&mut t, m)
    }

    #[test]
    fn isolated_fn_is_reachable_when_it_is_main() {
        let m = finish(vec![fn_halting(0, "main")]);
        let r = reach(&m);
        assert!(r.contains(&FnId(0)));
        assert_eq!(r.len(), 1);
    }

    #[test]
    fn orphan_fn_excluded() {
        let m = finish(vec![fn_halting(0, "main"), fn_halting(1, "orphan")]);
        let r = reach(&m);
        assert!(r.contains(&FnId(0)));
        assert!(!r.contains(&FnId(1)));
    }

    #[test]
    fn tail_call_edge_followed() {
        let m = finish(vec![fn_tail_calling(0, "main", 1), fn_halting(1, "callee")]);
        let r = reach(&m);
        assert!(r.contains(&FnId(0)));
        assert!(r.contains(&FnId(1)));
    }

    #[test]
    fn call_continuation_edge_followed() {
        let mut main_b = FnBuilder::new(FnId(0), "main");
        let entry = main_b.block(vec![]);
        main_b.set_terminator(
            entry,
            Term::Call {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee: FnId(1),
                args: vec![],
                continuation: Cont {
                    fn_id: FnId(2),
                    captured: vec![],
                },
            },
        );
        let m = finish(vec![main_b, fn_halting(1, "callee"), fn_halting(2, "cont")]);
        let r = reach(&m);
        assert!(r.contains(&FnId(1)));
        assert!(r.contains(&FnId(2)));
    }

    #[test]
    fn make_closure_edge_followed() {
        let mut main_b = FnBuilder::new(FnId(0), "main");
        let entry = main_b.block(vec![]);
        main_b.let_(
            entry,
            Prim::MakeClosure(crate::fz_ir::CallsiteIdent::synthetic(), FnId(1), vec![]),
        );
        main_b.set_terminator(entry, Term::Halt(Var(0)));
        let m = finish(vec![main_b, fn_halting(1, "lambda")]);
        let r = reach(&m);
        assert!(r.contains(&FnId(1)));
    }

    #[test]
    fn recursive_cycle_terminates() {
        let m = finish(vec![
            fn_tail_calling(0, "main", 1),
            fn_tail_calling(1, "a", 0),
        ]);
        let r = reach(&m);
        assert_eq!(r.len(), 2);
        assert!(r.contains(&FnId(0)));
        assert!(r.contains(&FnId(1)));
    }

    #[test]
    fn no_main_yields_empty() {
        let m = finish(vec![fn_halting(0, "not_main")]);
        let r = reach(&m);
        assert!(r.is_empty());
    }
}
