//! Planner-private static call-graph utilities over `fz_ir::Module`.
//!
//! This is the planner's one source of truth for "what counts as a call
//! edge." The worklist uses it for recursion-component discovery and entry
//! seeding; downstream consumers read planner reachability facts from
//! `ModulePlan` instead of replaying the graph.

use crate::fz_ir::{FnId, Module, Prim, Stmt, Term};
use crate::types::{Ty, Types};
use std::collections::{HashMap, HashSet};

/// Build the graph used to identify true recursive function components.
///
/// This deliberately excludes the artificial callee -> continuation edge used
/// by forward reachability. A non-tail call's continuation belongs to the
/// caller's control flow, not to the callee's body. Including that edge makes
/// sequential call chains look recursive and lets one call site's fixed-point
/// facts pollute another call site.
pub(super) fn build_recursion_graph(m: &Module) -> HashMap<FnId, HashSet<FnId>> {
    build_call_graph_with_return_continuations(m, false)
}

/// Root set for planner discovery: `main` seeded with an any-keyed arg vector.
pub(super) fn entry_seeds<T: Types<Ty = Ty>>(t: &mut T, m: &Module) -> Vec<(FnId, Vec<Ty>)> {
    let mut seeds = Vec::new();
    if let Some(main) = m.fns.iter().find(|f| f.name == "main") {
        let n_params = main.block(main.entry).params.len();
        let any = t.any();
        seeds.push((main.id, t.repeat(any, n_params)));
    }
    seeds
}

fn build_call_graph_with_return_continuations(
    m: &Module,
    include_callee_to_continuation: bool,
) -> HashMap<FnId, HashSet<FnId>> {
    let mut g: HashMap<FnId, HashSet<FnId>> = HashMap::new();
    let mut extra_edges: Vec<(FnId, FnId)> = Vec::new();
    for f in &m.fns {
        let edges = g.entry(f.id).or_default();
        for b in &f.blocks {
            for stmt in &b.stmts {
                let Stmt::Let(_, prim) = stmt;
                if let Prim::MakeFnRef(_, lam_fn_id) | Prim::MakeClosure(_, lam_fn_id, _) = prim {
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
                    if include_callee_to_continuation {
                        extra_edges.push((*callee, continuation.fn_id));
                    }
                }
                Term::TailCall { callee, .. } => {
                    edges.insert(*callee);
                }
                Term::CallClosure { continuation, .. } => {
                    edges.insert(continuation.fn_id);
                }
                Term::TailCallClosure { .. } => {}
                Term::Receive { continuation, ident: _ } => {
                    edges.insert(continuation.fn_id);
                }
                // fz-70q.3 — clause body / guard / after fns reached via
                // selective-receive dispatch (matcher hit -> trampoline).
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
    for (from, to) in extra_edges {
        g.entry(from).or_default().insert(to);
    }
    g
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{CallsiteIdent, Cont, FnBuilder, FnId, Module, Prim, Term, Var};

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
        let _unused = b.fresh_var();
        let entry = b.block(vec![]);
        b.set_terminator(entry, Term::Halt(Var(0)));
        b
    }

    fn fn_tail_calling(id: u32, name: &str, target: u32) -> FnBuilder {
        let mut b = FnBuilder::new(FnId(id), name);
        let entry = b.block(vec![]);
        b.set_terminator(
            entry,
            Term::TailCall {
                ident: CallsiteIdent::synthetic(),
                callee: FnId(target),
                args: vec![],
                is_back_edge: false,
            },
        );
        b
    }

    #[test]
    fn entry_seeds_main_with_any_inputs() {
        let mut t = crate::types::ConcreteTypes;
        let mut main = FnBuilder::new(FnId(0), "main");
        let a = main.fresh_var();
        let b = main.fresh_var();
        let entry = main.block(vec![a, b]);
        main.set_terminator(entry, Term::Halt(a));
        let m = finish(vec![main]);
        let seeds = entry_seeds(&mut t, &m);
        assert_eq!(seeds.len(), 1);
        assert_eq!(seeds[0].0, FnId(0));
        assert_eq!(seeds[0].1.len(), 2);
    }

    #[test]
    fn entry_seeds_is_empty_without_main() {
        let mut t = crate::types::ConcreteTypes;
        let m = finish(vec![fn_halting(0, "not_main")]);
        assert!(entry_seeds(&mut t, &m).is_empty());
    }

    #[test]
    fn forward_graph_includes_call_continuation_and_makeclosure_edges() {
        let mut main_b = FnBuilder::new(FnId(0), "main");
        let entry = main_b.block(vec![]);
        main_b.let_(entry, Prim::MakeClosure(CallsiteIdent::synthetic(), FnId(3), vec![]));
        main_b.set_terminator(
            entry,
            Term::Call {
                ident: CallsiteIdent::synthetic(),
                callee: FnId(1),
                args: vec![],
                continuation: Cont {
                    fn_id: FnId(2),
                    captured: vec![],
                },
            },
        );
        let m = finish(vec![
            main_b,
            fn_halting(1, "callee"),
            fn_halting(2, "cont"),
            fn_halting(3, "lambda"),
        ]);
        let graph = build_call_graph_with_return_continuations(&m, true);
        assert!(graph.get(&FnId(0)).is_some_and(|edges| edges.contains(&FnId(1))));
        assert!(graph.get(&FnId(0)).is_some_and(|edges| edges.contains(&FnId(2))));
        assert!(graph.get(&FnId(0)).is_some_and(|edges| edges.contains(&FnId(3))));
        assert!(graph.get(&FnId(1)).is_some_and(|edges| edges.contains(&FnId(2))));
    }

    #[test]
    fn recursion_graph_excludes_callee_to_continuation_edges() {
        let mut main_b = FnBuilder::new(FnId(0), "main");
        let entry = main_b.block(vec![]);
        main_b.set_terminator(
            entry,
            Term::Call {
                ident: CallsiteIdent::synthetic(),
                callee: FnId(1),
                args: vec![],
                continuation: Cont {
                    fn_id: FnId(2),
                    captured: vec![],
                },
            },
        );
        let m = finish(vec![main_b, fn_tail_calling(1, "callee", 1), fn_halting(2, "cont")]);
        let graph = build_recursion_graph(&m);
        assert!(graph.get(&FnId(0)).is_some_and(|edges| edges.contains(&FnId(1))));
        assert!(graph.get(&FnId(0)).is_some_and(|edges| edges.contains(&FnId(2))));
        assert!(!graph.get(&FnId(1)).is_some_and(|edges| edges.contains(&FnId(2))));
    }
}
