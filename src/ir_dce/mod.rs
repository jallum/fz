//! Function-local liveness classification for native codegen.

use crate::fz_ir::{FnIr, Stmt, Term, Var};
use std::collections::HashSet;

/// Returns `(if_only_conds, all_used)` in a single pass.
///
/// `if_only_conds`: vars used exclusively as Term::If conditions — no prim
/// arg, no other terminator use. Boolean-producing prims whose dest is in
/// this set can skip emitting a tagged form entirely (fz-cg2.3).
///
/// `all_used`: every var referenced in any prim arg or terminator arg.
pub fn classify_var_uses(f: &FnIr) -> (HashSet<Var>, HashSet<Var>) {
    let mut if_conds: HashSet<Var> = HashSet::new();
    let mut other_uses: HashSet<Var> = HashSet::new();
    for block in &f.blocks {
        for stmt in &block.stmts {
            let Stmt::Let(_, prim) = stmt;
            prim.collect_used_vars(&mut other_uses);
        }
        match &block.terminator {
            Term::If { cond, .. } => {
                if_conds.insert(*cond);
            }
            t => collect_term_vars(t, &mut other_uses),
        }
    }
    let mut all_used = other_uses.clone();
    all_used.extend(if_conds.iter().cloned());
    let if_only_conds: HashSet<Var> = if_conds.into_iter().filter(|v| !other_uses.contains(v)).collect();
    (if_only_conds, all_used)
}

fn collect_term_vars(t: &Term, used: &mut HashSet<Var>) {
    match t {
        Term::Goto(_, args) => {
            for v in args {
                used.insert(*v);
            }
        }
        Term::If { cond, .. } => {
            used.insert(*cond);
        }
        Term::Call {
            ident: _,
            args,
            continuation,
            ..
        } => {
            for v in args {
                used.insert(*v);
            }
            for v in &continuation.captured {
                used.insert(*v);
            }
        }
        Term::TailCall { args, .. } => {
            for v in args {
                used.insert(*v);
            }
        }
        Term::CallClosure {
            ident: _,
            closure,
            args,
            continuation,
            ..
        } => {
            used.insert(*closure);
            for v in args {
                used.insert(*v);
            }
            for v in &continuation.captured {
                used.insert(*v);
            }
        }
        Term::TailCallClosure {
            closure,
            args,
            ident: _,
            ..
        } => {
            used.insert(*closure);
            for v in args {
                used.insert(*v);
            }
        }
        Term::Return(a) | Term::Halt(a) => {
            used.insert(*a);
        }
        Term::ReturnLanes(lanes) => {
            for v in lanes {
                used.insert(*v);
            }
        }
        // fz-yxs — Vars referenced by ReceiveMatched: pinned and captures
        // are live (passed to matcher / clause-body fns), as is the
        // computed timeout Var if there's an after clause.
        Term::ReceiveMatched {
            pinned,
            captures,
            after,
            ..
        } => {
            for (_, v) in pinned {
                used.insert(*v);
            }
            for v in captures {
                used.insert(*v);
            }
            if let Some(a) = after {
                used.insert(a.timeout);
            }
        }
    }
}
