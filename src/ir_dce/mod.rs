//! Function-local liveness classification for native codegen.

use crate::fast_hash::{HashMap, HashSet};
use crate::fz_ir::{Block, BlockId, FnIr, Term, Var};

/// Returns `(if_only_conds, all_used)` in a single pass.
///
/// `if_only_conds`: vars whose only readers are branches: used as a
/// `Term::If` condition, or handed by `Term::Goto` to a block parameter that
/// is itself such a var. Only a block with exactly one predecessor, other
/// than the entry, passes its parameters on: the entry is reached from
/// outside the function (calls, frames, continuations), so its parameters
/// carry real values. Boolean-producing prims whose dest is in this set can
/// skip emitting a tagged form entirely (fz-cg2.3).
///
/// `all_used`: every var referenced in any prim arg or terminator arg.
pub fn classify_var_uses(f: &FnIr) -> (HashSet<Var>, HashSet<Var>) {
    let mut branch_reads: HashSet<Var> = HashSet::default();
    let mut other_uses: HashSet<Var> = HashSet::default();
    let mut hops: Vec<(Var, Var)> = Vec::new();
    let mut predecessors: HashMap<BlockId, usize> = HashMap::default();
    for block in &f.blocks {
        for stmt in &block.stmts {
            stmt.prim().collect_used_vars(&mut other_uses);
        }
        match &block.terminator {
            Term::If {
                cond, then_b, else_b, ..
            } => {
                branch_reads.insert(*cond);
                *predecessors.entry(*then_b).or_default() += 1;
                *predecessors.entry(*else_b).or_default() += 1;
            }
            Term::Goto(target, args) => {
                *predecessors.entry(*target).or_default() += 1;
                let params = &f.block(*target).params;
                hops.extend(args.iter().copied().zip(params.iter().copied()));
                branch_reads.extend(args.iter().copied());
            }
            t => {
                if let Term::Try { body, .. } = t {
                    *predecessors.entry(*body).or_default() += 1;
                }
                collect_term_vars(t, &mut other_uses);
            }
        }
    }
    let mut all_used = other_uses.clone();
    all_used.extend(branch_reads.iter().cloned());
    let passes_params = |block: &Block| block.id != f.entry && predecessors.get(&block.id) == Some(&1);
    let non_passing_params: HashSet<Var> = f
        .blocks
        .iter()
        .filter(|block| !passes_params(block))
        .flat_map(|block| block.params.iter().copied())
        .collect();
    let mut if_only_conds: HashSet<Var> = branch_reads
        .into_iter()
        .filter(|v| !other_uses.contains(v) && !non_passing_params.contains(v))
        .collect();
    // A var handed on to a param that reads the value is no longer branch-only.
    loop {
        let readers: Vec<Var> = hops
            .iter()
            .filter(|(arg, param)| if_only_conds.contains(arg) && !if_only_conds.contains(param))
            .map(|(arg, _)| *arg)
            .collect();
        if readers.is_empty() {
            break;
        }
        for read in readers {
            if_only_conds.remove(&read);
        }
    }
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
        Term::TailCallClosure { closure, args, .. } => {
            used.insert(*closure);
            for v in args {
                used.insert(*v);
            }
        }
        Term::Try { captures, .. } => {
            for v in captures {
                used.insert(*v);
            }
        }
        Term::Return(a) => {
            used.insert(*a);
        }
        Term::Raise { value, reason } => {
            used.insert(*value);
            used.extend(*reason);
        }
        Term::Reraise { kind, value, reason } => {
            used.insert(*kind);
            used.insert(*value);
            used.insert(*reason);
        }
        Term::RaiseUndefined {
            receiver,
            function,
            modules_without,
            arity: _,
        } => {
            used.extend([*receiver, *function, *modules_without]);
        }
        Term::Unreachable => {}
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
            for v in pinned {
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
