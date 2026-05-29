//! fz-t1m.1.5 — Closed-domain protocol switch dispatch.
//!
//! A protocol call dispatches on its first argument's runtime type. When the
//! planner can prove the receiver is a *single* implementing target it
//! devirtualizes the call to that impl (see `walk::protocol_dispatch_key`).
//! When the receiver is a *closed union* of several implementing targets —
//! `integer | list(...)` where both `Integer` and `List` implement the
//! protocol — no single subtype match exists, so the call would fall through
//! to the `__protocol__` stub and halt at runtime with
//! `:protocol_dispatch_unplanned`.
//!
//! This pass closes that gap by *rewriting the IR*, not by adding a new
//! dispatch state. For each such callsite it emits a `TypeTest`/`If` cascade
//! with one direct-call arm per implementing target:
//!
//! ```text
//!   t0 = TypeTest(recv, integer)
//!   if t0 -> arm_int  else -> arm_list
//! arm_int:    Integer.cb(recv, …) -> K
//! arm_list:   List.cb(recv, …)    -> K
//! ```
//!
//! Narrowing makes this correct by construction: `narrow::narrow_for_cond`
//! intersects `recv` with `integer` in the `then` arm and differences it in
//! the `else` arm, so when the authoritative `plan_module` re-types the
//! rewritten module each arm's receiver is the arm's target type and the
//! ordinary direct-call planner specs it to the right impl. `TypeTest`,
//! `If`, and `Call` already lower in the interpreter, JIT, and AOT, so the
//! rewrite holds three-path parity with no new codegen.
//!
//! The pass is modeled on `closures::rewrite_known_target_closures`: a
//! planner-fact-driven module mutation run before the authoritative plan.
//! Callers re-run `plan_module` afterward to refresh facts against the
//! rewritten IR.

use super::diagnostics::env_after_block_stmts;
use super::fn_types::{ModulePlan, SpecPlan};
use crate::fz_ir::{
    Block, BlockId, BranchOrigin, CallsiteIdent, FnId, Module, Prim, Stmt, Term, Var,
};
use std::collections::HashMap;

/// One arm of a switch: the runtime type to test the receiver against and the
/// local impl fn to call when it matches.
struct SwitchArm {
    target_ty: crate::types::Ty,
    impl_fn: FnId,
}

/// A rewrite to apply to one block whose terminator is a closed-union protocol
/// call. Collected in a read-only pass, then applied in a second mutating pass
/// so the planner facts stay valid while we decide.
struct BlockRewrite {
    fn_id: FnId,
    block_id: BlockId,
    arms: Vec<SwitchArm>,
}

/// Rewrite every closed-union protocol-dispatch callsite into a `TypeTest`/`If`
/// cascade of per-target direct calls. Module mutation only; returns `true` if
/// anything was rewritten so the caller can refresh its `ModulePlan` against
/// the new IR.
pub fn rewrite_closed_union_protocol_dispatch<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &mut Module,
    plan: &ModulePlan,
) -> bool {
    if module.protocol_call_targets.is_empty() {
        return false;
    }
    let rewrites = collect_block_rewrites(t, module, plan);
    let changed = !rewrites.is_empty();
    for rewrite in rewrites {
        apply_block_rewrite(module, rewrite);
    }
    changed
}

/// Decide which blocks to rewrite. Read-only over `module` + `plan`.
fn collect_block_rewrites<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    plan: &ModulePlan,
) -> Vec<BlockRewrite> {
    let specs_by_fn = value_specs_by_fn(plan);
    let mut out = Vec::new();
    for f in &module.fns {
        let Some(specs) = specs_by_fn.get(&f.id) else {
            continue;
        };
        for b in &f.blocks {
            let (callee, args) = match &b.terminator {
                Term::Call { callee, args, .. } | Term::TailCall { callee, args, .. } => {
                    (*callee, args)
                }
                _ => continue,
            };
            let Some(target) = module.protocol_call_targets.get(&callee) else {
                continue;
            };
            let Some(receiver_var) = args.first().copied() else {
                continue;
            };
            let receiver_ty = merged_receiver_ty(t, module, specs, b, receiver_var);
            if let Some(arms) = closed_union_arms(t, module, target, &receiver_ty) {
                out.push(BlockRewrite {
                    fn_id: f.id,
                    block_id: b.id,
                    arms,
                });
            }
        }
    }
    out
}

/// The receiver's type at `block`, merged (unioned) across every value spec of
/// the enclosing fn. Mirrors `rewrite_known_target_closures`' "consider every
/// spec" discipline: the rewrite must be sound for all specializations that
/// reach this block, so we test against their union.
fn merged_receiver_ty<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    specs: &[&SpecPlan],
    block: &Block,
    receiver_var: Var,
) -> crate::types::Ty {
    let mut merged = t.none();
    for ft in specs {
        if !ft.reachable_blocks.contains(&block.id) {
            continue;
        }
        let env = env_after_block_stmts(t, module, ft, block);
        let ty = env.get(&receiver_var).cloned().unwrap_or_else(|| t.any());
        merged = t.union(merged, ty);
    }
    merged
}

/// If `receiver_ty` is a closed union of two or more locally-implemented
/// targets — every part covered, no residual — return one arm per covered
/// target. Otherwise `None` (single target, residual, or an external impl —
/// all left to the existing single-dispatch path or to open/erased lookup).
fn closed_union_arms<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    module: &Module,
    target: &crate::fz_ir::ProtocolCallTarget,
    receiver_ty: &crate::types::Ty,
) -> Option<Vec<SwitchArm>> {
    if t.is_empty(receiver_ty) {
        return None;
    }
    let mut arms = Vec::new();
    let mut covered = t.none();
    for fact in module
        .protocol_registry
        .impls
        .values()
        .filter(|fact| fact.protocol == target.protocol)
    {
        let target_ty = crate::protocols::impl_target_type(t, &fact.target);
        let overlap = t.intersect(receiver_ty.clone(), target_ty.clone());
        if t.is_empty(&overlap) {
            continue;
        }
        // The receiver overlaps this target. The arm can only be a local,
        // direct call if the impl callback resolves to an in-module fn.
        let export = fact.callbacks.get(&(target.callback.clone(), target.arity))?;
        let fn_name = format!("{}.{}", export.module, export.name);
        let impl_fn = module.fn_by_name(&fn_name)?.id;
        covered = t.union(covered, overlap);
        arms.push(SwitchArm { target_ty, impl_fn });
    }
    // A switch is warranted only for a genuine closed union: at least two
    // arms, and the arms together account for the whole receiver. A single
    // arm is ordinary single dispatch; an uncovered residual is an open or
    // erased domain (runtime lookup, a separate concern).
    if arms.len() < 2 || !t.is_subtype(receiver_ty, &covered) {
        return None;
    }
    // Sort arms by impl FnId for a deterministic cascade order.
    arms.sort_by_key(|arm| arm.impl_fn.0);
    Some(arms)
}

/// Replace the protocol-call terminator in one block with the switch cascade.
///
/// The original block keeps its statements and becomes the cascade head. Each
/// arm gets a fresh block that calls its impl directly with the original call's
/// arguments and continuation; the receiver narrows to the arm's target type
/// when the module is re-planned. Tests are emitted for every arm except the
/// last, which is the final fall-through `else`.
fn apply_block_rewrite(module: &mut Module, rewrite: BlockRewrite) {
    let f = module
        .fns
        .iter_mut()
        .find(|f| f.id == rewrite.fn_id)
        .expect("rewrite targets an existing fn");

    let head_idx = f
        .blocks
        .iter()
        .position(|b| b.id == rewrite.block_id)
        .expect("rewrite targets an existing block");

    // The terminator we are replacing carries the call shape every arm reuses.
    let (args, continuation, is_tail, is_back_edge) = match &f.blocks[head_idx].terminator {
        Term::Call {
            args,
            continuation,
            ..
        } => (args.clone(), Some(continuation.clone()), false, false),
        Term::TailCall {
            args, is_back_edge, ..
        } => (args.clone(), None, true, *is_back_edge),
        other => unreachable!("rewrite block terminator is a protocol call, got {:?}", other),
    };
    let receiver = args[0];
    let n = rewrite.arms.len();

    let var_base = crate::ir_inline::max_var(f) + 1;
    let block_base = crate::ir_inline::max_block(f) + 1;

    // Block id layout: arm blocks first (one per arm), then the intermediate
    // test blocks (one per tested arm beyond the head, i.e. arms 1..n-1).
    let arm_block = |i: usize| BlockId(block_base + i as u32);
    let test_block = |i: usize| BlockId(block_base + n as u32 + (i as u32 - 1));
    // The test point for arm i: the head block for arm 0, a fresh test block
    // otherwise. The last arm (n-1) is never tested — it is the final `else`.
    let test_point = |i: usize| {
        if i == 0 {
            rewrite.block_id
        } else {
            test_block(i)
        }
    };

    let arm_terminator = |impl_fn: FnId| -> Term {
        let ident = CallsiteIdent::from_source(crate::diag::Span::DUMMY);
        if is_tail {
            Term::TailCall {
                ident,
                callee: impl_fn,
                args: args.clone(),
                is_back_edge,
            }
        } else {
            Term::Call {
                ident,
                callee: impl_fn,
                args: args.clone(),
                continuation: continuation.clone().expect("non-tail call has a continuation"),
            }
        }
    };

    // Emit the test cascade onto the head block and the intermediate test
    // blocks. For tested arm i, the `else` target is the next test point
    // (arm i+1's test) — except the penultimate test, whose `else` is the
    // final untested arm block.
    let mut new_blocks: Vec<Block> = Vec::with_capacity(2 * n);
    for i in 0..n - 1 {
        let tv = Var(var_base + i as u32);
        let test_stmt = Stmt::Let(tv, Prim::TypeTest(receiver, Box::new(rewrite.arms[i].target_ty.clone())));
        let else_b = if i + 1 == n - 1 {
            arm_block(n - 1)
        } else {
            test_block(i + 1)
        };
        let term = Term::If {
            cond: tv,
            then_b: arm_block(i),
            else_b,
            origin: BranchOrigin::ClauseDispatch,
        };
        let point = test_point(i);
        if point == rewrite.block_id {
            f.blocks[head_idx].stmts.push(test_stmt);
            f.blocks[head_idx].terminator = term;
        } else {
            new_blocks.push(Block {
                id: point,
                params: vec![],
                stmts: vec![test_stmt],
                terminator: term,
            });
        }
    }

    // Emit one arm block per target, each a direct call to the impl.
    for (i, arm) in rewrite.arms.iter().enumerate() {
        new_blocks.push(Block {
            id: arm_block(i),
            params: vec![],
            stmts: vec![],
            terminator: arm_terminator(arm.impl_fn),
        });
    }

    f.blocks.extend(new_blocks);
}

fn value_specs_by_fn(plan: &ModulePlan) -> HashMap<FnId, Vec<&SpecPlan>> {
    let mut out: HashMap<FnId, Vec<&SpecPlan>> = HashMap::new();
    for (key, ft) in &plan.specs {
        if key.demand.is_value() {
            out.entry(key.fn_id).or_default().push(ft);
        }
    }
    out
}
