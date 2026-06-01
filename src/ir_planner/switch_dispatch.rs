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

/// A rewrite to apply to one block whose terminator is a protocol call.
/// Collected in a read-only pass, then applied in a second mutating pass so the
/// planner facts stay valid while we decide.
struct BlockRewrite {
    fn_id: FnId,
    block_id: BlockId,
    arms: Vec<SwitchArm>,
    /// True when the arms together cover the whole receiver (a closed union):
    /// the last arm is the cascade's final `else` and no fallthrough is needed.
    /// False for an open or erased receiver (an `any`, or a union with a
    /// residual outside every impl): every arm is tested and the final `else`
    /// preserves the original stub call, so a runtime value matching no impl
    /// halts exactly as it does today.
    fully_covered: bool,
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
            if let Some((arms, fully_covered)) = switch_arms(t, module, target, &receiver_ty) {
                out.push(BlockRewrite {
                    fn_id: f.id,
                    block_id: b.id,
                    arms,
                    fully_covered,
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

/// Compute the dispatch arms for a protocol callsite, with one arm per local
/// implementing target the receiver overlaps. Returns the arms and whether they
/// cover the whole receiver (a closed union) or leave a residual (an open or
/// erased domain). `None` when no cascade is warranted: no overlapping local
/// impl, or a single fully-covering impl (ordinary static dispatch, already
/// devirtualized by `apply_planned_direct_call_targets`).
///
/// Arms are local-only: an arm calls its impl directly, so the callback must
/// resolve to an in-module fn. An overlapping target whose impl is external
/// (a provider not yet linked) makes the receiver not fully covered here — its
/// part of the receiver becomes residual handled by the fallthrough, the same
/// boundary `protocol_dispatch_key` draws between local and external dispatch.
fn switch_arms<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    module: &Module,
    target: &crate::fz_ir::ProtocolCallTarget,
    receiver_ty: &crate::types::Ty,
) -> Option<(Vec<SwitchArm>, bool)> {
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
        let target_ty = crate::frontend::protocols::impl_target_type(t, &fact.target);
        let overlap = t.intersect(receiver_ty.clone(), target_ty.clone());
        if t.is_empty(&overlap) {
            continue;
        }
        // The receiver overlaps this target. The arm can only be a local,
        // direct call if the impl callback resolves to an in-module fn; an
        // external impl is left to the fallthrough (its overlap stays residual).
        let Some(export) = fact.callbacks.get(&(target.callback.clone(), target.arity)) else {
            continue;
        };
        let fn_name = format!("{}.{}", export.module, export.name);
        let Some(impl_fn) = module.fn_by_name(&fn_name).map(|f| f.id) else {
            continue;
        };
        covered = t.union(covered, overlap);
        arms.push(SwitchArm { target_ty, impl_fn });
    }
    if arms.is_empty() {
        return None;
    }
    let fully_covered = t.is_subtype(receiver_ty, &covered);
    // A single arm that covers the whole receiver is ordinary single dispatch
    // (`protocol_dispatch_key` already matched it by subtype); no cascade.
    if arms.len() == 1 && fully_covered {
        return None;
    }
    // Sort arms by impl FnId for a deterministic cascade order.
    arms.sort_by_key(|arm| arm.impl_fn.0);
    Some((arms, fully_covered))
}

/// Replace the protocol-call terminator in one block with the switch cascade.
///
/// The original block keeps its statements and becomes the cascade head. Each
/// arm gets a fresh block that calls its impl directly with the original call's
/// arguments and continuation; the receiver narrows to the arm's target type
/// when the planner processes the rewritten module.
///
/// A fully-covered (closed-union) receiver tests every arm but the last, which
/// is the final `else`. An open or erased receiver tests every arm and routes
/// the final `else` to a fallthrough block that preserves the original stub
/// call, so a runtime value matching no arm halts as it does today.
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

    // The original stub terminator carries the call shape every arm reuses and,
    // for an open receiver, becomes the no-match fallthrough verbatim.
    let original = f.blocks[head_idx].terminator.clone();
    let (args, continuation, is_tail, is_back_edge) = match &original {
        Term::Call {
            args, continuation, ..
        } => (args.clone(), Some(continuation.clone()), false, false),
        Term::TailCall {
            args, is_back_edge, ..
        } => (args.clone(), None, true, *is_back_edge),
        other => unreachable!(
            "rewrite block terminator is a protocol call, got {:?}",
            other
        ),
    };
    let receiver = args[0];
    let n = rewrite.arms.len();
    // Arms tested in the cascade. A closed union leaves its last arm untested
    // (the final `else`); an open receiver tests them all.
    let num_tests = if rewrite.fully_covered { n - 1 } else { n };

    let var_base = crate::ir_inline::max_var(f) + 1;
    let block_base = crate::ir_inline::max_block(f) + 1;
    // Block id layout: arm blocks [0, n), then (open only) the fallthrough
    // block, then the intermediate test blocks (tests 1..num_tests; test 0 is
    // the head block).
    let arm_block = |i: usize| BlockId(block_base + i as u32);
    let fallthrough_block = BlockId(block_base + n as u32);
    let test_extra_base = block_base + n as u32 + if rewrite.fully_covered { 0 } else { 1 };
    let test_point = |i: usize| {
        if i == 0 {
            rewrite.block_id
        } else {
            BlockId(test_extra_base + (i as u32 - 1))
        }
    };
    let final_else = if rewrite.fully_covered {
        arm_block(n - 1)
    } else {
        fallthrough_block
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
                continuation: continuation
                    .clone()
                    .expect("non-tail call has a continuation"),
            }
        }
    };

    // Emit the test cascade onto the head block and the intermediate test
    // blocks. Tested arm i branches then→arm i, else→the next test point, or
    // the final `else` (the untested last arm, or the fallthrough).
    let mut new_blocks: Vec<Block> = Vec::with_capacity(2 * n + 1);
    for i in 0..num_tests {
        let tv = Var(var_base + i as u32);
        let test_stmt = Stmt::Let(
            tv,
            Prim::TypeTest(receiver, Box::new(rewrite.arms[i].target_ty.clone())),
        );
        let else_b = if i + 1 < num_tests {
            test_point(i + 1)
        } else {
            final_else
        };
        let term = Term::If {
            cond: tv,
            then_b: arm_block(i),
            else_b,
            origin: BranchOrigin::ClauseDispatch,
        };
        if i == 0 {
            f.blocks[head_idx].stmts.push(test_stmt);
            f.blocks[head_idx].terminator = term;
        } else {
            new_blocks.push(Block {
                id: test_point(i),
                params: vec![],
                stmts: vec![test_stmt],
                terminator: term,
            });
        }
    }

    // One arm block per target, each a direct call to the impl.
    for (i, arm) in rewrite.arms.iter().enumerate() {
        new_blocks.push(Block {
            id: arm_block(i),
            params: vec![],
            stmts: vec![],
            terminator: arm_terminator(arm.impl_fn),
        });
    }

    // Open receiver: the fallthrough preserves the original stub call so a
    // value matching no arm halts exactly as before the rewrite.
    if !rewrite.fully_covered {
        new_blocks.push(Block {
            id: fallthrough_block,
            params: vec![],
            stmts: vec![],
            terminator: original,
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
