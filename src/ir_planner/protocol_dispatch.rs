//! DispatchMatrix-backed protocol dispatch.
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
//! This pass closes that gap by building a `DispatchMatrix` over the receiver
//! domain and lowering the resulting `DispatchGraph` into IR. For each such
//! callsite it emits a `TypeTest`/`If` cascade with one direct-call arm per
//! implementing target:
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
//! the `else` arm, so when the authoritative `plan_module_with_role` re-types the
//! rewritten module each arm's receiver is the arm's target type and the
//! ordinary direct-call planner specs it to the right impl. `TypeTest`,
//! `If`, and `Call` already lower in the interpreter, JIT, and AOT, so the
//! rewrite holds three-path parity with no new codegen.
//!
//! The pass is a planner-fact-driven module mutation that must run before the
//! authoritative plan for the rewritten module is produced.

use super::diagnostics::env_after_block_stmts;
use super::fn_types::{ModulePlan, SpecPlan};
use crate::compiler::source::Span;
use crate::dispatch_matrix::{
    CompiledDispatchGraph, DispatchCompileError, DispatchCompileOptions, DispatchMatrix, DispatchMatrixBuilder,
    DispatchNode, EdgeEvidence, EqualTypeRegionPolicy, GraphNodeId, OutcomeId, OutcomeMultiplicity, Region,
    RegionQuestion, SubjectId, compile_dispatch_matrix_with_type_order,
};
use crate::frontend::protocols::impl_target_type;
use crate::fz_ir::{
    BitSizeIr, Block, BlockId, BranchOrigin, CallsiteIdent, FnId, FnIr, Module, Prim, ProtocolCallTarget, Stmt, Term,
    Var,
};
use crate::types::{ClosureTypes, Ty, Types};
use std::collections::HashMap;

/// One visible local protocol implementation arm before it is assigned a
/// DispatchMatrix outcome.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ProtocolImplArm {
    target_ty: Ty,
    impl_fn: FnId,
}

struct ProtocolDispatchRewrite {
    fn_id: FnId,
    block_id: BlockId,
    lowering: ProtocolDispatchLowering,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ProtocolDispatchLowering {
    tests: Vec<ProtocolDispatchTest>,
    final_else: ProtocolDispatchTerminal,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ProtocolDispatchTest {
    target_ty: Ty,
    impl_fn: FnId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ProtocolDispatchTerminal {
    Direct { impl_fn: FnId },
    Fallback,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProtocolDispatchMatrixCandidate {
    pub(crate) fn_id: FnId,
    pub(crate) block_id: BlockId,
    pub(crate) selection: ProtocolDispatchMatrixSelection,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ProtocolDispatchMatrixSelection {
    StaticDirect,
    Matrix(Box<ProtocolDispatchMatrixPlan>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProtocolDispatchMatrixPlan {
    pub(crate) matrix: DispatchMatrix,
    pub(crate) graph: CompiledDispatchGraph,
    pub(crate) direct_outcomes: Vec<ProtocolDirectOutcome>,
    pub(crate) fallback_outcome: Option<OutcomeId>,
    pub(crate) fully_covered: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProtocolDirectOutcome {
    pub(crate) outcome: OutcomeId,
    pub(crate) target_ty: Ty,
    pub(crate) impl_fn: FnId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ProtocolImplSelection {
    NoLocalArms,
    StaticDirect,
    Matrix {
        arms: Vec<ProtocolImplArm>,
        fully_covered: bool,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ProtocolDispatchLowerError {
    UnknownGraphNode(GraphNodeId),
    UnsupportedGraphShape(&'static str),
    UnsupportedPredicate,
    UnsupportedSubject(SubjectId),
    UnknownOutcome(OutcomeId),
    FallbackOnMatch(OutcomeId),
    DirectOutcomeTypeMismatch {
        outcome: OutcomeId,
        predicate_ty: Ty,
        outcome_ty: Ty,
    },
}

fn max_var(f: &FnIr) -> u32 {
    let mut max = 0;
    for block in &f.blocks {
        for param in &block.params {
            max = max.max(param.0);
        }
        for stmt in &block.stmts {
            let Stmt::Let(var, prim) = stmt;
            max = max.max(var.0).max(max_var_in_prim(prim));
        }
        max = max.max(max_var_in_term(&block.terminator));
    }
    max
}

fn max_block(f: &FnIr) -> u32 {
    f.blocks.iter().map(|block| block.id.0).max().unwrap_or(0)
}

fn max_var_in_prim(prim: &Prim) -> u32 {
    let mut max = 0;
    let mut visit = |var: Var| max = max.max(var.0);
    match prim {
        Prim::Const(_)
        | Prim::MakeFnRef(_, _)
        | Prim::DestTupleBegin { .. }
        | Prim::DestListBegin { .. }
        | Prim::ConstBitstring(_, _) => {}
        Prim::BinOp(_, lhs, rhs) | Prim::MapGet(lhs, rhs) | Prim::MatcherMapGet(lhs, rhs) => {
            visit(*lhs);
            visit(*rhs);
        }
        Prim::UnOp(_, value)
        | Prim::ListHead(value)
        | Prim::ListTail(value)
        | Prim::IsEmptyList(value)
        | Prim::IsListCons(value)
        | Prim::TupleField(value, _)
        | Prim::StructField(value, _)
        | Prim::IsMatcherMapMiss(value)
        | Prim::BitReaderInit(value)
        | Prim::BitReaderDone(value)
        | Prim::TypeTest(value, _)
        | Prim::RuntimeTypeTestShim(value, _)
        | Prim::Brand(value, _) => visit(*value),
        Prim::Extern(_, _, args) => args.iter().for_each(|arg| visit(arg.var)),
        Prim::MakeTuple(args) | Prim::MakeClosure(_, _, args) => args.iter().for_each(|arg| visit(*arg)),
        Prim::MakeStruct { fields, .. } => fields.iter().for_each(|(_, value)| visit(*value)),
        Prim::DestTupleSet { dest, value, .. } => {
            visit(*dest);
            visit(*value);
        }
        Prim::DestFreeze { dest, .. } => visit(*dest),
        Prim::DestListCons { head, tail, .. } => {
            visit(*head);
            if let Some(tail) = tail {
                visit(*tail);
            }
        }
        Prim::DestListFreeze { list, .. } => visit(*list),
        Prim::MakeList(items, tail) => {
            items.iter().for_each(|item| visit(*item));
            if let Some(tail) = tail {
                visit(*tail);
            }
        }
        Prim::MakeMap(entries) => entries.iter().for_each(|(key, value)| {
            visit(*key);
            visit(*value);
        }),
        Prim::MapUpdate(base, entries) => {
            visit(*base);
            entries.iter().for_each(|(key, value)| {
                visit(*key);
                visit(*value);
            });
        }
        Prim::DestMapBegin { base, .. } => {
            if let Some(base) = base {
                visit(*base);
            }
        }
        Prim::DestMapPut { map, key, value, .. } => {
            visit(*map);
            visit(*key);
            visit(*value);
        }
        Prim::DestMapFreeze { map, .. } => visit(*map),
        Prim::MakeBitstring(fields) => fields.iter().for_each(|field| {
            visit(field.value);
            if let Some(BitSizeIr::Var(size)) = &field.size {
                visit(*size);
            }
        }),
        Prim::BitReadField { reader, size, .. } => {
            visit(*reader);
            if let Some(BitSizeIr::Var(size)) = size {
                visit(*size);
            }
        }
    }
    max
}

fn max_var_in_term(term: &Term) -> u32 {
    let mut max = 0;
    let mut visit = |var: Var| max = max.max(var.0);
    match term {
        Term::Goto(_, args) | Term::TailCall { args, .. } => args.iter().for_each(|arg| visit(*arg)),
        Term::If { cond, .. } | Term::Return(cond) | Term::Halt(cond) => visit(*cond),
        Term::Call { args, continuation, .. } | Term::CallClosure { args, continuation, .. } => {
            args.iter().for_each(|arg| visit(*arg));
            continuation.captured.iter().for_each(|capture| visit(*capture));
            if let Term::CallClosure { closure, .. } = term {
                visit(*closure);
            }
        }
        Term::TailCallClosure { closure, args, .. } => {
            visit(*closure);
            args.iter().for_each(|arg| visit(*arg));
        }
        Term::ReceiveMatched {
            pinned,
            captures,
            after,
            ..
        } => {
            pinned.iter().for_each(|(_, var)| visit(*var));
            captures.iter().for_each(|capture| visit(*capture));
            if let Some(after) = after {
                visit(after.timeout);
            }
        }
    }
    max
}

/// Rewrite every matrix-backed protocol-dispatch callsite into a `TypeTest`/`If`
/// cascade of per-target direct calls plus any residual stub fallthrough.
/// Module mutation only; returns `true` if anything was rewritten so the caller
/// can refresh its `ModulePlan` against the new IR.
pub fn rewrite_closed_union_protocol_dispatch<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    module: &mut Module,
    plan: &ModulePlan,
) -> bool {
    if module.protocol_call_targets.is_empty() {
        return false;
    }
    let candidates = collect_protocol_dispatch_matrix_candidates(t, module, plan)
        .expect("protocol dispatch matrix construction should be valid");
    let rewrites = candidates
        .into_iter()
        .filter_map(|candidate| {
            let ProtocolDispatchMatrixSelection::Matrix(plan) = candidate.selection else {
                return None;
            };
            let lowering =
                protocol_dispatch_lowering(&plan).expect("protocol DispatchGraph should lower to protocol TypeTest IR");
            Some(ProtocolDispatchRewrite {
                fn_id: candidate.fn_id,
                block_id: candidate.block_id,
                lowering,
            })
        })
        .collect::<Vec<_>>();
    let changed = !rewrites.is_empty();
    for rewrite in rewrites {
        apply_protocol_dispatch_matrix_rewrite(module, rewrite);
    }
    changed
}

/// Build DispatchMatrix protocol-dispatch candidates from the same planner
/// facts the IR rewrite consumes.
pub(crate) fn collect_protocol_dispatch_matrix_candidates<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    module: &Module,
    plan: &ModulePlan,
) -> Result<Vec<ProtocolDispatchMatrixCandidate>, DispatchCompileError> {
    let specs_by_fn = value_specs_by_fn(plan);
    let mut out = Vec::new();
    for f in &module.fns {
        let Some(specs) = specs_by_fn.get(&f.id) else {
            continue;
        };
        for b in &f.blocks {
            let (callee, args) = match &b.terminator {
                Term::Call { callee, args, .. } | Term::TailCall { callee, args, .. } => (*callee, args),
                _ => continue,
            };
            let Some(target) = module.protocol_call_targets.get(&callee) else {
                continue;
            };
            let Some(receiver_var) = args.first().copied() else {
                continue;
            };
            let receiver_ty = merged_receiver_ty(t, module, specs, b, receiver_var);
            let Some(selection) = protocol_dispatch_matrix_for_receiver(t, module, target, &receiver_ty)? else {
                continue;
            };
            out.push(ProtocolDispatchMatrixCandidate {
                fn_id: f.id,
                block_id: b.id,
                selection,
            });
        }
    }
    Ok(out)
}

/// The receiver's type at `block`, merged (unioned) across every value spec of
/// the enclosing fn. The rewrite must be sound for all specializations that
/// reach this block, so we test against their union.
fn merged_receiver_ty<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    module: &Module,
    specs: &[&SpecPlan],
    block: &Block,
    receiver_var: Var,
) -> Ty {
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

/// Compute the local impl arms for a protocol callsite, with one arm per local
/// implementing target the receiver overlaps. The result also records whether
/// those arms cover the whole receiver (a closed union) or leave a residual (an
/// open or erased domain). No matrix is warranted when there is no overlapping
/// local impl, or a single fully-covering impl (ordinary static dispatch,
/// already devirtualized by `apply_planned_direct_call_targets`).
///
/// Arms are local-only: an arm calls its impl directly, so the callback must
/// resolve to an in-module fn. An overlapping target whose impl is external
/// (a provider not yet linked) makes the receiver not fully covered here — its
/// part of the receiver becomes residual handled by the fallthrough, the same
/// boundary `protocol_dispatch_key` draws between local and external dispatch.
fn protocol_dispatch_matrix_for_receiver<T: Types<Ty = Ty>>(
    t: &mut T,
    module: &Module,
    target: &ProtocolCallTarget,
    receiver_ty: &Ty,
) -> Result<Option<ProtocolDispatchMatrixSelection>, DispatchCompileError> {
    match protocol_impl_selection(t, module, target, receiver_ty) {
        ProtocolImplSelection::NoLocalArms => Ok(None),
        ProtocolImplSelection::StaticDirect => Ok(Some(ProtocolDispatchMatrixSelection::StaticDirect)),
        ProtocolImplSelection::Matrix { arms, fully_covered } => {
            let mut builder = DispatchMatrixBuilder::typed(crate::dispatch_matrix::Order::Specificity);
            let receiver = builder.add_input_subject();
            let mut direct_outcomes = Vec::new();
            for arm in arms {
                let outcome = builder.add_outcome(OutcomeMultiplicity::Unique);
                builder
                    .add_arm_questions(
                        vec![RegionQuestion::type_region(receiver, arm.target_ty.clone())],
                        EdgeEvidence::empty(),
                        outcome,
                    )
                    .map_err(DispatchCompileError::MatrixBuild)?;
                direct_outcomes.push(ProtocolDirectOutcome {
                    outcome,
                    target_ty: arm.target_ty,
                    impl_fn: arm.impl_fn,
                });
            }
            let fallback_outcome = if fully_covered {
                None
            } else {
                Some(builder.add_outcome(OutcomeMultiplicity::Unique))
            };
            let matrix = builder.build().map_err(DispatchCompileError::MatrixBuild)?;
            let options = fallback_outcome
                .map(DispatchCompileOptions::open)
                .unwrap_or_else(DispatchCompileOptions::closed);
            let graph =
                compile_dispatch_matrix_with_type_order(t, &matrix, options, EqualTypeRegionPolicy::DuplicateCoverage)?;
            Ok(Some(ProtocolDispatchMatrixSelection::Matrix(Box::new(
                ProtocolDispatchMatrixPlan {
                    matrix,
                    graph,
                    direct_outcomes,
                    fallback_outcome,
                    fully_covered,
                },
            ))))
        }
    }
}

fn protocol_impl_selection<T: Types<Ty = Ty>>(
    t: &mut T,
    module: &Module,
    target: &ProtocolCallTarget,
    receiver_ty: &Ty,
) -> ProtocolImplSelection {
    if t.is_empty(receiver_ty) {
        return ProtocolImplSelection::NoLocalArms;
    }
    let mut arms = Vec::new();
    let mut covered = t.none();
    for fact in module
        .protocol_registry
        .impls
        .values()
        .filter(|fact| fact.protocol == target.protocol)
    {
        let target_ty = impl_target_type(t, &fact.target);
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
        arms.push(ProtocolImplArm { target_ty, impl_fn });
    }
    if arms.is_empty() {
        return ProtocolImplSelection::NoLocalArms;
    }
    let fully_covered = t.is_subtype(receiver_ty, &covered);
    // A single arm that covers the whole receiver is ordinary single dispatch
    // (`protocol_dispatch_key` already matched it by subtype); no cascade.
    if arms.len() == 1 && fully_covered {
        return ProtocolImplSelection::StaticDirect;
    }
    // Specificity ordering in DispatchMatrix determines semantic priority; this
    // pre-sort keeps orthogonal arms deterministic before matrix construction.
    arms.sort_by_key(|arm| arm.impl_fn.0);
    ProtocolImplSelection::Matrix { arms, fully_covered }
}

fn protocol_dispatch_lowering(
    plan: &ProtocolDispatchMatrixPlan,
) -> Result<ProtocolDispatchLowering, ProtocolDispatchLowerError> {
    let mut tests = Vec::new();
    let mut node = plan.graph.graph.root;
    loop {
        let graph_node = plan
            .graph
            .graph
            .node(node)
            .ok_or(ProtocolDispatchLowerError::UnknownGraphNode(node))?;
        match graph_node {
            DispatchNode::Test {
                predicate,
                on_match,
                on_miss,
            } => {
                if predicate.subject != SubjectId(0) {
                    return Err(ProtocolDispatchLowerError::UnsupportedSubject(predicate.subject));
                }
                let Region::Type(target_ty) = &predicate.region else {
                    return Err(ProtocolDispatchLowerError::UnsupportedPredicate);
                };
                let outcome = direct_outcome_for_node(plan, on_match.target)?;
                if outcome.target_ty != *target_ty {
                    return Err(ProtocolDispatchLowerError::DirectOutcomeTypeMismatch {
                        outcome: outcome.outcome,
                        predicate_ty: target_ty.clone(),
                        outcome_ty: outcome.target_ty.clone(),
                    });
                }
                tests.push(ProtocolDispatchTest {
                    target_ty: target_ty.clone(),
                    impl_fn: outcome.impl_fn,
                });
                node = on_miss.target;
            }
            DispatchNode::Outcome { outcome, .. } if Some(*outcome) == plan.fallback_outcome => {
                if plan.fully_covered {
                    return Err(ProtocolDispatchLowerError::UnsupportedGraphShape(
                        "closed protocol matrix cannot end in fallback",
                    ));
                }
                if tests.is_empty() {
                    return Err(ProtocolDispatchLowerError::UnsupportedGraphShape(
                        "protocol matrix needs at least one test",
                    ));
                }
                return Ok(ProtocolDispatchLowering {
                    tests,
                    final_else: ProtocolDispatchTerminal::Fallback,
                });
            }
            DispatchNode::Outcome { outcome, .. } => {
                let direct =
                    direct_outcome(plan, *outcome).ok_or(ProtocolDispatchLowerError::UnknownOutcome(*outcome))?;
                if tests.is_empty() {
                    return Err(ProtocolDispatchLowerError::UnsupportedGraphShape(
                        "protocol matrix needs at least one test",
                    ));
                }
                return Ok(ProtocolDispatchLowering {
                    tests,
                    final_else: ProtocolDispatchTerminal::Direct {
                        impl_fn: direct.impl_fn,
                    },
                });
            }
            DispatchNode::Fail => {
                if !plan.fully_covered {
                    return Err(ProtocolDispatchLowerError::UnsupportedGraphShape(
                        "open protocol matrix cannot end in fail",
                    ));
                }
                let Some(last) = tests.pop() else {
                    return Err(ProtocolDispatchLowerError::UnsupportedGraphShape(
                        "closed protocol matrix needs a final direct outcome",
                    ));
                };
                if tests.is_empty() {
                    return Err(ProtocolDispatchLowerError::UnsupportedGraphShape(
                        "closed protocol matrix needs a tested arm before its final direct else",
                    ));
                }
                return Ok(ProtocolDispatchLowering {
                    tests,
                    final_else: ProtocolDispatchTerminal::Direct { impl_fn: last.impl_fn },
                });
            }
        }
    }
}

fn direct_outcome_for_node(
    plan: &ProtocolDispatchMatrixPlan,
    node: GraphNodeId,
) -> Result<&ProtocolDirectOutcome, ProtocolDispatchLowerError> {
    let graph_node = plan
        .graph
        .graph
        .node(node)
        .ok_or(ProtocolDispatchLowerError::UnknownGraphNode(node))?;
    let DispatchNode::Outcome { outcome, .. } = graph_node else {
        return Err(ProtocolDispatchLowerError::UnsupportedGraphShape(
            "protocol match edge must target a direct outcome",
        ));
    };
    if Some(*outcome) == plan.fallback_outcome {
        return Err(ProtocolDispatchLowerError::FallbackOnMatch(*outcome));
    }
    direct_outcome(plan, *outcome).ok_or(ProtocolDispatchLowerError::UnknownOutcome(*outcome))
}

fn direct_outcome(plan: &ProtocolDispatchMatrixPlan, outcome: OutcomeId) -> Option<&ProtocolDirectOutcome> {
    plan.direct_outcomes.iter().find(|direct| direct.outcome == outcome)
}

/// Replace the protocol-call terminator in one block with the matrix dispatch cascade.
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
fn apply_protocol_dispatch_matrix_rewrite(module: &mut Module, rewrite: ProtocolDispatchRewrite) {
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
        Term::Call { args, continuation, .. } => (args.clone(), Some(continuation.clone()), false, false),
        Term::TailCall { args, is_back_edge, .. } => (args.clone(), None, true, *is_back_edge),
        other => unreachable!("rewrite block terminator is a protocol call, got {:?}", other),
    };
    let receiver = args[0];
    let num_tests = rewrite.lowering.tests.len();
    debug_assert!(
        num_tests > 0,
        "protocol matrix lowerer rejects empty executable matrices"
    );
    let mut direct_impls = rewrite
        .lowering
        .tests
        .iter()
        .map(|test| test.impl_fn)
        .collect::<Vec<_>>();
    let final_else_is_fallback = rewrite.lowering.final_else == ProtocolDispatchTerminal::Fallback;
    if let ProtocolDispatchTerminal::Direct { impl_fn } = rewrite.lowering.final_else {
        direct_impls.push(impl_fn);
    }
    let direct_count = direct_impls.len();

    let var_base = max_var(f) + 1;
    let block_base = max_block(f) + 1;
    // Block id layout: direct outcome blocks, then (open only) the fallthrough
    // block, then the intermediate test blocks (tests 1..num_tests; test 0 is
    // the head block).
    let arm_block = |i: usize| BlockId(block_base + i as u32);
    let fallthrough_block = BlockId(block_base + direct_count as u32);
    let test_extra_base = block_base + direct_count as u32 + u32::from(final_else_is_fallback);
    let test_point = |i: usize| {
        if i == 0 {
            rewrite.block_id
        } else {
            BlockId(test_extra_base + (i as u32 - 1))
        }
    };
    let final_else = if final_else_is_fallback {
        fallthrough_block
    } else {
        arm_block(direct_count - 1)
    };

    let arm_terminator = |impl_fn: FnId| -> Term {
        let ident = CallsiteIdent::from_source(Span::DUMMY);
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
    // blocks. Tested arm i branches then→arm i, else→the next test point, or
    // the final `else` (the untested last arm, or the fallthrough).
    let mut new_blocks: Vec<Block> = Vec::with_capacity(num_tests + direct_count + usize::from(final_else_is_fallback));
    for i in 0..num_tests {
        let tv = Var(var_base + i as u32);
        let test_stmt = Stmt::Let(
            tv,
            Prim::TypeTest(receiver, Box::new(rewrite.lowering.tests[i].target_ty.clone())),
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

    // One direct outcome block per target, each a direct call to the impl.
    for (i, impl_fn) in direct_impls.into_iter().enumerate() {
        new_blocks.push(Block {
            id: arm_block(i),
            params: vec![],
            stmts: vec![],
            terminator: arm_terminator(impl_fn),
        });
    }

    // Open receiver: the fallthrough preserves the original stub call so a
    // value matching no arm halts exactly as before the rewrite.
    if final_else_is_fallback {
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
