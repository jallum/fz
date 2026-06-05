use crate::frontend::spec_registry::{BestCoverCandidate, SpecRegistry, best_covering_candidate};
use crate::fz_ir::{
    Block, BlockId, CallsiteId, EmitSlot, FnId, FnIr, Module, Prim, SpecId, Stmt, Term, Var, visit_prim_vars,
    visit_term_vars,
};
use crate::ir_dce::{collect_used, dce_fn};
use crate::ir_fold::fold_planned_body;
use crate::ir_fuse::{subst_prim, subst_stmt, subst_term};
use crate::ir_planner::callgraph::entry_seeds;
use crate::ir_planner::fn_types::{
    CallEdgePlan, CallableCapability, EffectSummary, ModulePlan, SpecKey, SpecPlan, SpecReachabilityRole,
    spec_key_for_fn_id, spec_key_input_tys,
};
use crate::ir_planner::reachable::reachable_spec_ids;
use crate::ir_planner::type_fn::type_fn;
use crate::telemetry::Telemetry;
use crate::types::{ClosureTypes, Ty, Types, key_slot_var_count};
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

pub(crate) struct PlannedProgram {
    spec_registry: SpecRegistry,
    spec_keys: Vec<SpecKey>,
    spec_fn_indices: Vec<Option<usize>>,
    bodies: Vec<PlannedBody>,
    body_index_by_spec_slot: Vec<Option<usize>>,
    callable_entries: BTreeMap<u32, CallableEntryPlan>,
    reachable_specs: HashSet<u32>,
}

pub(crate) struct PlannedBody {
    pub spec_id: SpecId,
    pub spec_key: SpecKey,
    pub body_key: crate::ir_planner::fn_types::BodyKey,
    pub fn_id: FnId,
    pub fn_idx: usize,
    pub spec_plan: SpecPlan,
    pub body: FnIr,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct PlannedProgramStats {
    pub spec_slot_count: usize,
    pub planned_body_count: usize,
    pub sentinel_spec_count: usize,
    pub folded_prim_count: usize,
    pub folded_branch_count: usize,
    pub fused_block_count: usize,
    pub direct_call_inline_count: usize,
    pub continuation_inline_count: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct CallableEntryPlan {
    pub capture_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PlannedCallableEntrySelection {
    pub spec_id: u32,
    pub target_key: SpecKey,
    pub candidate_count: usize,
}

impl PlannedProgram {
    pub(crate) fn spec_registry(&self) -> &SpecRegistry {
        &self.spec_registry
    }

    pub(crate) fn spec_count(&self) -> usize {
        self.spec_registry.len()
    }

    pub(crate) fn spec_keys(&self) -> &[SpecKey] {
        &self.spec_keys
    }

    pub(crate) fn spec_fn_indices(&self) -> &[Option<usize>] {
        &self.spec_fn_indices
    }

    pub(crate) fn callable_entries(&self) -> &BTreeMap<u32, CallableEntryPlan> {
        &self.callable_entries
    }

    pub(crate) fn reachable_specs(&self) -> &HashSet<u32> {
        &self.reachable_specs
    }

    pub(crate) fn executable_body(&self, spec_id: SpecId) -> &PlannedBody {
        let body_index = self
            .body_index_by_spec_slot
            .get(spec_id.0 as usize)
            .and_then(|idx| *idx)
            .expect("registered executable spec must have a planned body");
        let body = &self.bodies[body_index];
        debug_assert_eq!(
            body.body_key,
            self.spec_keys[spec_id.0 as usize].body_key(),
            "spec slot and planned body must agree on semantic body identity"
        );
        body
    }
}

/// Materialize the executable projection of a canonical module and its
/// authoritative plan.
///
/// `Module` remains the lowered source-shape IR. `ModulePlan` remains the
/// semantic authority. `PlannedProgram` is the codegen-facing projection:
/// stable `SpecId` registration, per-spec plan lookup, and exact folded bodies.
pub(crate) fn materialize_program<T>(
    t: &mut T,
    module: &Module,
    module_plan: &ModulePlan,
    tel: &dyn Telemetry,
) -> PlannedProgram
where
    T: Types<Ty = Ty> + ClosureTypes,
{
    let spec_registry = build_spec_registry(t, module, module_plan);
    let spec_keys: Vec<SpecKey> = spec_registry.iter().map(|(_, key)| key.clone()).collect();
    let mut idx_of: HashMap<FnId, usize> = HashMap::new();
    for (i, f) in module.fns.iter().enumerate() {
        idx_of.insert(f.id, i);
    }

    let spec_fn_indices: Vec<Option<usize>> = spec_keys
        .iter()
        .map(|key| {
            if !module_plan.specs.contains_key(key) {
                return None;
            }
            idx_of.get(&key.fn_id).copied()
        })
        .collect();
    let spec_plans: Vec<Option<&SpecPlan>> = spec_keys
        .iter()
        .enumerate()
        .map(|(sid, key)| {
            spec_fn_indices[sid]?;
            module_plan.specs.get(key)
        })
        .collect();
    let mut folded_prim_count = 0;
    let mut folded_branch_count = 0;
    let mut fused_block_count = 0;
    let mut direct_call_inline_count = 0;
    let mut continuation_inline_count = 0;
    let mut bodies: Vec<PlannedBody> = Vec::new();
    let mut body_index_by_spec_slot = Vec::with_capacity(spec_registry.len());
    for sid in 0..spec_registry.len() {
        match (spec_fn_indices[sid], spec_plans[sid]) {
            (Some(fn_idx), Some(spec_plan)) => {
                // One materialized body per spec. `ReturnDemand` is part of the
                // spec identity, and codegen lowers the return ABI from it, so
                // demand siblings (same `BodyKey`, different demand — e.g. a
                // `tuple_fields` and a `value` reach of one helper) are distinct
                // native bodies, exactly like distinct type specializations.
                // They are not merged: merging would force one return ABI onto
                // callers that asked for the other.
                let body_key = spec_keys[sid].body_key();
                let mut body = module.fns[fn_idx].clone();
                let rewrite_stats = inline_single_entry_direct_calls(
                    t,
                    module,
                    module_plan,
                    &spec_registry,
                    &spec_keys,
                    &spec_plans,
                    spec_plan,
                    &mut body,
                );
                let mut materialized_plan = if rewrite_stats.changed() {
                    retype_materialized_body(
                        t,
                        module,
                        &body,
                        &spec_keys[sid],
                        spec_plan,
                        &rewrite_stats.call_edges_to_add,
                    )
                } else {
                    spec_plan.clone()
                };
                let fold_stats = fold_planned_body(t, &mut body, &materialized_plan);
                let body_fused_block_count = if rewrite_stats.changed() {
                    fuse_single_predecessor_goto_blocks(&mut body)
                } else {
                    0
                };
                if rewrite_stats.changed() && !materialization_dce_is_observable(module_plan, body.id) {
                    dce_fn(module.module_path(), &mut body, tel);
                    materialized_plan = retype_materialized_body(
                        t,
                        module,
                        &body,
                        &spec_keys[sid],
                        spec_plan,
                        &rewrite_stats.call_edges_to_add,
                    );
                } else if body_fused_block_count > 0 {
                    materialized_plan = retype_materialized_body(
                        t,
                        module,
                        &body,
                        &spec_keys[sid],
                        spec_plan,
                        &rewrite_stats.call_edges_to_add,
                    );
                }
                folded_prim_count += fold_stats.prim_count;
                folded_branch_count += fold_stats.branch_count;
                fused_block_count += body_fused_block_count;
                direct_call_inline_count += rewrite_stats.direct_call_inline_count;
                continuation_inline_count += rewrite_stats.continuation_inline_count;
                let orphan_call_edges = materialized_orphan_call_edges(&body, &materialized_plan);
                let body_index = bodies.len();
                tel.execute(
                    &["fz", "planner", "body_materialized"],
                    &crate::measurements! {
                        spec_id: sid as u64,
                        fn_id: body.id.0 as u64,
                        fn_idx: fn_idx as u64,
                        block_count: body.blocks.len() as u64,
                        folded_prim_count: fold_stats.prim_count as u64,
                        folded_branch_count: fold_stats.branch_count as u64,
                        fused_block_count: body_fused_block_count as u64,
                        direct_call_inline_count: rewrite_stats.direct_call_inline_count as u64,
                        continuation_inline_count: rewrite_stats.continuation_inline_count as u64,
                        orphan_call_edge_count: orphan_call_edges.len() as u64,
                    },
                    &crate::metadata! {
                        role: "authoritative",
                        module_path: module.module_path().to_owned(),
                        fn_name: body.name.clone(),
                        spec_key: format!("{:?}", spec_keys[sid]),
                        orphan_call_edges: orphan_call_edges,
                    },
                );
                bodies.push(PlannedBody {
                    spec_id: SpecId(sid as u32),
                    spec_key: spec_keys[sid].clone(),
                    body_key,
                    fn_id: body.id,
                    fn_idx,
                    spec_plan: materialized_plan,
                    body,
                });
                body_index_by_spec_slot.push(Some(body_index));
            }
            _ => body_index_by_spec_slot.push(None),
        }
    }
    let pre_rewrite_reachable_specs = reachable_spec_ids(t, &spec_registry, module_plan);
    let materialized_reachability = materialized_reachable_specs(
        t,
        module,
        module_plan,
        &spec_registry,
        &bodies,
        &body_index_by_spec_slot,
    );
    let reachable_specs = materialized_reachability.specs;
    let callable_entries =
        build_callable_entries(t, &bodies, &spec_registry, &body_index_by_spec_slot, &reachable_specs);
    let make_closure_callable_gaps = make_closure_callable_gap_issues(
        t,
        module,
        &bodies,
        &spec_registry,
        &body_index_by_spec_slot,
        &callable_entries,
        &reachable_specs,
    );

    let planned_body_count = bodies.len();
    let post_plan_reachability_growth_count = reachable_specs.difference(&pre_rewrite_reachable_specs).count();
    let post_plan_reachability_pruned_count = pre_rewrite_reachable_specs.difference(&reachable_specs).count();
    let stats = PlannedProgramStats {
        spec_slot_count: spec_registry.len(),
        planned_body_count,
        sentinel_spec_count: spec_registry.len() - planned_body_count,
        folded_prim_count,
        folded_branch_count,
        fused_block_count,
        direct_call_inline_count,
        continuation_inline_count,
    };
    tel.execute(
        &["fz", "planner", "materialized"],
        &crate::measurements! {
            spec_slot_count: stats.spec_slot_count as u64,
            planned_body_count: stats.planned_body_count as u64,
            sentinel_spec_count: stats.sentinel_spec_count as u64,
            folded_prim_count: stats.folded_prim_count as u64,
            folded_branch_count: stats.folded_branch_count as u64,
            fused_block_count: stats.fused_block_count as u64,
            direct_call_inline_count: stats.direct_call_inline_count as u64,
            continuation_inline_count: stats.continuation_inline_count as u64,
            reachable_spec_count: reachable_specs.len() as u64,
            post_plan_reachability_growth_count: post_plan_reachability_growth_count as u64,
            post_plan_reachability_pruned_count: post_plan_reachability_pruned_count as u64,
            materialized_reachability_missing_body_count:
                materialized_reachability.missing_body_specs.len() as u64,
            make_closure_callable_gap_count: make_closure_callable_gaps.len() as u64,
        },
        &crate::metadata! {
            role: "authoritative",
            module_path: module.module_path().to_owned(),
            reachable_specs: display_spec_ids(&reachable_specs),
            materialized_reachability_missing_body_specs:
                materialized_reachability.missing_body_specs.clone(),
            make_closure_callable_gaps: make_closure_callable_gaps.clone(),
        },
    );

    PlannedProgram {
        spec_registry,
        spec_keys,
        spec_fn_indices,
        bodies,
        body_index_by_spec_slot,
        callable_entries,
        reachable_specs,
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct MaterializeRewriteStats {
    direct_call_inline_count: usize,
    continuation_inline_count: usize,
    call_edges_to_add: HashMap<CallsiteId, CallEdgePlan>,
}

impl MaterializeRewriteStats {
    fn changed(&self) -> bool {
        self.direct_call_inline_count != 0 || self.continuation_inline_count != 0
    }
}

#[allow(clippy::too_many_arguments)]
fn inline_single_entry_direct_calls<T>(
    t: &mut T,
    module: &Module,
    module_plan: &ModulePlan,
    spec_registry: &SpecRegistry,
    spec_keys: &[SpecKey],
    spec_plans: &[Option<&SpecPlan>],
    caller_plan: &SpecPlan,
    body: &mut FnIr,
) -> MaterializeRewriteStats
where
    T: Types<Ty = Ty> + ClosureTypes,
{
    let mut stats = MaterializeRewriteStats::default();
    let mut next_var = next_var_id(body);
    let mut next_block = next_block_id(body);
    for block_idx in 0..body.blocks.len() {
        let term = body.blocks[block_idx].terminator.clone();
        let Some(inlined) = build_known_call_inline(
            t,
            module,
            module_plan,
            spec_registry,
            spec_keys,
            spec_plans,
            caller_plan,
            body.id,
            &term,
            &mut next_var,
            &mut next_block,
        ) else {
            continue;
        };
        body.blocks[block_idx].stmts.extend(inlined.stmts);
        body.blocks[block_idx].terminator = inlined.terminator;
        body.blocks.extend(inlined.extra_blocks);
        stats.call_edges_to_add.extend(inlined.call_edges);
        stats.direct_call_inline_count += 1;
        if inlined.inlined_continuation {
            stats.continuation_inline_count += 1;
        }
    }
    stats
}

struct InlinedDirectCall {
    stmts: Vec<Stmt>,
    terminator: Term,
    extra_blocks: Vec<Block>,
    call_edges: HashMap<CallsiteId, CallEdgePlan>,
    inlined_continuation: bool,
}

#[allow(clippy::too_many_arguments)]
fn build_known_call_inline<T>(
    t: &mut T,
    module: &Module,
    module_plan: &ModulePlan,
    spec_registry: &SpecRegistry,
    spec_keys: &[SpecKey],
    spec_plans: &[Option<&SpecPlan>],
    caller_plan: &SpecPlan,
    caller_fn_id: FnId,
    term: &Term,
    next_var: &mut u32,
    next_block: &mut u32,
) -> Option<InlinedDirectCall>
where
    T: Types<Ty = Ty> + ClosureTypes,
{
    let (ident, args, continuation, closure, producer_slot) = match term {
        Term::Call {
            ident,
            callee: _,
            args,
            continuation,
        } => (ident, args, Some(continuation), None, EmitSlot::Direct),
        Term::TailCall {
            ident,
            callee: _,
            args,
            is_back_edge: _,
        } => (ident, args, None, None, EmitSlot::Direct),
        Term::CallClosure {
            ident,
            closure,
            args,
            continuation,
        } => (ident, args, Some(continuation), Some(*closure), EmitSlot::ClosureCall),
        Term::TailCallClosure { ident, closure, args } => (ident, args, None, Some(*closure), EmitSlot::ClosureCall),
        _ => return None,
    };
    let direct_callsite = CallsiteId::new(caller_fn_id, ident, producer_slot);
    let direct_target = caller_plan.local_call_target(&direct_callsite)?;
    if let Some(closure) = closure {
        let inlineable_closure_target =
            if let Some(info) = caller_plan.vars.get(&closure).and_then(|ty| t.closure_lit_parts(ty)) {
                FnId::from(info.target) == direct_target.fn_id && info.captures.is_empty()
            } else {
                let capability = caller_plan.callable_capabilities.get(&closure)?;
                match capability {
                    CallableCapability::KnownFn(fn_id) => *fn_id == direct_target.fn_id,
                    CallableCapability::KnownClosure { fn_id, captures, .. } => {
                        *fn_id == direct_target.fn_id && captures.is_empty()
                    }
                    CallableCapability::OpaqueCallable => false,
                }
            };
        if !inlineable_closure_target {
            return None;
        }
    }
    if direct_target.fn_id == caller_fn_id {
        return None;
    }
    let direct_effects = module_plan
        .fn_effects
        .get(&direct_target.fn_id)
        .copied()
        .unwrap_or_default();
    if !direct_callee_is_inline_safe(direct_effects) {
        return None;
    }
    let direct_sid = spec_registry.resolve_spec_key(t, direct_target)?;
    let direct_key = spec_keys.get(direct_sid.0 as usize)?;
    let direct_plan = spec_plans.get(direct_sid.0 as usize).and_then(|plan| *plan)?;
    let direct_fn = module.fn_by_id(direct_key.fn_id);
    if module.boundary_fns.contains(&direct_fn.id) {
        return None;
    }
    inlineable_direct_return_graph(module, direct_fn, direct_plan)?;

    if let Some(continuation) = continuation {
        let cont_callsite = CallsiteId::new(caller_fn_id, ident, EmitSlot::Cont);
        let cont_target = caller_plan.local_call_target(&cont_callsite)?;
        if cont_target.fn_id == caller_fn_id {
            return None;
        }
        let cont_sid = spec_registry.resolve_spec_key(t, cont_target)?;
        let cont_key = spec_keys.get(cont_sid.0 as usize)?;
        let cont_plan = spec_plans.get(cont_sid.0 as usize).and_then(|plan| *plan)?;
        let cont_fn = module.fn_by_id(cont_key.fn_id);
        if module.boundary_fns.contains(&cont_fn.id) || !continuation_graph_can_move_into_caller(module, cont_fn) {
            return None;
        }

        return clone_direct_return_graph(
            direct_fn,
            direct_plan,
            cont_fn,
            cont_plan,
            caller_fn_id,
            args,
            continuation,
            next_var,
            next_block,
        );
    }

    clone_direct_tail_graph(direct_fn, direct_plan, caller_fn_id, args, next_var, next_block)
}

fn direct_callee_is_inline_safe(effects: EffectSummary) -> bool {
    !effects.allocates
        && !effects.observable
        && !effects.reads_allocation_stats
        && !effects.scheduler_visible
        && !effects.halts
        && !effects.calls_opaque
}

fn inlineable_direct_return_graph(module: &Module, f: &FnIr, plan: &SpecPlan) -> Option<()> {
    if !plan.reachable_blocks.contains(&f.entry) {
        return None;
    }
    if !f.physical_entry_params.is_empty() || !f.physical_capabilities.is_empty() {
        return None;
    }
    let mut saw_return = false;
    for block in f
        .blocks
        .iter()
        .filter(|block| plan.reachable_blocks.contains(&block.id))
    {
        if !stmts_can_move_into_caller(module, &block.stmts) || term_targets_block(&block.terminator, f.entry) {
            return None;
        }
        match block.terminator {
            Term::Goto(_, _) | Term::If { .. } => {}
            Term::Return(_) => {
                saw_return = true;
            }
            Term::Call { .. }
            | Term::TailCall { .. }
            | Term::CallClosure { .. }
            | Term::TailCallClosure { .. }
            | Term::Halt(_)
            | Term::ReceiveMatched { .. } => return None,
        }
    }
    if !saw_return {
        return None;
    }
    Some(())
}

fn stmts_can_move_into_caller(module: &Module, stmts: &[Stmt]) -> bool {
    stmts.iter().all(|stmt| {
        let Stmt::Let(_, prim) = stmt;
        match prim {
            Prim::Extern(_, extern_id, _) => !module.extern_by_id(*extern_id).variadic,
            _ => true,
        }
    })
}

fn continuation_graph_can_move_into_caller(module: &Module, f: &FnIr) -> bool {
    if (!f.physical_entry_params.is_empty() || !f.physical_capabilities.is_empty())
        && f.blocks.iter().any(|block| !block.stmts.is_empty())
    {
        return false;
    }
    f.blocks.iter().all(|block| {
        stmts_can_move_into_caller(module, &block.stmts) && !matches!(block.terminator, Term::ReceiveMatched { .. })
    })
}

struct ClonedContinuationGraph {
    entry_block: BlockId,
    blocks: Vec<Block>,
    call_edges: HashMap<CallsiteId, CallEdgePlan>,
}

fn clone_direct_return_graph(
    direct_fn: &FnIr,
    direct_plan: &SpecPlan,
    cont_fn: &FnIr,
    cont_plan: &SpecPlan,
    caller_fn_id: FnId,
    args: &[Var],
    continuation: &crate::fz_ir::Cont,
    next_var: &mut u32,
    next_block: &mut u32,
) -> Option<InlinedDirectCall> {
    let direct_entry = direct_fn.block(direct_fn.entry);
    if direct_entry.params.len() != args.len() {
        return None;
    }
    if cont_fn.block(cont_fn.entry).params.len() != continuation.captured.len() + 1 {
        return None;
    }

    let cloned_cont = clone_continuation_entry_graph(cont_fn, cont_plan, caller_fn_id, next_var, next_block)?;

    let mut block_subst = HashMap::new();
    for block in direct_fn
        .blocks
        .iter()
        .filter(|block| direct_plan.reachable_blocks.contains(&block.id))
    {
        if block.id != direct_fn.entry {
            block_subst.insert(block.id, fresh_block(next_block));
        }
    }

    let mut var_subst = HashMap::new();
    for (param, arg) in direct_entry.params.iter().zip(args) {
        var_subst.insert(*param, *arg);
    }
    for block in direct_fn
        .blocks
        .iter()
        .filter(|block| direct_plan.reachable_blocks.contains(&block.id))
    {
        if block.id == direct_fn.entry {
            continue;
        }
        for param in &block.params {
            var_subst.insert(*param, fresh_var(next_var));
        }
    }

    let mut call_edges = HashMap::new();
    call_edges.extend(cloned_cont.call_edges);
    let mut extra_blocks = cloned_cont.blocks;
    let mut entry_stmts = Vec::new();
    clone_stmts_with_fresh_defs(&direct_entry.stmts, &mut var_subst, next_var, &mut entry_stmts);
    let entry_terminator = clone_direct_graph_terminator(
        &direct_entry.terminator,
        cloned_cont.entry_block,
        continuation,
        &mut var_subst,
        &block_subst,
    )?;

    for block in direct_fn
        .blocks
        .iter()
        .filter(|block| direct_plan.reachable_blocks.contains(&block.id))
    {
        if block.id == direct_fn.entry {
            continue;
        }
        let mut stmts = Vec::new();
        clone_stmts_with_fresh_defs(&block.stmts, &mut var_subst, next_var, &mut stmts);
        let terminator = clone_direct_graph_terminator(
            &block.terminator,
            cloned_cont.entry_block,
            continuation,
            &mut var_subst,
            &block_subst,
        )?;
        let params = block.params.iter().map(|param| subst_var(*param, &var_subst)).collect();
        let id = *block_subst.get(&block.id)?;
        extra_blocks.push(Block {
            id,
            params,
            stmts,
            terminator,
        });
    }

    Some(InlinedDirectCall {
        stmts: entry_stmts,
        terminator: entry_terminator,
        extra_blocks,
        call_edges,
        inlined_continuation: true,
    })
}

fn clone_direct_tail_graph(
    direct_fn: &FnIr,
    direct_plan: &SpecPlan,
    caller_fn_id: FnId,
    args: &[Var],
    next_var: &mut u32,
    next_block: &mut u32,
) -> Option<InlinedDirectCall> {
    let direct_entry = direct_fn.block(direct_fn.entry);
    if direct_entry.params.len() != args.len() {
        return None;
    }

    let mut block_subst = HashMap::new();
    for block in direct_fn
        .blocks
        .iter()
        .filter(|block| direct_plan.reachable_blocks.contains(&block.id))
    {
        if block.id != direct_fn.entry {
            block_subst.insert(block.id, fresh_block(next_block));
        }
    }

    let mut var_subst = HashMap::new();
    for (param, arg) in direct_entry.params.iter().zip(args) {
        var_subst.insert(*param, *arg);
    }
    for block in direct_fn
        .blocks
        .iter()
        .filter(|block| direct_plan.reachable_blocks.contains(&block.id))
    {
        if block.id == direct_fn.entry {
            continue;
        }
        for param in &block.params {
            var_subst.insert(*param, fresh_var(next_var));
        }
    }

    let mut extra_blocks = Vec::new();
    let mut entry_stmts = Vec::new();
    clone_stmts_with_fresh_defs(&direct_entry.stmts, &mut var_subst, next_var, &mut entry_stmts);
    let entry_terminator = clone_tail_graph_terminator(&direct_entry.terminator, &mut var_subst, &block_subst)?;

    let mut call_edges = HashMap::new();
    add_remapped_call_edges(
        direct_fn.id,
        caller_fn_id,
        &direct_entry.terminator,
        direct_plan,
        &mut call_edges,
    );
    for block in direct_fn
        .blocks
        .iter()
        .filter(|block| direct_plan.reachable_blocks.contains(&block.id))
    {
        if block.id == direct_fn.entry {
            continue;
        }
        let mut stmts = Vec::new();
        clone_stmts_with_fresh_defs(&block.stmts, &mut var_subst, next_var, &mut stmts);
        let terminator = clone_tail_graph_terminator(&block.terminator, &mut var_subst, &block_subst)?;
        add_remapped_call_edges(
            direct_fn.id,
            caller_fn_id,
            &block.terminator,
            direct_plan,
            &mut call_edges,
        );
        let params = block.params.iter().map(|param| subst_var(*param, &var_subst)).collect();
        let id = *block_subst.get(&block.id)?;
        extra_blocks.push(Block {
            id,
            params,
            stmts,
            terminator,
        });
    }

    Some(InlinedDirectCall {
        stmts: entry_stmts,
        terminator: entry_terminator,
        extra_blocks,
        call_edges,
        inlined_continuation: false,
    })
}

#[allow(clippy::too_many_arguments)]
fn clone_direct_graph_terminator(
    term: &Term,
    cont_entry_block: BlockId,
    continuation: &crate::fz_ir::Cont,
    var_subst: &mut HashMap<Var, Var>,
    block_subst: &HashMap<BlockId, BlockId>,
) -> Option<Term> {
    if let Term::Return(result) = term {
        let mut args = Vec::with_capacity(continuation.captured.len() + 1);
        args.push(subst_var(*result, var_subst));
        args.extend(continuation.captured.iter().copied());
        return Some(Term::Goto(cont_entry_block, args));
    }
    subst_term_with_blocks(term, var_subst, block_subst)
}

fn clone_tail_graph_terminator(
    term: &Term,
    var_subst: &mut HashMap<Var, Var>,
    block_subst: &HashMap<BlockId, BlockId>,
) -> Option<Term> {
    if let Term::Return(result) = term {
        return Some(Term::Return(subst_var(*result, var_subst)));
    }
    subst_term_with_blocks(term, var_subst, block_subst)
}

fn clone_continuation_entry_graph(
    cont_fn: &FnIr,
    cont_plan: &SpecPlan,
    caller_fn_id: FnId,
    next_var: &mut u32,
    next_block: &mut u32,
) -> Option<ClonedContinuationGraph> {
    let mut block_subst = HashMap::new();
    for block in &cont_fn.blocks {
        block_subst.insert(block.id, fresh_block(next_block));
    }

    let mut var_subst = HashMap::new();
    for block in &cont_fn.blocks {
        for param in &block.params {
            var_subst.insert(*param, fresh_var(next_var));
        }
    }

    let mut call_edges = HashMap::new();
    let mut blocks = Vec::new();
    for block in cont_fn
        .blocks
        .iter()
        .filter(|block| block.id == cont_fn.entry)
        .chain(cont_fn.blocks.iter().filter(|block| block.id != cont_fn.entry))
    {
        let mut stmts = Vec::new();
        clone_stmts_with_fresh_defs(&block.stmts, &mut var_subst, next_var, &mut stmts);
        let terminator = subst_term_with_blocks(&block.terminator, &var_subst, &block_subst)?;
        add_remapped_call_edges(cont_fn.id, caller_fn_id, &block.terminator, cont_plan, &mut call_edges);
        let params = block.params.iter().map(|param| subst_var(*param, &var_subst)).collect();
        let id = *block_subst.get(&block.id)?;
        blocks.push(Block {
            id,
            params,
            stmts,
            terminator,
        });
    }

    Some(ClonedContinuationGraph {
        entry_block: *block_subst.get(&cont_fn.entry)?,
        blocks,
        call_edges,
    })
}

fn subst_term_with_blocks(
    term: &Term,
    var_subst: &HashMap<Var, Var>,
    block_subst: &HashMap<BlockId, BlockId>,
) -> Option<Term> {
    let sv = |v: Var| subst_var(v, var_subst);
    let sb = |b: &BlockId| block_subst.get(b).copied();
    Some(match term {
        Term::Goto(target, args) => Term::Goto(sb(target)?, args.iter().map(|arg| sv(*arg)).collect()),
        Term::If {
            cond,
            then_b,
            else_b,
            origin,
        } => Term::If {
            cond: sv(*cond),
            then_b: sb(then_b)?,
            else_b: sb(else_b)?,
            origin: *origin,
        },
        Term::ReceiveMatched { .. } => return None,
        _ => subst_term(term, var_subst),
    })
}

fn term_targets_block(term: &Term, target: BlockId) -> bool {
    match term {
        Term::Goto(block, _) => *block == target,
        Term::If { then_b, else_b, .. } => *then_b == target || *else_b == target,
        _ => false,
    }
}

fn add_remapped_call_edges(
    source_fn_id: FnId,
    target_fn_id: FnId,
    source_term: &Term,
    source_plan: &SpecPlan,
    out: &mut HashMap<CallsiteId, CallEdgePlan>,
) {
    let Some(ident) = source_term.ident() else {
        return;
    };
    for slot in call_edge_slots(source_term) {
        let source = CallsiteId::new(source_fn_id, ident, slot);
        let Some(edge) = source_plan.call_edges.get(&source) else {
            continue;
        };
        out.insert(CallsiteId::new(target_fn_id, ident, slot), edge.clone());
    }
}

fn call_edge_slots(term: &Term) -> Vec<EmitSlot> {
    match term {
        Term::Call { .. } => vec![EmitSlot::Direct, EmitSlot::Cont],
        Term::TailCall { .. } => vec![EmitSlot::Direct],
        Term::CallClosure { .. } => vec![EmitSlot::ClosureCall, EmitSlot::Cont],
        Term::TailCallClosure { .. } => vec![EmitSlot::ClosureCall],
        Term::ReceiveMatched { .. } => vec![EmitSlot::Cont],
        _ => Vec::new(),
    }
}

fn fuse_single_predecessor_goto_blocks(f: &mut FnIr) -> usize {
    let mut fused = 0;
    while let Some(fusion) = next_single_predecessor_goto_fusion(f) {
        let target_block = f.blocks[fusion.target_idx].clone();
        let subst: HashMap<Var, Var> = target_block
            .params
            .iter()
            .copied()
            .zip(fusion.args.iter().copied())
            .collect();
        let moved_stmts = target_block
            .stmts
            .iter()
            .map(|stmt| subst_stmt(stmt, &subst))
            .collect::<Vec<_>>();
        let moved_terminator = subst_term(&target_block.terminator, &subst);
        f.blocks[fusion.source_idx].stmts.extend(moved_stmts);
        f.blocks[fusion.source_idx].terminator = moved_terminator;
        for fact in &mut f.physical_capabilities {
            *fact = fact.map_vars(|var| subst_var(var, &subst));
        }
        f.blocks.remove(fusion.target_idx);
        f.dedup_physical_facts();
        fused += 1;
    }
    fused
}

struct GotoFusion {
    source_idx: usize,
    target_idx: usize,
    args: Vec<Var>,
}

fn next_single_predecessor_goto_fusion(f: &FnIr) -> Option<GotoFusion> {
    let predecessor_counts = block_predecessor_counts(f);
    for (source_idx, block) in f.blocks.iter().enumerate() {
        let Term::Goto(target, args) = &block.terminator else {
            continue;
        };
        if *target == f.entry || *target == block.id {
            continue;
        }
        if predecessor_counts.get(target).copied().unwrap_or_default() != 1 {
            continue;
        }
        let Some(target_idx) = f.blocks.iter().position(|candidate| candidate.id == *target) else {
            continue;
        };
        let target_block = &f.blocks[target_idx];
        if target_block.params.len() != args.len()
            || term_targets_block(&target_block.terminator, block.id)
            || block_params_used_outside_block(f, target_block)
        {
            continue;
        }
        return Some(GotoFusion {
            source_idx,
            target_idx,
            args: args.clone(),
        });
    }
    None
}

fn block_params_used_outside_block(f: &FnIr, target: &Block) -> bool {
    if target.params.is_empty() {
        return false;
    }
    let params = target.params.iter().copied().collect::<HashSet<_>>();
    for block in &f.blocks {
        if block.id == target.id {
            continue;
        }
        for stmt in &block.stmts {
            let Stmt::Let(_, prim) = stmt;
            let mut used = false;
            visit_prim_vars(prim, &mut |var| {
                used |= params.contains(&var);
            });
            if used {
                return true;
            }
        }
        let mut used = false;
        visit_term_vars(&block.terminator, &mut |var| {
            used |= params.contains(&var);
        });
        if used {
            return true;
        }
    }
    false
}

fn block_predecessor_counts(f: &FnIr) -> HashMap<BlockId, usize> {
    let mut counts = HashMap::new();
    for block in &f.blocks {
        match &block.terminator {
            Term::Goto(target, _) => {
                *counts.entry(*target).or_default() += 1;
            }
            Term::If { then_b, else_b, .. } => {
                *counts.entry(*then_b).or_default() += 1;
                *counts.entry(*else_b).or_default() += 1;
            }
            _ => {}
        }
    }
    counts
}

fn clone_stmts_with_fresh_defs(stmts: &[Stmt], subst: &mut HashMap<Var, Var>, next_var: &mut u32, out: &mut Vec<Stmt>) {
    for stmt in stmts {
        let Stmt::Let(dest, prim) = stmt;
        let fresh = fresh_var(next_var);
        let prim = subst_prim(prim, subst);
        subst.insert(*dest, fresh);
        out.push(Stmt::Let(fresh, prim));
    }
}

fn subst_var(var: Var, subst: &HashMap<Var, Var>) -> Var {
    *subst.get(&var).unwrap_or(&var)
}

fn fresh_var(next_var: &mut u32) -> Var {
    let var = Var(*next_var);
    *next_var += 1;
    var
}

fn fresh_block(next_block: &mut u32) -> BlockId {
    let block = BlockId(*next_block);
    *next_block += 1;
    block
}

fn next_var_id(f: &FnIr) -> u32 {
    let mut max_seen = 0;
    let mut saw_var = false;
    let mut record = |var: Var| {
        saw_var = true;
        max_seen = max_seen.max(var.0);
    };
    for block in &f.blocks {
        for param in &block.params {
            record(*param);
        }
        for stmt in &block.stmts {
            let Stmt::Let(dest, prim) = stmt;
            record(*dest);
            visit_prim_vars(prim, &mut record);
        }
        visit_term_vars(&block.terminator, &mut record);
    }
    if saw_var { max_seen + 1 } else { 0 }
}

fn next_block_id(f: &FnIr) -> u32 {
    f.blocks.iter().map(|block| block.id.0).max().unwrap_or(0) + 1
}

fn retype_materialized_body<T>(
    t: &mut T,
    module: &Module,
    body: &FnIr,
    spec_key: &SpecKey,
    source_plan: &SpecPlan,
    extra_call_edges: &HashMap<CallsiteId, CallEdgePlan>,
) -> SpecPlan
where
    T: Types<Ty = Ty> + ClosureTypes,
{
    let input_tys = spec_key_input_tys(t, spec_key);
    let mut materialized = type_fn(t, body, module, Some(&input_tys));
    materialized.call_edges = materialized_call_edges(source_plan, extra_call_edges, body);
    materialized.callable_entry_targets = source_plan.callable_entry_targets.clone();
    materialized.extern_marshals = source_plan.extern_marshals.clone();
    materialized.brand_inners = source_plan.brand_inners.clone();
    materialized.opaque_inners = source_plan.opaque_inners.clone();
    materialized
}

fn materialized_call_edges(
    source_plan: &SpecPlan,
    extra_call_edges: &HashMap<CallsiteId, CallEdgePlan>,
    body: &FnIr,
) -> HashMap<CallsiteId, CallEdgePlan> {
    let callsites = materialized_callsite_ids(body);
    source_plan
        .call_edges
        .iter()
        .chain(extra_call_edges.iter())
        .filter(|(callsite, _)| callsite.slot == EmitSlot::CallableBoundary || callsites.contains(*callsite))
        .map(|(callsite, edge)| (callsite.clone(), edge.clone()))
        .collect()
}

fn materialized_callsite_ids(body: &FnIr) -> HashSet<CallsiteId> {
    let mut callsites = HashSet::new();
    for block in &body.blocks {
        let Some(ident) = block.terminator.ident() else {
            continue;
        };
        for slot in call_edge_slots(&block.terminator) {
            callsites.insert(CallsiteId::new(body.id, ident, slot));
        }
        if let Term::ReceiveMatched { clauses, after, .. } = &block.terminator {
            for clause in clauses {
                callsites.insert(CallsiteId::new(body.id, &clause.ident, EmitSlot::Cont));
            }
            if let Some(after) = after {
                callsites.insert(CallsiteId::new(body.id, &after.ident, EmitSlot::Cont));
            }
        }
    }
    callsites
}

fn materialized_orphan_call_edges(body: &FnIr, spec_plan: &SpecPlan) -> Vec<String> {
    let callsites = materialized_callsite_ids(body);
    let mut orphans = spec_plan
        .call_edges
        .keys()
        .filter(|callsite| {
            callsite.caller == body.id && callsite.slot != EmitSlot::CallableBoundary && !callsites.contains(*callsite)
        })
        .map(|callsite| {
            let span = callsite.ident.span();
            format!("{:?}@{}..{}", callsite.slot, span.start, span.end)
        })
        .collect::<Vec<_>>();
    orphans.sort();
    orphans
}

fn materialization_dce_is_observable(module_plan: &ModulePlan, fn_id: FnId) -> bool {
    module_plan
        .fn_effects
        .get(&fn_id)
        .is_some_and(|effects| effects.reads_allocation_stats)
}

fn make_closure_callable_gap_issues<T>(
    t: &mut T,
    module: &Module,
    bodies: &[PlannedBody],
    spec_registry: &SpecRegistry,
    body_index_by_spec_slot: &[Option<usize>],
    callable_entries: &BTreeMap<u32, CallableEntryPlan>,
    reachable_specs: &HashSet<u32>,
) -> Vec<String>
where
    T: Types<Ty = Ty> + ClosureTypes,
{
    let mut gaps = Vec::new();
    for planned_body in bodies {
        if !reachable_specs.contains(&planned_body.spec_id.0) {
            continue;
        }
        let spec_plan = &planned_body.spec_plan;
        let used_vars = collect_used(&planned_body.body);
        for blk in &planned_body.body.blocks {
            if !spec_plan.reachable_blocks.contains(&blk.id) {
                continue;
            }
            let block_env = spec_plan.block_envs.get(&blk.id);
            for stmt in &blk.stmts {
                let Stmt::Let(dest, prim) = stmt;
                let (lam_fn_id, captured) = match prim {
                    Prim::MakeFnRef(_, lam_fn_id) => (*lam_fn_id, &[][..]),
                    Prim::MakeClosure(_, lam_fn_id, captured) => (*lam_fn_id, captured.as_slice()),
                    _ => continue,
                };
                if !used_vars.contains(dest) {
                    continue;
                }
                let selected = select_callable_entry_target(
                    t,
                    spec_registry,
                    spec_plan,
                    |sid| {
                        reachable_specs.contains(&sid.0)
                            && body_index_by_spec_slot.get(sid.0 as usize).is_some_and(Option::is_some)
                    },
                    lam_fn_id,
                    captured,
                    block_env,
                );
                if selected
                    .as_ref()
                    .is_some_and(|selection| callable_entries.contains_key(&selection.spec_id))
                {
                    continue;
                }
                let lam_name = module
                    .fns
                    .iter()
                    .find(|f| f.id == lam_fn_id)
                    .map(|f| f.name.clone())
                    .unwrap_or_else(|| format!("FnId({})", lam_fn_id.0));
                let reason = selected
                    .map(|selection| format!("selected_spec={}", selection.spec_id))
                    .unwrap_or_else(|| "no_planned_target".to_string());
                gaps.push(format!(
                    "{} spec_id={} missing callable entry for {} (captures={}, {})",
                    planned_body.body.name,
                    planned_body.spec_id.0,
                    lam_name,
                    captured.len(),
                    reason
                ));
            }
        }
    }
    gaps
}

fn display_spec_ids(reachable_specs: &HashSet<u32>) -> Vec<String> {
    let mut ids: Vec<u32> = reachable_specs.iter().copied().collect();
    ids.sort_unstable();
    ids.into_iter().map(|sid| sid.to_string()).collect()
}

#[derive(Debug, Default)]
struct MaterializedReachability {
    specs: HashSet<u32>,
    missing_body_specs: Vec<String>,
}

fn materialized_reachable_specs<T>(
    t: &mut T,
    module: &Module,
    module_plan: &ModulePlan,
    spec_registry: &SpecRegistry,
    bodies: &[PlannedBody],
    body_index_by_spec_slot: &[Option<usize>],
) -> MaterializedReachability
where
    T: Types<Ty = Ty> + ClosureTypes,
{
    let mut reachable = HashSet::new();
    let mut work = VecDeque::new();
    let mut missing_body_specs = Vec::new();
    for (fn_id, input_tys) in entry_seeds(t, module) {
        let key = spec_key_for_fn_id(module, fn_id, input_tys);
        enqueue_materialized_spec(t, spec_registry, &mut reachable, &mut work, &key);
    }
    loop {
        while let Some(sid) = work.pop_front() {
            let Some(body_idx) = body_index_by_spec_slot.get(sid as usize).and_then(|idx| *idx) else {
                missing_body_specs.push(format!("spec_id={sid}"));
                continue;
            };
            let planned_body = &bodies[body_idx];
            for target in materialized_successor_targets(t, spec_registry, planned_body, body_index_by_spec_slot) {
                enqueue_materialized_spec(t, spec_registry, &mut reachable, &mut work, &target);
            }
        }
        if !enqueue_role_siblings_for_reachable_body_keys(t, module_plan, spec_registry, &mut reachable, &mut work) {
            break;
        }
    }

    MaterializedReachability {
        specs: reachable,
        missing_body_specs,
    }
}

fn enqueue_role_siblings_for_reachable_body_keys<T>(
    t: &mut T,
    module_plan: &ModulePlan,
    spec_registry: &SpecRegistry,
    reachable: &mut HashSet<u32>,
    work: &mut VecDeque<u32>,
) -> bool
where
    T: Types<Ty = Ty> + ClosureTypes,
{
    let reachable_body_keys: HashSet<_> = spec_registry
        .iter()
        .filter(|(sid, _)| reachable.contains(&sid.0))
        .map(|(_, key)| key.body_key())
        .collect();
    let mut changed = false;
    for key in &module_plan.reachable_specs {
        if !reachable_body_keys.contains(&key.body_key()) {
            continue;
        }
        let role = module_plan
            .spec_roles
            .get(&key.body_key())
            .copied()
            .unwrap_or(SpecReachabilityRole::ProjectionGap);
        if !matches!(
            role,
            SpecReachabilityRole::Activation | SpecReachabilityRole::CallableEntry
        ) {
            continue;
        }
        let before = reachable.len();
        enqueue_materialized_spec(t, spec_registry, reachable, work, key);
        changed |= reachable.len() != before;
    }
    changed
}

fn enqueue_materialized_spec<T>(
    t: &mut T,
    spec_registry: &SpecRegistry,
    reachable: &mut HashSet<u32>,
    work: &mut VecDeque<u32>,
    key: &SpecKey,
) where
    T: Types<Ty = Ty> + ClosureTypes,
{
    let sid = spec_registry
        .resolve_spec_key(t, key)
        .unwrap_or_else(|| panic!("materialized spec {:?} missing from spec registry", key));
    if reachable.insert(sid.0) {
        work.push_back(sid.0);
    }
}

fn materialized_successor_targets<T>(
    t: &mut T,
    spec_registry: &SpecRegistry,
    planned_body: &PlannedBody,
    body_index_by_spec_slot: &[Option<usize>],
) -> Vec<SpecKey>
where
    T: Types<Ty = Ty> + ClosureTypes,
{
    let spec_plan = &planned_body.spec_plan;
    let mut out = Vec::new();
    for edge in spec_plan.call_edges.values() {
        if let Some(target) = edge.local_target() {
            push_unique_spec_key(&mut out, target.clone());
        }
        if let Some(contract) = edge.return_contract.as_ref() {
            push_unique_spec_key(&mut out, contract.target.clone());
        }
    }

    let used_vars = collect_used(&planned_body.body);
    for block in &planned_body.body.blocks {
        if !spec_plan.reachable_blocks.contains(&block.id) {
            continue;
        }
        let block_env = spec_plan.block_envs.get(&block.id);
        for stmt in &block.stmts {
            let Stmt::Let(dest, prim) = stmt;
            let (fn_id, captured) = match prim {
                Prim::MakeFnRef(_, fn_id) => (*fn_id, &[][..]),
                Prim::MakeClosure(_, fn_id, captured) => (*fn_id, captured.as_slice()),
                _ => continue,
            };
            if !used_vars.contains(dest) {
                continue;
            }
            let Some(selection) = select_callable_entry_target(
                t,
                spec_registry,
                spec_plan,
                |sid| body_index_by_spec_slot.get(sid.0 as usize).is_some_and(Option::is_some),
                fn_id,
                captured,
                block_env,
            ) else {
                continue;
            };
            push_unique_spec_key(&mut out, selection.target_key);
        }
    }
    out
}

fn push_unique_spec_key(out: &mut Vec<SpecKey>, key: SpecKey) {
    if !out.contains(&key) {
        out.push(key);
    }
}

fn build_callable_entries<T>(
    t: &mut T,
    bodies: &[PlannedBody],
    spec_registry: &SpecRegistry,
    body_index_by_spec_slot: &[Option<usize>],
    reachable_specs: &HashSet<u32>,
) -> BTreeMap<u32, CallableEntryPlan>
where
    T: Types<Ty = Ty> + ClosureTypes,
{
    let mut callable_entries = BTreeMap::new();
    for planned_body in bodies {
        if !reachable_specs.contains(&planned_body.spec_id.0) {
            continue;
        }
        let spec_plan = &planned_body.spec_plan;
        let used_vars = collect_used(&planned_body.body);
        for blk in &planned_body.body.blocks {
            if !spec_plan.reachable_blocks.contains(&blk.id) {
                continue;
            }
            let block_env = spec_plan.block_envs.get(&blk.id);
            for stmt in blk.stmts.iter() {
                let Stmt::Let(dest, prim) = stmt;
                let (lam_fn_id, captured) = match prim {
                    Prim::MakeFnRef(_ident, lam_fn_id) => (*lam_fn_id, &[][..]),
                    Prim::MakeClosure(_ident, lam_fn_id, captured) => (*lam_fn_id, captured.as_slice()),
                    _ => continue,
                };
                if !used_vars.contains(dest) {
                    continue;
                }
                let Some(selection) = select_callable_entry_target(
                    t,
                    spec_registry,
                    spec_plan,
                    |sid| {
                        reachable_specs.contains(&sid.0)
                            && body_index_by_spec_slot.get(sid.0 as usize).is_some_and(Option::is_some)
                    },
                    lam_fn_id,
                    captured,
                    block_env,
                ) else {
                    continue;
                };
                callable_entries.insert(
                    selection.spec_id,
                    CallableEntryPlan {
                        capture_count: captured.len(),
                    },
                );
            }
        }
    }
    callable_entries
}

pub(crate) fn select_callable_entry_target<T>(
    t: &mut T,
    spec_registry: &SpecRegistry,
    spec_plan: &SpecPlan,
    mut has_callable_body: impl FnMut(SpecId) -> bool,
    fn_id: FnId,
    captured: &[crate::fz_ir::Var],
    block_env: Option<&HashMap<crate::fz_ir::Var, Ty>>,
) -> Option<PlannedCallableEntrySelection>
where
    T: Types<Ty = Ty> + ClosureTypes,
{
    let mut capture_tys = Vec::with_capacity(captured.len());
    for var in captured {
        let ty = block_env
            .and_then(|env| env.get(var))
            .or_else(|| spec_plan.vars.get(var))
            .cloned()
            .unwrap_or_else(|| t.any());
        let erased = t.erase_closure_identity(&ty);
        capture_tys.push(t.alpha_normalize_vars(&erased));
    }
    let capture_count = captured.len();
    let mut candidates: Vec<(SpecId, &SpecKey)> = Vec::new();
    let mut seen_candidates: HashSet<u32> = HashSet::new();
    for target in spec_plan
        .callable_entry_targets
        .iter()
        .filter(|target| target.fn_id == fn_id && target.input.len() >= capture_count)
    {
        let Some(sid) = spec_registry.resolve_spec_key(&*t, target) else {
            continue;
        };
        if has_callable_body(sid) && seen_candidates.insert(sid.0) {
            candidates.push((sid, target));
        }
    }
    let candidate_count = candidates.len();
    let selected_idx = best_covering_candidate(
        &*t,
        &capture_tys,
        candidates.iter().enumerate().map(|(idx, (sid, target))| {
            let capture_key = &target.input[..capture_count];
            BestCoverCandidate {
                id: idx,
                key: capture_key,
                key_var_count: key_slot_var_count(&*t, capture_key),
                precedence: sid.0,
            }
        }),
    )?;
    let (sid, target_key) = candidates[selected_idx];
    Some(PlannedCallableEntrySelection {
        spec_id: sid.0,
        target_key: target_key.clone(),
        candidate_count,
    })
}

fn build_spec_registry<T: Types<Ty = Ty>>(t: &mut T, module: &Module, module_plan: &ModulePlan) -> SpecRegistry {
    let mut spec_registry = SpecRegistry::new();
    let mut fns_by_fnid: Vec<&FnIr> = module.fns.iter().collect();
    fns_by_fnid.sort_by_key(|f| f.id.0);
    for f in &fns_by_fnid {
        let n_params = f.block(f.entry).params.len();
        let any_ty = t.any();
        let any_key = f.semantic_key(vec![any_ty; n_params]);
        let spec_key = SpecKey::value(f.id, any_key.clone());
        if !module_plan.specs.contains_key(&spec_key) {
            continue;
        }
        let precedence = *module_plan.spec_precedence.get(&spec_key.body_key()).unwrap_or(&0);
        let sid = spec_registry.register_any_key_at_with_precedence(t, f.id, any_key, precedence);
        debug_assert_eq!(sid.0, f.id.0);
    }

    let any_ty = t.any();
    let mut narrow_keys: Vec<SpecKey> = module_plan
        .specs
        .keys()
        .filter(|spec_key| {
            let Some(f) = module.fns.iter().find(|f| f.id == spec_key.fn_id) else {
                return true;
            };
            let n_params = f.block(f.entry).params.len();
            let any_key = f.semantic_key(vec![any_ty.clone(); n_params]);
            !(spec_key.demand.is_value() && spec_key.input == any_key)
        })
        .cloned()
        .collect();
    narrow_keys.sort_by(|a, b| {
        a.fn_id
            .0
            .cmp(&b.fn_id.0)
            .then_with(|| format!("{:?}", a.input).cmp(&format!("{:?}", b.input)))
            .then_with(|| format!("{:?}", a.demand).cmp(&format!("{:?}", b.demand)))
    });
    for spec_key in narrow_keys {
        let precedence = *module_plan.spec_precedence.get(&spec_key.body_key()).unwrap_or(&0);
        spec_registry.register_spec_key_with_precedence(t, spec_key, precedence);
    }
    spec_registry
}
