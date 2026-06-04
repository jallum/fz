use crate::frontend::spec_registry::{BestCoverCandidate, SpecRegistry, best_covering_candidate};
use crate::fz_ir::{FnId, FnIr, Module, Prim, SpecId, Stmt};
use crate::ir_dce::collect_used;
use crate::ir_fold::fold_planned_body;
use crate::ir_planner::fn_types::{ModulePlan, SpecKey, SpecPlan};
use crate::ir_planner::reachable::reachable_spec_ids;
use crate::telemetry::Telemetry;
use crate::types::{ClosureTypes, Ty, Types, key_slot_var_count};
use std::collections::{BTreeMap, HashMap, HashSet};

pub(crate) struct PlannedProgram<'plan> {
    spec_registry: SpecRegistry,
    spec_keys: Vec<SpecKey>,
    spec_fn_indices: Vec<Option<usize>>,
    spec_plans: Vec<Option<&'plan SpecPlan>>,
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
    pub body: FnIr,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct PlannedProgramStats {
    pub spec_slot_count: usize,
    pub planned_body_count: usize,
    pub sentinel_spec_count: usize,
    pub folded_prim_count: usize,
    pub folded_branch_count: usize,
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

impl<'plan> PlannedProgram<'plan> {
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

    pub(crate) fn spec_plans(&self) -> &[Option<&'plan SpecPlan>] {
        &self.spec_plans
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
pub(crate) fn materialize_program<'plan, T>(
    t: &mut T,
    module: &Module,
    module_plan: &'plan ModulePlan,
    tel: &dyn Telemetry,
) -> PlannedProgram<'plan>
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
                let fold_stats = fold_planned_body(t, &mut body, spec_plan);
                folded_prim_count += fold_stats.prim_count;
                folded_branch_count += fold_stats.branch_count;
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
                    },
                    &crate::metadata! {
                        role: "authoritative",
                        module_path: module.module_path().to_owned(),
                        fn_name: body.name.clone(),
                        spec_key: format!("{:?}", spec_keys[sid]),
                    },
                );
                bodies.push(PlannedBody {
                    spec_id: SpecId(sid as u32),
                    spec_key: spec_keys[sid].clone(),
                    body_key,
                    fn_id: body.id,
                    fn_idx,
                    body,
                });
                body_index_by_spec_slot.push(Some(body_index));
            }
            _ => body_index_by_spec_slot.push(None),
        }
    }
    let reachable_specs = reachable_spec_ids(t, &spec_registry, module_plan);
    let callable_entries = build_callable_entries(
        t,
        &bodies,
        &spec_registry,
        &spec_plans,
        &body_index_by_spec_slot,
        &reachable_specs,
    );
    let make_closure_callable_gaps = make_closure_callable_gap_issues(
        t,
        module,
        &bodies,
        &spec_registry,
        &spec_plans,
        &body_index_by_spec_slot,
        &callable_entries,
        &reachable_specs,
    );

    let planned_body_count = bodies.len();
    let stats = PlannedProgramStats {
        spec_slot_count: spec_registry.len(),
        planned_body_count,
        sentinel_spec_count: spec_registry.len() - planned_body_count,
        folded_prim_count,
        folded_branch_count,
    };
    tel.execute(
        &["fz", "planner", "materialized"],
        &crate::measurements! {
            spec_slot_count: stats.spec_slot_count as u64,
            planned_body_count: stats.planned_body_count as u64,
            sentinel_spec_count: stats.sentinel_spec_count as u64,
            folded_prim_count: stats.folded_prim_count as u64,
            folded_branch_count: stats.folded_branch_count as u64,
            reachable_spec_count: reachable_specs.len() as u64,
            post_plan_reachability_growth_count: 0,
            make_closure_callable_gap_count: make_closure_callable_gaps.len() as u64,
        },
        &crate::metadata! {
            role: "authoritative",
            module_path: module.module_path().to_owned(),
            reachable_specs: display_spec_ids(&reachable_specs),
            make_closure_callable_gaps: make_closure_callable_gaps.clone(),
        },
    );

    PlannedProgram {
        spec_registry,
        spec_keys,
        spec_fn_indices,
        spec_plans,
        bodies,
        body_index_by_spec_slot,
        callable_entries,
        reachable_specs,
    }
}

fn make_closure_callable_gap_issues<T>(
    t: &mut T,
    module: &Module,
    bodies: &[PlannedBody],
    spec_registry: &SpecRegistry,
    spec_plans: &[Option<&SpecPlan>],
    body_index_by_spec_slot: &[Option<usize>],
    callable_entries: &BTreeMap<u32, CallableEntryPlan>,
    reachable_specs: &HashSet<u32>,
) -> Vec<String>
where
    T: Types<Ty = Ty>,
{
    let mut gaps = Vec::new();
    for planned_body in bodies {
        if !reachable_specs.contains(&planned_body.spec_id.0) {
            continue;
        }
        let Some(spec_plan) = spec_plans.get(planned_body.spec_id.0 as usize).and_then(|plan| *plan) else {
            continue;
        };
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

fn build_callable_entries<T>(
    t: &mut T,
    bodies: &[PlannedBody],
    spec_registry: &SpecRegistry,
    spec_plans: &[Option<&SpecPlan>],
    body_index_by_spec_slot: &[Option<usize>],
    reachable_specs: &HashSet<u32>,
) -> BTreeMap<u32, CallableEntryPlan>
where
    T: Types<Ty = Ty>,
{
    let mut callable_entries = BTreeMap::new();
    for planned_body in bodies {
        if !reachable_specs.contains(&planned_body.spec_id.0) {
            continue;
        }
        let Some(spec_plan) = spec_plans.get(planned_body.spec_id.0 as usize).and_then(|plan| *plan) else {
            continue;
        };
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
    T: Types<Ty = Ty>,
{
    let capture_tys = captured
        .iter()
        .map(|var| {
            block_env
                .and_then(|env| env.get(var))
                .or_else(|| spec_plan.vars.get(var))
                .cloned()
                .unwrap_or_else(|| t.any())
        })
        .collect::<Vec<_>>();
    let capture_count = captured.len();
    let mut candidates: Vec<(SpecId, &SpecKey)> = Vec::new();
    for target in spec_plan
        .callable_entry_targets
        .iter()
        .filter(|target| target.fn_id == fn_id && target.input.len() >= capture_count)
    {
        let Some(sid) = spec_registry.resolve_spec_key(&*t, target) else {
            continue;
        };
        if has_callable_body(sid) {
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
