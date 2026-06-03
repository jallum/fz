use crate::frontend::spec_registry::SpecRegistry;
use crate::fz_ir::{FnId, FnIr, Module, Prim, SpecId, Stmt};
use crate::ir_dce::collect_used;
use crate::ir_fold::fold_planned_body;
use crate::ir_planner::fn_types::{BodyKey, ModulePlan, SpecKey, SpecPlan};
use crate::ir_planner::reachable::reachable_spec_ids;
use crate::telemetry::Telemetry;
use crate::types::{ClosureTypes, Ty, Types};
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
    let mut body_index_by_key: HashMap<BodyKey, usize> = HashMap::new();
    let mut body_index_by_spec_slot = Vec::with_capacity(spec_registry.len());
    for sid in 0..spec_registry.len() {
        match (spec_fn_indices[sid], spec_plans[sid]) {
            (Some(fn_idx), Some(spec_plan)) => {
                let body_key = spec_keys[sid].body_key();
                if let Some(&body_index) = body_index_by_key.get(&body_key) {
                    let canonical = &bodies[body_index];
                    let canonical_plan = module_plan
                        .specs
                        .get(&canonical.spec_key)
                        .expect("canonical planned body must keep its spec plan");
                    assert_same_body_plan(&canonical.spec_key, canonical_plan, &spec_keys[sid], spec_plan);
                    body_index_by_spec_slot.push(Some(body_index));
                    continue;
                }
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
                    body_key: body_key.clone(),
                    fn_id: body.id,
                    fn_idx,
                    body,
                });
                body_index_by_key.insert(body_key, body_index);
                body_index_by_spec_slot.push(Some(body_index));
            }
            _ => body_index_by_spec_slot.push(None),
        }
    }
    let reachable_specs = reachable_spec_ids(t, &spec_registry, module_plan);
    let callable_entries = build_callable_entries(&bodies, &spec_registry, &body_index_by_spec_slot, &reachable_specs);
    let make_closure_callable_gaps =
        make_closure_callable_gap_issues(module, &bodies, &spec_registry, &callable_entries, &reachable_specs);

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

fn make_closure_callable_gap_issues(
    module: &Module,
    bodies: &[PlannedBody],
    spec_registry: &SpecRegistry,
    callable_entries: &BTreeMap<u32, CallableEntryPlan>,
    reachable_specs: &HashSet<u32>,
) -> Vec<String> {
    let mut gaps = Vec::new();
    for planned_body in bodies {
        if !reachable_specs.contains(&planned_body.spec_id.0) {
            continue;
        }
        let used_vars = collect_used(&planned_body.body);
        for blk in &planned_body.body.blocks {
            for stmt in &blk.stmts {
                let Stmt::Let(dest, prim) = stmt;
                let Prim::MakeClosure(_, lam_fn_id, captured) = prim else {
                    continue;
                };
                if !used_vars.contains(dest) {
                    continue;
                }
                let resolved =
                    spec_registry.resolve_closure_body_spec(*lam_fn_id, |sid| callable_entries.contains_key(&sid.0));
                if resolved.is_some() {
                    continue;
                }
                let lam_name = module
                    .fns
                    .iter()
                    .find(|f| f.id == *lam_fn_id)
                    .map(|f| f.name.clone())
                    .unwrap_or_else(|| format!("FnId({})", lam_fn_id.0));
                gaps.push(format!(
                    "{} spec_id={} missing callable entry for {} (captures={})",
                    planned_body.body.name,
                    planned_body.spec_id.0,
                    lam_name,
                    captured.len()
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

fn assert_same_body_plan(canonical_key: &SpecKey, canonical: &SpecPlan, sibling_key: &SpecKey, sibling: &SpecPlan) {
    assert_eq!(
        canonical.vars, sibling.vars,
        "body-local var facts diverged for shared body {:?} vs {:?}",
        canonical_key, sibling_key
    );
    assert_eq!(
        canonical.block_envs, sibling.block_envs,
        "body-local block envs diverged for shared body {:?} vs {:?}",
        canonical_key, sibling_key
    );
    assert_eq!(
        canonical.callable_capabilities, sibling.callable_capabilities,
        "body-local callable capabilities diverged for shared body {:?} vs {:?}",
        canonical_key, sibling_key
    );
    assert_eq!(
        canonical.reachable_blocks, sibling.reachable_blocks,
        "reachable blocks diverged for shared body {:?} vs {:?}",
        canonical_key, sibling_key
    );
    assert_eq!(
        canonical.dead_branches, sibling.dead_branches,
        "dead branches diverged for shared body {:?} vs {:?}",
        canonical_key, sibling_key
    );
    assert_eq!(
        canonical.brand_inners, sibling.brand_inners,
        "brand inners diverged for shared body {:?} vs {:?}",
        canonical_key, sibling_key
    );
    assert_eq!(
        canonical.opaque_inners, sibling.opaque_inners,
        "opaque inners diverged for shared body {:?} vs {:?}",
        canonical_key, sibling_key
    );
}

fn build_callable_entries(
    bodies: &[PlannedBody],
    spec_registry: &SpecRegistry,
    body_index_by_spec_slot: &[Option<usize>],
    reachable_specs: &HashSet<u32>,
) -> BTreeMap<u32, CallableEntryPlan> {
    let mut callable_entries = BTreeMap::new();
    let has_body = |sid: SpecId| body_index_by_spec_slot.get(sid.0 as usize).is_some_and(Option::is_some);
    for planned_body in bodies {
        if !reachable_specs.contains(&planned_body.spec_id.0) {
            continue;
        }
        let used_vars = collect_used(&planned_body.body);
        for blk in &planned_body.body.blocks {
            for stmt in blk.stmts.iter() {
                let Stmt::Let(dest, prim) = stmt;
                if let Prim::MakeClosure(_ident, lam_fn_id, captured) = prim {
                    if !used_vars.contains(dest) {
                        continue;
                    }
                    let cl_sid = spec_registry
                        .resolve_closure_body_spec(*lam_fn_id, has_body)
                        .map(|sid| sid.0);
                    let Some(cl_sid) = cl_sid else {
                        continue;
                    };
                    callable_entries.insert(
                        cl_sid,
                        CallableEntryPlan {
                            capture_count: captured.len(),
                        },
                    );
                }
            }
        }
    }
    callable_entries
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
        let precedence = *module_plan.spec_precedence.get(&spec_key).unwrap_or(&0);
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
        let precedence = *module_plan.spec_precedence.get(&spec_key).unwrap_or(&0);
        spec_registry.register_spec_key_with_precedence(t, spec_key, precedence);
    }
    spec_registry
}
