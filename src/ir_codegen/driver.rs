#![allow(unused_imports)]

#[cfg(debug_assertions)]
use super::invariants::{assert_no_new_call_shapes, emit_and_assert_spec_dispatch_coverage, snapshot_call_shapes};
use super::receive::{MatcherRuntimeHelpers, declare_matcher, emit_matcher_body_from_matcher};
use super::*;
use crate::concrete_types::ty_descr;
use crate::fz_ir::{BinOp, BlockId, CallsiteId, Const, EmitSlot, FnId, Module, Prim, SpecId, Stmt, Term, UnOp};
use crate::ir_const_bs::fold_module;
use crate::ir_dce::{dce_module_level, dce_module_with_telemetry};
use crate::ir_dest::{lower_destinations, verify_module};
use crate::ir_diverge::truncate_diverging_blocks;
use crate::ir_extern_marshal::resolve_module_types;
use crate::ir_fuse::fuse_blocks_with_telemetry;
use crate::ir_inline::{inline_module_with_plan, inline_single_use_conts};
use crate::ir_planner::fn_types::SpecKey;
use crate::ir_planner::planned::CallableEntryPlan;
use crate::ir_planner::{
    ModulePlan, SpecPlan, collect_diagnostics, materialize_program, plan_callable_capabilities, plan_module,
    rewrite_known_target_closures,
};
use crate::ir_reducer::reduce_module_with_telemetry;
use crate::telemetry::value::opaque;
use crate::telemetry::{Telemetry, TelemetryExt as _, next_compile_nonce};
#[cfg(test)]
use crate::test_support::assert_module_planner_consistent;
use crate::types::{
    ClosureTarget, ClosureTypes, LiteralTypes, RenderTypes, Ty, Types, VisibilityTypes, key_slots_from_tys,
    key_slots_to_tys,
};
use cranelift_codegen::Context;
use cranelift_codegen::ir::{
    self, AbiParam, BlockArg, InstBuilder, MemFlags, Signature,
    condcodes::{FloatCC, IntCC},
    types,
};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module as ClModule};
use fz_runtime::heap::{FieldDescriptor, FieldKind, Schema, SchemaRegistry};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

/// Walk every fn body collecting tuple arities used by MakeTuple /
/// DestTupleBegin / TypeTest descrs, detecting any bitstring prim, then
/// registering a deterministic-id Schema per arity in `user_schemas`.
///
/// Returns `(tuple_arities, tuple_schema_ids, bs_tuple_arity1_schema,
/// bs_tuple_arity3_schema)`. Arity-1 / arity-3 schemas used by the
/// bitstring reader / result tuples are pre-registered when any bs prim
/// is present even if no MakeTuple uses those arities directly. BTreeSet
/// iteration keeps assignment order deterministic so the AOT runtime's
/// ids match what codegen baked in.
fn collect_tuple_arities_and_register_schemas(
    module: &Module,
    user_schemas: &RefCell<SchemaRegistry>,
) -> (BTreeSet<usize>, HashMap<usize, u32>, Option<u32>, Option<u32>) {
    let mut tuple_arities: BTreeSet<usize> = BTreeSet::new();
    let mut has_bs_prim = false;
    for f in &module.fns {
        for blk in &f.blocks {
            for stmt in &blk.stmts {
                let Stmt::Let(_, prim) = stmt;
                match prim {
                    Prim::MakeTuple(args) => {
                        tuple_arities.insert(args.len());
                    }
                    Prim::DestTupleBegin { arity, .. } => {
                        tuple_arities.insert(*arity);
                    }
                    Prim::MakeBitstring(_)
                    | Prim::BitReaderInit(_)
                    | Prim::BitReadField { .. }
                    | Prim::BitReaderDone(_) => {
                        has_bs_prim = true;
                    }
                    Prim::TypeTest(_, descr) => {
                        for arity in ty_descr(descr).type_test_tuple_arities() {
                            tuple_arities.insert(arity);
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    if has_bs_prim {
        tuple_arities.insert(1);
        tuple_arities.insert(3);
    }
    let mut tuple_schema_ids: HashMap<usize, u32> = HashMap::new();
    {
        let mut reg = user_schemas.borrow_mut();
        for &arity in &tuple_arities {
            let id = reg.register(Schema::tuple_of_arity(arity));
            tuple_schema_ids.insert(arity, id);
        }
    }
    let (bs_tuple_arity1_schema, bs_tuple_arity3_schema) = if has_bs_prim {
        (
            Some(*tuple_schema_ids.get(&1).expect("arity-1 schema registered")),
            Some(*tuple_schema_ids.get(&3).expect("arity-3 schema registered")),
        )
    } else {
        (None, None)
    };
    (
        tuple_arities,
        tuple_schema_ids,
        bs_tuple_arity1_schema,
        bs_tuple_arity3_schema,
    )
}

/// Build per-SpecId frame schemas, refining entry-param kinds from each
/// spec's SpecPlan. The any-key SpecId for FnId K lands at index K
/// (invariant) so any code path that uses fn_id.0 as a schema_id
/// continues to hit the right schema. Sentinel SpecIds (missing-FnId
/// slots) get a zero-field placeholder schema; they're never reached at
/// runtime.
fn build_per_spec_schemas<T: Types<Ty = Ty>>(
    t: &mut T,
    module: &Module,
    spec_count: usize,
    spec_fnidx: &[Option<usize>],
    spec_fn_types: &[Option<&SpecPlan>],
) -> Vec<Schema> {
    let mut schemas: Vec<Schema> = Vec::with_capacity(spec_count);
    for sid in 0..spec_count {
        let Some(idx) = spec_fnidx[sid] else {
            schemas.push(build_frame_schema("__sentinel", &[]));
            continue;
        };
        let f = &module.fns[idx];
        let ft = spec_fn_types[sid].expect("non-sentinel spec must have SpecPlan");
        let entry_block = f.block(f.entry);
        let mut kinds: Vec<FieldKind> = entry_block.params.iter().map(|_| FieldKind::AnyValue).collect();
        let any = t.any();
        for (j, p) in entry_block.params.iter().enumerate() {
            match ArgRepr::from_ty(t, &ft.vars.get(p).cloned().unwrap_or_else(|| any.clone())) {
                ArgRepr::RawF64 => kinds[j] = FieldKind::RawF64,
                ArgRepr::RawInt => kinds[j] = FieldKind::RawI64,
                _ => {}
            }
        }
        schemas.push(build_frame_schema(&f.name, &kinds));
    }
    schemas
}

/// Per-spec return ABI type comes from the planner's finished
/// `module_plan.effective_returns`. Planner projection is total for
/// executable specs, including callable-entry declared contracts. Codegen does
/// not instantiate declared specs as a fallback.
///
/// Halt-only specs project to `none()`; substitute `any` so
/// `ArgRepr::from_descr` doesn't pick RawF64 (none is a subtype of every set,
/// including float). The value never reaches anyone for a halt-only spec, but
/// the ABI must still be valid.
fn derive_return_tys<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    spec_keys: &[SpecKey],
    spec_fnidx: &[Option<usize>],
    module_plan: &ModulePlan,
) -> Vec<Ty> {
    let any = t.any();
    let none = t.none();
    spec_keys
        .iter()
        .enumerate()
        .map(|(sid, key)| {
            if spec_fnidx[sid].is_none() {
                return any.clone();
            }
            let ret = module_plan
                .effective_returns
                .get(&key.body_key())
                .cloned()
                .unwrap_or_else(|| panic!("planned spec {:?} missing effective return", key));
            if t.is_subtype(&ret, &none) { any.clone() } else { ret }
        })
        .collect()
}

/// Per-spec entry-param ArgReprs. Drives `build_fn_signature`
/// (AbiParam types) and call-site coerce (raw int / raw f64 vs one-word
/// ValueRef). Sentinel slots get empty params; they're never declared.
///
/// CAPTURE slots [0..n_caps) keep their per-spec narrow reprs. Ordinary
/// direct-entry arg slots honor the selected `SpecKey`'s typed input.
///
/// Callable entries are different: closures store a public callable-entry
/// code pointer, and that ABI is always the generic ValueRef seam. So for
/// closure-target bodies we force ARG slots [n_caps..] to ValueRef here and
/// let the separately-emitted callable-entry wrapper decode into the direct
/// typed body entry when needed. That keeps one semantic body while making
/// the executable contract explicit: direct typed calls stay narrow, indirect
/// closure calls never guess.
fn derive_param_reprs<T: Types<Ty = Ty>>(
    t: &mut T,
    module: &Module,
    spec_count: usize,
    spec_fnidx: &[Option<usize>],
    spec_fn_types: &[Option<&SpecPlan>],
    spec_keys: &[SpecKey],
    cont_fns: &HashSet<FnId>,
) -> Vec<Vec<ArgRepr>> {
    (0..spec_count)
        .map(|sid| match spec_fnidx[sid] {
            Some(idx) => {
                let f = &module.fns[idx];
                let ft = spec_fn_types[sid].expect("non-sentinel spec must have SpecPlan");
                if spec_keys[sid].input.iter().all(Option::is_none) {
                    build_param_reprs(t, f, ft)
                } else {
                    build_param_reprs_for_spec(t, f, ft, &spec_keys[sid], cont_fns.contains(&f.id))
                }
            }
            None => Vec::new(),
        })
        .collect()
}

/// Per-spec tagged-return tracking: transitive closure of specs
/// whose return is ValueRef-by-construction. Drives BOTH the
/// return_reprs force AND the tagged_slot0_cont_specs check so
/// producer-side ABI and consumer-side schema stay aligned. One spec of
/// a fn can have a fully-resolved TailCallClosure (returning the body's
/// narrow repr) while a sibling spec's TailCallClosure stays opaque
/// (returning ValueRef through the indirect seam) — per-spec is the
/// precise grain.
///
/// Seed: spec has an UNRESOLVED TailCallClosure (returns through the
/// all-ValueRef indirect ABI), or spec's body is a closure-target body.
/// Closure-target ABI is structurally uniform ValueRef.
///
/// Propagation: spec's terminator chains into another spec that's
/// already tagged. Per-spec analysis uses each block's terminator under
/// this spec's env (spec_fn_types[sid]).
fn compute_tagged_return_specs<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    module: &Module,
    spec_fnidx: &[Option<usize>],
    spec_fn_types: &[Option<&SpecPlan>],
    spec_registry: &SpecRegistry,
    closure_capture_counts: &HashMap<FnId, usize>,
) -> HashSet<u32> {
    let mut set: HashSet<u32> = HashSet::new();
    let any_ty = t.any();
    // Seed: spec has an unresolved TailCallClosure.
    for (sid, &entry) in spec_fnidx.iter().enumerate() {
        let Some(idx) = entry else {
            continue;
        };
        let f = &module.fns[idx];
        for b in &f.blocks {
            if let Term::TailCallClosure {
                closure,
                args,
                ident: _,
            } = &b.terminator
                && spec_fn_types
                    .get(sid)
                    .and_then(|o| *o)
                    .and_then(|ft| resolve_tcc_body(t, closure, args, ft, module, spec_registry).map(|(_, s)| s))
                    .is_none()
            {
                set.insert(sid as u32);
                break;
            }
        }
    }
    // Also seed: spec's body is a closure-target body.
    for (sid, &entry) in spec_fnidx.iter().enumerate() {
        let Some(idx) = entry else {
            continue;
        };
        let fid = module.fns[idx].id;
        if closure_capture_counts.contains_key(&fid) {
            set.insert(sid as u32);
        }
    }
    // Propagation.
    loop {
        let mut changed = false;
        for (sid, &entry) in spec_fnidx.iter().enumerate() {
            if set.contains(&(sid as u32)) {
                continue;
            }
            let Some(idx) = entry else {
                continue;
            };
            let f = &module.fns[idx];
            let propagates = f.blocks.iter().any(|b| match &b.terminator {
                Term::TailCall { callee, args, .. } => {
                    let csid = (|| {
                        let ft = spec_fn_types.get(sid).and_then(|o| *o)?;
                        let arg_tys: Vec<Ty> = args
                            .iter()
                            .map(|av| ft.vars.get(av).cloned().unwrap_or_else(|| any_ty.clone()))
                            .collect();
                        let key = SpecKey::value(*callee, key_slots_from_tys(arg_tys));
                        spec_registry.resolve_spec_key(t, &key).map(|s| s.0)
                    })()
                    .unwrap_or(callee.0);
                    set.contains(&csid)
                }
                Term::TailCallClosure {
                    closure,
                    args,
                    ident: _,
                } => {
                    let body_sid = spec_fn_types
                        .get(sid)
                        .and_then(|o| *o)
                        .and_then(|ft| resolve_tcc_body(t, closure, args, ft, module, spec_registry).map(|(_, s)| s));
                    match body_sid {
                        Some(body_sid) => set.contains(&body_sid),
                        None => true,
                    }
                }
                Term::Call { continuation, .. }
                | Term::CallClosure { continuation, .. }
                | Term::Receive { continuation, ident: _ } => set.contains(&continuation.fn_id.0),
                _ => false,
            });
            if propagates {
                set.insert(sid as u32);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    set
}

/// Cont specs whose producer delivers a `ValueRef` lane must accept
/// `ValueRef` at slot 0. Producers that deliver tuple fields do not use
/// that slot-0 seam at all.
///
/// Reads the producer→cont call-edge facts from `SpecPlan.call_edges`
/// rather than recovering them from payload typing. The direct edge selects
/// both the producer spec (for representation) and the return shape.
fn compute_tagged_slot0_cont_specs<T: Types<Ty = Ty>>(
    t: &mut T,
    module: &Module,
    spec_count: usize,
    spec_fnidx: &[Option<usize>],
    spec_fn_types: &[Option<&SpecPlan>],
    spec_registry: &SpecRegistry,
    return_reprs: &[ArgRepr],
) -> HashSet<u32> {
    let mut tagged_slot0_cont_specs: HashSet<u32> = HashSet::new();
    for sid_caller in 0..spec_count {
        let Some(caller_idx) = spec_fnidx[sid_caller] else {
            continue;
        };
        let caller = &module.fns[caller_idx];
        let Some(caller_ft) = spec_fn_types[sid_caller] else {
            continue;
        };
        for blk in &caller.blocks {
            let Some(term_ident) = blk.terminator.ident() else {
                continue;
            };
            let produces_tagged_slot0 = match &blk.terminator {
                Term::Call { .. } => {
                    let cid = CallsiteId {
                        caller: caller.id,
                        ident: term_ident.clone(),
                        slot: EmitSlot::Direct,
                    };
                    caller_ft.local_call_target(&cid).is_some_and(|key| {
                        if !DemandAbi::new(key).delivers_value_lane() {
                            return false;
                        }
                        spec_registry
                            .resolve_spec_key(t, key)
                            .is_some_and(|sid| return_reprs[sid.0 as usize] == ArgRepr::ValueRef)
                    })
                }
                Term::CallClosure { .. } | Term::Receive { .. } => true,
                _ => false,
            };
            if !produces_tagged_slot0 {
                continue;
            }
            let cid = CallsiteId {
                caller: caller.id,
                ident: term_ident.clone(),
                slot: EmitSlot::Cont,
            };
            if let Some(cont_key) = caller_ft.local_call_target(&cid)
                && let Some(sid) = spec_registry.resolve_spec_key(t, cont_key)
            {
                tagged_slot0_cont_specs.insert(sid.0);
            }
        }
    }
    tagged_slot0_cont_specs
}

/// Per-spec chain analysis: for each registered spec, walk its exit
/// terminators and follow callee resolutions transitively. The chain's
/// halt-seam kind = JOIN of every Return contributing along reachable
/// paths.
///
/// Closure_lit-driven chain resolution: when this spec's env types the
/// closure as `closure_lit(F, K)`, the resolved body's chain feeds ours,
/// so halt_kind selection (fz_entry_thunk, halt-cont singletons) picks
/// the right kind. Indirect closure dispatch uses the all-ValueRef seam
/// ABI, so anything returning through it is ValueRef.
fn compute_halt_reprs<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    module: &Module,
    spec_count: usize,
    spec_fnidx: &[Option<usize>],
    spec_fn_types: &[Option<&SpecPlan>],
    spec_registry: &SpecRegistry,
    return_reprs: &[ArgRepr],
) -> Vec<ArgRepr> {
    let join = |a: ArgRepr, b: ArgRepr| -> ArgRepr { if a == b { a } else { ArgRepr::ValueRef } };
    let mut chain: Vec<Option<ArgRepr>> = vec![None; spec_count];
    let any_ty = t.any();
    for _ in 0..(spec_count * 4 + 16) {
        let mut changed = false;
        for sid in 0..spec_count {
            let Some(idx) = spec_fnidx[sid] else {
                continue;
            };
            let f = &module.fns[idx];
            let mut contributions: Vec<ArgRepr> = Vec::new();
            for blk in &f.blocks {
                match &blk.terminator {
                    Term::Return(_) => {
                        contributions.push(return_reprs[sid]);
                    }
                    Term::TailCall { callee, args, .. } => {
                        let csid = (|| {
                            let ft = spec_fn_types.get(sid).and_then(|o| *o)?;
                            let arg_tys: Vec<Ty> = args
                                .iter()
                                .map(|av| ft.vars.get(av).cloned().unwrap_or_else(|| any_ty.clone()))
                                .collect();
                            let key = SpecKey::value(*callee, key_slots_from_tys(arg_tys));
                            spec_registry.resolve_spec_key(t, &key).map(|s| s.0)
                        })()
                        .unwrap_or(callee.0);
                        if let Some(c) = chain.get(csid as usize).and_then(|o| *o) {
                            contributions.push(c);
                        }
                    }
                    Term::Call { continuation, .. }
                    | Term::CallClosure { continuation, .. }
                    | Term::Receive { continuation, ident: _ } => {
                        let cont_sid = continuation.fn_id.0;
                        if let Some(c) = chain.get(cont_sid as usize).and_then(|o| *o) {
                            contributions.push(c);
                        }
                    }
                    Term::TailCallClosure {
                        closure,
                        args,
                        ident: _,
                    } => {
                        let resolved_body = spec_fn_types.get(sid).and_then(|o| *o).and_then(|ft| {
                            resolve_tcc_body(t, closure, args, ft, module, spec_registry).map(|(_, s)| s)
                        });
                        match resolved_body {
                            Some(body_sid) => {
                                if let Some(c) = chain.get(body_sid as usize).and_then(|o| *o) {
                                    contributions.push(c);
                                }
                            }
                            None => {
                                contributions.push(ArgRepr::ValueRef);
                            }
                        }
                    }
                    _ => {}
                }
            }
            if contributions.is_empty() {
                continue;
            }
            let joined = contributions.into_iter().reduce(join).unwrap();
            if chain[sid] != Some(joined) {
                chain[sid] = Some(joined);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    chain.into_iter().map(|o| o.unwrap_or(ArgRepr::ValueRef)).collect()
}

/// Per-fn halt-kind: looked up via the fn's any-key spec sid for the
/// entry-time halt chain.
fn derive_fn_halt_kinds(module: &Module, halt_reprs: &[ArgRepr]) -> HashMap<u32, u32> {
    let mut m: HashMap<u32, u32> = HashMap::new();
    for f in &module.fns {
        let sid = f.id.0 as usize;
        if let Some(r) = halt_reprs.get(sid).copied() {
            m.insert(f.id.0, r.halt_kind());
        }
    }
    m
}

/// Per-spec Cranelift Signature. Native fns get typed-arity i64s +
/// host_ctx; uniform fns get (i64, i64) -> i64. Sentinel slots get the
/// uniform sig — they're never declared.
///
/// Closure-target fn shape is gated on native (uniform closure targets
/// still go through the existing stub adapter).
#[allow(clippy::too_many_arguments)]
fn build_fn_sigs(
    module: &Module,
    spec_count: usize,
    spec_fnidx: &[Option<usize>],
    spec_keys: &[SpecKey],
    param_reprs: &[Vec<ArgRepr>],
    native_abi_fns: &HashSet<FnId>,
    cont_fns: &HashSet<FnId>,
    closure_capture_counts: &HashMap<FnId, usize>,
    cont_extras_count: &HashMap<FnId, usize>,
) -> Vec<Signature> {
    (0..spec_count)
        .map(|sid| match spec_fnidx[sid] {
            Some(idx) => {
                let f = &module.fns[idx];
                let is_native = native_abi_fns.contains(&f.id);
                let demand_abi = DemandAbi::new(&spec_keys[sid]);
                build_fn_signature(
                    &param_reprs[sid],
                    is_native,
                    cont_fns.contains(&f.id),
                    if is_native {
                        closure_capture_counts.get(&f.id).copied()
                    } else {
                        None
                    },
                    demand_abi
                        .tuple_field_arity()
                        .or_else(|| cont_extras_count.get(&f.id).copied()),
                )
            }
            None => {
                let mut sig = Signature::new(CallConv::Tail);
                sig.params.push(AbiParam::new(types::I64));
                sig.params.push(AbiParam::new(types::I64));
                sig.returns.push(AbiParam::new(types::I64));
                sig
            }
        })
        .collect()
}

/// Collect zero-capture closure-target specs for static singletons.
/// code_ptr is the body's func_addr directly (closure-target sig
/// `(args, self, cont) tail`), not a SystemV stub. The singleton acts
/// both as `self` for direct callers (zero-cap bodies ignore self) and
/// as the closure handed to MakeClosure(fid, []) sites. See
/// docs/cps-in-clif.md §8.2.
///
/// Pack halt_kind so fz_entry_thunk can pick the matching halt-cont
/// singleton at task launch.
fn collect_static_closure_targets(
    callable_entries: &BTreeMap<u32, CallableEntryPlan>,
    spec_keys: &[SpecKey],
    callable_entry_fn_ids: &HashMap<u32, FuncId>,
    return_reprs: &[ArgRepr],
) -> Vec<(u32, u32, FuncId, u32)> {
    callable_entries
        .iter()
        .filter(|(_, entry)| entry.capture_count == 0)
        .map(|(cl_sid, _)| {
            let fn_id = spec_keys[*cl_sid as usize].fn_id;
            let body_fid = *callable_entry_fn_ids
                .get(cl_sid)
                .expect("zero-cap closure spec must have a callable-entry FuncId");
            let halt_kind = return_reprs[*cl_sid as usize].halt_kind();
            (*cl_sid, fn_id.0, body_fid, halt_kind)
        })
        .collect()
}

fn build_callable_entry_signature(arg_count: usize) -> Signature {
    let mut sig = Signature::new(CallConv::Tail);
    for _ in 0..arg_count {
        sig.params.push(AbiParam::new(types::I64));
    }
    sig.params.push(AbiParam::new(types::I64)); // self
    sig.params.push(AbiParam::new(types::I64)); // cont
    sig.returns.push(AbiParam::new(types::I64));
    sig
}

fn declare_callable_entry_fns<M: cranelift_module::Module>(
    m: &mut M,
    callable_entries: &BTreeMap<u32, CallableEntryPlan>,
    param_reprs: &[Vec<ArgRepr>],
    spec_keys: &[SpecKey],
) -> Result<HashMap<u32, FuncId>, CodegenError> {
    let mut callable_entry_fn_ids = HashMap::new();
    for (&body_sid, entry) in callable_entries {
        let arg_count = param_reprs[body_sid as usize].len().saturating_sub(entry.capture_count);
        let sig = build_callable_entry_signature(arg_count);
        let name = format!(
            "fz_callable_entry_{}_s{}",
            spec_keys[body_sid as usize].fn_id.0, body_sid
        );
        let func_id = m
            .declare_function(&name, Linkage::Local, &sig)
            .map_err(|e| CodegenError::new(format!("declare {name}: {e}")))?;
        callable_entry_fn_ids.insert(body_sid, func_id);
    }
    Ok(callable_entry_fn_ids)
}

fn emit_callable_entry_bodies<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    runtime: &RuntimeRefs,
    fn_ids: &HashMap<u32, FuncId>,
    callable_entry_fn_ids: &HashMap<u32, FuncId>,
    callable_entries: &BTreeMap<u32, CallableEntryPlan>,
    param_reprs: &[Vec<ArgRepr>],
    spec_keys: &[SpecKey],
    tel: &dyn Telemetry,
    module_path: &str,
) -> Result<(), CodegenError> {
    for (&body_sid, entry) in callable_entries {
        let body_func_id = *fn_ids
            .get(&body_sid)
            .ok_or_else(|| CodegenError::new(format!("missing direct body FuncId for spec {body_sid}")))?;
        let callable_entry_id = *callable_entry_fn_ids
            .get(&body_sid)
            .ok_or_else(|| CodegenError::new(format!("missing callable-entry FuncId for spec {body_sid}")))?;
        let reprs = &param_reprs[body_sid as usize];
        let arg_reprs = &reprs[entry.capture_count..];
        let spec_key = &spec_keys[body_sid as usize];
        let sig = build_callable_entry_signature(arg_reprs.len());
        let entry_name = format!("callable_entry_s{body_sid}");
        tel.execute(
            &["fz", "codegen", "callable_entry_lowered"],
            &crate::measurements! {
                spec_id: body_sid as u64,
                arg_count: arg_reprs.len() as u64,
                capture_count: entry.capture_count as u64,
            },
            &crate::metadata! {
                module_path: module_path.to_owned(),
                fn_name: entry_name.clone(),
                body_spec_key: format!("{spec_key:?}"),
            },
        );
        emit_fn_body(m, fbctx, sig, callable_entry_id, |m, b| {
            let entry_block = b.create_block();
            b.append_block_params_for_function_params(entry_block);
            b.switch_to_block(entry_block);
            b.seal_block(entry_block);
            let params = b.block_params(entry_block).to_vec();
            let self_value = params[arg_reprs.len()];
            let cont_value = params[arg_reprs.len() + 1];
            let mut shim_cache = CodegenCache::default();
            let mut cg = CodegenFn::for_runtime_shim(runtime, b, m, &mut shim_cache);
            let body_fref = cg.func_ref(body_func_id);
            let mut direct_args: Vec<ir::Value> = Vec::with_capacity(arg_reprs.len() + 2);
            for (idx, repr) in arg_reprs.iter().copied().enumerate() {
                let binding = CodegenValue::AnyRef(params[idx]);
                cg.push_binding_as_abi_arg(&mut direct_args, binding, repr);
            }
            direct_args.push(self_value);
            direct_args.push(cont_value);
            cg.b.ins().return_call(body_fref, &direct_args);
        })
        .map_err(|e| CodegenError::new(format!("define {entry_name}: {e}")))?;
    }
    Ok(())
}

/// Force slot 0 of every cont spec in `tagged_slot0_cont_specs` to
/// ValueRef so the producer's ValueRef return matches the cont's wire
/// sig at the seam.
fn refine_param_reprs_for_tagging(
    param_reprs: Vec<Vec<ArgRepr>>,
    tagged_slot0_cont_specs: &HashSet<u32>,
) -> Vec<Vec<ArgRepr>> {
    param_reprs
        .into_iter()
        .enumerate()
        .map(|(sid, mut reprs)| {
            if !reprs.is_empty() && tagged_slot0_cont_specs.contains(&(sid as u32)) {
                reprs[0] = ArgRepr::ValueRef;
            }
            reprs
        })
        .collect()
}

/// Derive per-spec return ArgRepr from `return_tys`, then force ValueRef
/// for every spec in `tagged_return_specs`. Closure-target spec bodies
/// return ValueRef i64, matching the closure-target sig
/// (cps-in-clif.md §8.2). This extends to every fn in
/// `tagged_return_specs`: a spec whose reachable exits forward the
/// closure-target/indirect ValueRef seam through its own outer sig must
/// keep that outer return tagged as `ValueRef`. Declaring that outer
/// return as RawInt/RawF64 would let the caller read tag-shifted bits as
/// a raw number (e.g. 42 → 337).
///
/// `tagged_return_specs` is the precise grain; specs whose
/// `TailCallClosure` resolves via closure_lit keep their narrow return
/// repr.
fn build_return_reprs<T: Types<Ty = Ty>>(
    t: &mut T,
    return_tys: &[Ty],
    tagged_return_specs: &HashSet<u32>,
) -> Vec<ArgRepr> {
    return_tys
        .iter()
        .enumerate()
        .map(|(sid, ty)| {
            let r = ArgRepr::from_ty(t, ty);
            if tagged_return_specs.contains(&(sid as u32)) {
                ArgRepr::ValueRef
            } else {
                r
            }
        })
        .collect()
}

/// Emit fz_main_trampoline. The closure-target body for a main-style
/// entry's synthetic inner closure. The inner closure carries the raw
/// `(cont)` main fn pointer in capture[0] (a raw int, so GC never treats it
/// as a heap reference). Closure-target sig `(self, cont) tail`: read main_fp
/// from capture[0] and `call_indirect Tail main_fp(cont)`. This bridges a
/// plain main fn — whose body sig is `(cont)` — into the uniform
/// entry-thunk + `fz_resume` dispatch path without forcing a closure-target
/// body onto the entry fn itself.
fn emit_main_trampoline<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    runtime: &RuntimeRefs,
) -> Result<(), CodegenError> {
    let mut sig = Signature::new(CallConv::Tail);
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    emit_fn_body(m, fbctx, sig, runtime.main_trampoline_id, |m, b| {
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let self_cl = b.block_params(entry)[0];
        let cont = b.block_params(entry)[1];
        let mut shim_cache = CodegenCache::default();
        let mut cg = CodegenFn::for_runtime_shim(runtime, b, m, &mut shim_cache);
        // capture[0] holds the raw `(cont)` main fn pointer (raw int).
        let zero = cg.b.ins().iconst(types::I64, 0);
        let main_fp = cg.closure_capture_i64(self_cl, zero);
        let mut main_sig = Signature::new(CallConv::Tail);
        main_sig.params.push(AbiParam::new(types::I64));
        main_sig.returns.push(AbiParam::new(types::I64));
        let sig_ref = cg.b.func.import_signature(main_sig);
        let inst = cg.b.ins().call_indirect(sig_ref, main_fp, &[cont]);
        let r = cg.b.inst_results(inst)[0];
        cg.b.ins().return_(&[r]);
    })
    .map_err(|e| CodegenError::new(format!("define fz_main_trampoline: {}", e)))
}

/// Emit fz_drain_dtor_entry. SystemV scheduler-callable shim that
/// invokes a 1-arg resource dtor closure with its payload. Picks a
/// Strict halt-cont via fz_get_halt_cont, reads the body addr through
/// the closure ABI, and Tail-CC indirect-calls
/// `(payload_ref, closure, halt_cl)`. Result is discarded by the caller.
/// Sig: `(closure:i64, payload_ref:i64) -> i64 system_v`.
fn emit_drain_dtor_entry<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    runtime: &RuntimeRefs,
) -> Result<(), CodegenError> {
    let mut sig = Signature::new(CallConv::SystemV);
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    emit_fn_body(m, fbctx, sig, runtime.drain_dtor_entry_id, |m, b| {
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let closure = b.block_params(entry)[0];
        let payload_ref = b.block_params(entry)[1];
        let mut shim_cache = CodegenCache::default();
        let mut cg = CodegenFn::for_runtime_shim(runtime, b, m, &mut shim_cache);
        // Strict halt-cont (kind=0). Dtor return is discarded;
        // ValueRef avoids RawInt/F64 unboxing.
        let strict_addr = cg.func_addr(runtime.halt_cont_body_strict_id);
        let zero = cg.b.ins().iconst(types::I32, 0);
        let halt_cl = cg.get_halt_cont(strict_addr, zero);
        let code = cg.closure_code_ref(closure);
        // Closure-target body sig: `(args..., self, cont) tail -> i64`.
        // Generic args are one-word ValueRefs.
        let mut closure_sig = Signature::new(CallConv::Tail);
        closure_sig.params.push(AbiParam::new(types::I64)); // x ValueRef
        closure_sig.params.push(AbiParam::new(types::I64)); // self
        closure_sig.params.push(AbiParam::new(types::I64)); // cont
        closure_sig.returns.push(AbiParam::new(types::I64));
        let sig_ref = cg.b.func.import_signature(closure_sig);
        let inst =
            cg.b.ins()
                .call_indirect(sig_ref, code, &[payload_ref, closure, halt_cl]);
        let r = cg.b.inst_results(inst)[0];
        cg.b.ins().return_(&[r]);
    })
    .map_err(|e| CodegenError::new(format!("define fz_drain_dtor_entry: {}", e)))
}

/// Emit fz_entry_thunk. The uniform first-entry wrapper for a freshly
/// spawned task. A task's `runnable` is an entry thunk whose single capture
/// is the task's inner closure (a user lambda for `spawn_closure`, or the
/// synthetic `fz_main_trampoline` closure for a main-style entry). The
/// scheduler resumes the thunk through the one `fz_resume` shim, so the thunk
/// has the resume-shaped closure-target sig `(self) -> i64 tail`. The body
/// reads the inner closure from capture[0], picks the halt-cont matching the
/// inner closure's halt_kind, and tail-calls the inner body `(inner, halt_cl)`
/// — exactly the launch the retired `fz_spawn_entry` performed, but driven
/// off the captured inner instead of a scheduler argument.
///
/// Closure metadata layout:
///   off 0  : kind (u16)         off 4  : size_bytes (u32)
///   off 2  : flags (u16)        off 8  : schema_id (u32)
///                               off 12 : _reserved (u32)
/// flags low 14 bits = captured_count; high 2 bits = halt_kind.
fn emit_entry_thunk<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    runtime: &RuntimeRefs,
) -> Result<(), CodegenError> {
    let mut sig = Signature::new(CallConv::Tail);
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    emit_fn_body(m, fbctx, sig, runtime.entry_thunk_id, |m, b| {
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let self_cl = b.block_params(entry)[0];
        let mut shim_cache = CodegenCache::default();
        let mut cg = CodegenFn::for_runtime_shim(runtime, b, m, &mut shim_cache);
        // capture[0] is the inner closure to launch.
        let zero_idx = cg.b.ins().iconst(types::I64, 0);
        let closure = cg.closure_capture_ref(self_cl, zero_idx);
        let kind = cg.closure_halt_kind_ref(closure);
        // Select halt_cont_body_addr by kind. Branchless via three
        // func_addrs + a tiny dispatch — keeps the thunk a leaf.
        let a_strict = cg.func_addr(runtime.halt_cont_body_strict_id);
        let a_i64 = cg.func_addr(runtime.halt_cont_body_i64_id);
        let a_f64 = cg.func_addr(runtime.halt_cont_body_f64_id);
        let one = cg.b.ins().iconst(types::I32, 1);
        let two = cg.b.ins().iconst(types::I32, 2);
        let is_i64 = cg.b.ins().icmp(IntCC::Equal, kind, one);
        let is_f64 = cg.b.ins().icmp(IntCC::Equal, kind, two);
        let pick_i64_or_tagged = cg.b.ins().select(is_i64, a_i64, a_strict);
        let hcb_addr = cg.b.ins().select(is_f64, a_f64, pick_i64_or_tagged);
        let halt_cl = cg.get_halt_cont(hcb_addr, kind);
        // Read inner closure body addr through the runtime ABI and invoke as
        // closure-target sig `(self, cont) tail` (zero user args).
        let code = cg.closure_code_ref(closure);
        let mut closure_sig = Signature::new(CallConv::Tail);
        closure_sig.params.push(AbiParam::new(types::I64)); // self
        closure_sig.params.push(AbiParam::new(types::I64)); // cont
        closure_sig.returns.push(AbiParam::new(types::I64));
        let sig_ref = cg.b.func.import_signature(closure_sig);
        let inst = cg.b.ins().call_indirect(sig_ref, code, &[closure, halt_cl]);
        let r = cg.b.inst_results(inst)[0];
        cg.b.ins().return_(&[r]);
    })
    .map_err(|e| CodegenError::new(format!("define fz_entry_thunk: {}", e)))
}

/// Emit three fz_halt_cont_body fns, one per repr. Generic ValueRef
/// bodies receive `(value_ref, self)`; RawInt / RawF64 variants stay
/// narrow as `(value, self)`.
fn emit_halt_cont_bodies<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    runtime: &RuntimeRefs,
) -> Result<(), CodegenError> {
    let mut sig = Signature::new(CallConv::Tail);
    push_repr_param(&mut sig, ArgRepr::ValueRef);
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    emit_fn_body(m, fbctx, sig, runtime.halt_cont_body_strict_id, |m, b| {
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let value_ref = b.block_params(entry)[0];
        let hi_fref = m.declare_func_in_func(runtime.halt_implicit_ref_id, b.func);
        let process = b.ins().get_pinned_reg(types::I64);
        b.ins().call(hi_fref, &[process, value_ref]);
        let zero = b.ins().iconst(types::I64, 0);
        b.ins().return_(&[zero]);
    })
    .map_err(|e| CodegenError::new(format!("define halt_cont_body: {}", e)))?;
    for (body_id, val_ty, halt_impl_id) in [
        (runtime.halt_cont_body_i64_id, types::I64, runtime.halt_implicit_i64_id),
        (runtime.halt_cont_body_f64_id, types::F64, runtime.halt_implicit_f64_id),
    ] {
        let mut sig = Signature::new(CallConv::Tail);
        sig.params.push(AbiParam::new(val_ty));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        emit_fn_body(m, fbctx, sig, body_id, |m, b| {
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);
            let val = b.block_params(entry)[0];
            let hi_fref = m.declare_func_in_func(halt_impl_id, b.func);
            let process = b.ins().get_pinned_reg(types::I64);
            b.ins().call(hi_fref, &[process, val]);
            let zero = b.ins().iconst(types::I64, 0);
            b.ins().return_(&[zero]);
        })
        .map_err(|e| CodegenError::new(format!("define halt_cont_body: {}", e)))?;
    }
    Ok(())
}

/// Single SystemV `fz_resume(cont) -> i64` shim. Bound args live in
/// the outcome closure env, so the shim sig is fixed regardless of
/// clause arity. Body:
///     code = call fz_closure_code_ref(cont)
///     call_indirect Tail(cont) -> i64
///     return result
fn emit_resume<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    runtime: &RuntimeRefs,
) -> Result<FuncId, CodegenError> {
    let mut sig = Signature::new(CallConv::SystemV);
    sig.params.push(AbiParam::new(types::I64)); // cont
    sig.returns.push(AbiParam::new(types::I64));
    let id = m
        .declare_function("fz_resume", Linkage::Local, &sig)
        .map_err(|e| CodegenError::new(format!("declare fz_resume: {}", e)))?;
    emit_fn_body(m, fbctx, sig, id, |m, b| {
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let cont = b.block_params(entry)[0];
        let mut shim_cache = CodegenCache::default();
        let mut cg = CodegenFn::for_runtime_shim(runtime, b, m, &mut shim_cache);
        let code = cg.closure_code_ref(cont);
        let mut stub_sig = Signature::new(CallConv::Tail);
        stub_sig.params.push(AbiParam::new(types::I64)); // self
        stub_sig.returns.push(AbiParam::new(types::I64));
        let sig_ref = cg.b.func.import_signature(stub_sig);
        let inst = cg.b.ins().call_indirect(sig_ref, code, &[cont]);
        let r = cg.b.inst_results(inst)[0];
        cg.b.ins().return_(&[r]);
    })
    .map_err(|e| CodegenError::new(format!("define fz_resume: {}", e)))?;
    Ok(id)
}

/// Declare one Cranelift function per real SpecId, named
/// `fz_fn_{spec_id.0}`. Sentinel slots are skipped — no module
/// declaration is made. Any-key SpecId.0 == FnId.0 so the existing
/// closure / Spawn / Receive paths (which iconst fn_id.0 as the
/// schema_id) keep landing on the right entry.
fn declare_spec_fns<M: cranelift_module::Module>(
    m: &mut M,
    linkage: Linkage,
    spec_count: usize,
    spec_fnidx: &[Option<usize>],
    fn_sigs: &[Signature],
) -> Result<HashMap<u32, FuncId>, CodegenError> {
    let mut fn_ids: HashMap<u32, FuncId> = HashMap::new();
    for sid in 0..spec_count {
        if spec_fnidx[sid].is_none() {
            continue;
        }
        let name = format!("fz_fn_{}", sid);
        let id = m
            .declare_function(&name, linkage, &fn_sigs[sid])
            .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))?;
        fn_ids.insert(sid as u32, id);
    }
    Ok(fn_ids)
}

/// Pre-pass over Term::ReceiveMatched sites: one matcher FuncId per
/// site, keyed by `(fn_id.0, block_id.0)`. Declared up front so the
/// park-site terminator arm can take a `func_addr` of an as-yet-unemitted
/// symbol; the body is emitted in a post-fn-loop pass.
type MatcherFnIds = HashMap<(u32, u32), FuncId>;
type ReceiveMatchedSites = Vec<(FnId, BlockId)>;
type MidFlightContFnIds = HashMap<(u32, Vec<MidFlightArgShape>), FuncId>;

fn declare_matcher_fns<M: cranelift_module::Module>(
    m: &mut M,
    module: &Module,
    tel: &dyn Telemetry,
) -> Result<(MatcherFnIds, ReceiveMatchedSites), CodegenError> {
    let mut matcher_fn_ids: HashMap<(u32, u32), FuncId> = HashMap::new();
    let mut receive_matched_sites: Vec<(FnId, BlockId)> = Vec::new();
    for f in &module.fns {
        for blk in &f.blocks {
            let Term::ReceiveMatched {
                clauses,
                matcher,
                after,
                pinned,
                captures,
                ..
            } = &blk.terminator
            else {
                continue;
            };
            let name = format!("fz_matcher_fn_{}_b{}", f.id.0, blk.id.0);
            let m_id = declare_matcher(m, &name)?;
            matcher_fn_ids.insert((f.id.0, blk.id.0), m_id);
            receive_matched_sites.push((f.id, blk.id));
            tel.execute(
                &["fz", "codegen", "receive", "site"],
                &crate::measurements! {
                    fn_id: f.id.0 as u64,
                    block_id: blk.id.0 as u64,
                    clause_count: clauses.len() as u64,
                    after_count: if after.is_some() { 1u64 } else { 0u64 },
                    pinned_count: pinned.len() as u64,
                    capture_count: captures.len() as u64,
                    matcher_input_count: matcher.inputs.len() as u64,
                    matcher_prepared_key_count: matcher.prepared_keys.len() as u64,
                    matcher_node_count: matcher.nodes.len() as u64,
                },
                &crate::metadata! {
                    module_path: module.module_path().to_owned(),
                    fn_name: f.name.clone(),
                    matcher: opaque(matcher),
                },
            );
        }
    }
    Ok((matcher_fn_ids, receive_matched_sites))
}

/// Emit matcher fn bodies for every Term::ReceiveMatched site
/// discovered in the pre-pass above. Matchers were declared before the
/// fn-compilation loop so the park-site terminator arm could take
/// `func_addr` of the still-undefined symbols. Bodies are pure leaf fns
/// (no allocation, no extern); the emitter refuses any clause with a
/// guard.
#[allow(clippy::too_many_arguments)]
fn emit_matcher_bodies<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    module: &Module,
    runtime: &RuntimeRefs,
    tuple_schema_ids: &HashMap<usize, u32>,
    matcher_fn_ids: &HashMap<(u32, u32), FuncId>,
    receive_matched_sites: &[(FnId, BlockId)],
    tel: &dyn Telemetry,
) -> Result<(), CodegenError> {
    for (fn_id, blk_id) in receive_matched_sites {
        let f = module.fn_by_id(*fn_id);
        let blk = f.blocks.iter().find(|b| b.id == *blk_id).unwrap();
        let Term::ReceiveMatched {
            clauses,
            pinned,
            matcher,
            ..
        } = &blk.terminator
        else {
            unreachable!("receive_matched_sites holds only Term::ReceiveMatched terms");
        };
        let m_id = matcher_fn_ids[&(fn_id.0, blk_id.0)];
        let display_name = format!("fz_matcher_fn_{}_b{}", fn_id.0, blk_id.0);
        let (block_count, instruction_count) = {
            let _span = tel.span(
                &["fz", "codegen", "lower_function"],
                crate::metadata! {
                    body_kind: "receive_matcher",
                    module_path: module.module_path().to_owned(),
                    fn_name: display_name.clone(),
                    fn_id: fn_id.0 as u64,
                    block_id: blk_id.0 as u64,
                },
            );
            emit_matcher_body_from_matcher(
                m,
                fbctx,
                m_id,
                module,
                tuple_schema_ids,
                pinned.as_slice(),
                clauses.as_slice(),
                matcher,
                &MatcherRuntimeHelpers {
                    value_eq_typed_id: Some(runtime.value_eq_ref_id),
                    matcher_eq_bytes_id: Some(runtime.matcher_eq_bytes_id),
                    matcher_map_get_id: Some(runtime.matcher_map_get_id),
                    matcher_map_get_ref_id: Some(runtime.matcher_map_get_ref_id),
                    type_of_id: Some(runtime.type_of_id),
                    unbox_int_id: Some(runtime.unbox_int_id),
                    unbox_float_id: Some(runtime.unbox_float_id),
                    unbox_atom_id: Some(runtime.unbox_atom_id),
                    struct_schema_id_ref_id: Some(runtime.struct_schema_id_ref_id),
                    truthy_ref_id: Some(runtime.truthy_ref_id),
                    box_int_for_any_id: Some(runtime.box_int_for_any_id),
                    box_float_for_any_id: Some(runtime.box_float_for_any_id),
                    box_atom_for_any_id: Some(runtime.box_atom_for_any_id),
                    map_is_map_id: Some(runtime.map_is_map_id),
                    bs_reader_init_id: Some(runtime.bs_reader_init_ref_id),
                    bs_read_field_id: Some(runtime.bs_read_field_ref_id),
                    struct_get_field_id: Some(runtime.struct_get_field_id),
                    list_is_cons_id: Some(runtime.list_is_cons_id),
                    list_head_id: Some(runtime.list_head_fallback_id),
                    list_tail_id: Some(runtime.list_tail_fallback_id),
                },
            )?
        };
        tel.execute(
            &["fz", "codegen", "function_lowered"],
            &crate::measurements! {
                fn_id: fn_id.0 as u64,
                block_id: blk_id.0 as u64,
                block_count: block_count as u64,
                instruction_count: instruction_count as u64,
                clause_count: clauses.len() as u64,
                pinned_count: pinned.len() as u64,
                matcher_input_count: matcher.inputs.len() as u64,
                matcher_prepared_key_count: matcher.prepared_keys.len() as u64,
                matcher_node_count: matcher.nodes.len() as u64,
            },
            &crate::metadata! {
                body_kind: "receive_matcher",
                module_path: module.module_path().to_owned(),
                fn_name: display_name,
                matcher: opaque(matcher),
            },
        );
    }
    Ok(())
}

/// Emit SystemV stub + Tail-CC body for every declared mid-flight
/// continuation. The SystemV stub bridges scheduler-resume into Tail-CC;
/// the tail body replays each argument from the closure capture array
/// and `return_call_indirect`s the callee body with its narrow ABI.
fn emit_mid_flight_cont_bodies<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    runtime: &RuntimeRefs,
    fn_ids: &HashMap<u32, FuncId>,
    mid_flight_cont_fn_ids: &HashMap<(u32, Vec<MidFlightArgShape>), FuncId>,
    mid_flight_cont_tail_fn_ids: &HashMap<(u32, Vec<MidFlightArgShape>), FuncId>,
) -> Result<(), CodegenError> {
    for ((callee_sid, arg_shapes), stub_id) in mid_flight_cont_fn_ids.clone() {
        let key = (callee_sid, arg_shapes.clone());
        let tail_id = *mid_flight_cont_tail_fn_ids
            .get(&key)
            .ok_or_else(|| CodegenError::new(format!("missing mid-flight continuation tail {callee_sid}")))?;
        let callee_fid = *fn_ids
            .get(&callee_sid)
            .ok_or_else(|| CodegenError::new(format!("missing callee FuncId {callee_sid}")))?;
        let stub_name = format!("fz_mid_flight_cont_fn_{callee_sid}");
        let mut stub_sig = Signature::new(CallConv::SystemV);
        stub_sig.params.push(AbiParam::new(types::I64));
        stub_sig.returns.push(AbiParam::new(types::I64));
        emit_fn_body(m, fbctx, stub_sig, stub_id, move |m, b| {
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);
            let self_bits = b.block_params(entry)[0];
            let tail_ref = m.declare_func_in_func(tail_id, b.func);
            let inst = b.ins().call(tail_ref, &[self_bits]);
            let result = b.inst_results(inst)[0];
            b.ins().return_(&[result]);
        })
        .map_err(|e| CodegenError::new(format!("define {}: {}", stub_name, e)))?;

        let tail_name = format!("fz_mid_flight_cont_fn_{callee_sid}_tail");
        let mut tail_sig = Signature::new(CallConv::Tail);
        tail_sig.params.push(AbiParam::new(types::I64));
        tail_sig.returns.push(AbiParam::new(types::I64));
        emit_fn_body(m, fbctx, tail_sig, tail_id, move |m, b| {
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);
            let self_bits = b.block_params(entry)[0];
            let mut args = Vec::with_capacity(arg_shapes.iter().map(MidFlightArgShape::abi_arity).sum());
            let mut shim_cache = CodegenCache::default();
            let mut cg = CodegenFn::for_runtime_shim(runtime, b, m, &mut shim_cache);
            for (i, arg_shape) in arg_shapes.iter().enumerate() {
                let value_ref = cg.closure_capture_ref_at(self_bits, i);
                arg_shape.replay_from_capture(&mut cg, CodegenValue::AnyRef(value_ref), &mut args);
            }
            let mut callee_sig = Signature::new(CallConv::Tail);
            for arg_shape in &arg_shapes {
                arg_shape.push_param(&mut callee_sig);
            }
            callee_sig.returns.push(AbiParam::new(types::I64));
            let sig_ref = cg.b.func.import_signature(callee_sig);
            let fn_ptr = cg.func_addr(callee_fid);
            cg.b.ins().return_call_indirect(sig_ref, fn_ptr, &args);
        })
        .map_err(|e| CodegenError::new(format!("define {}: {}", tail_name, e)))?;
    }
    Ok(())
}

/// Declare SystemV + Tail-CC stubs for every back-edge TailCall to a
/// native callee. Each (callee_sid, arg_shapes) tuple uniquely keys a
/// pair of mid-flight continuation FuncIds; the SystemV stub bridges
/// scheduler-resume into Tail-CC and the Tail-CC body replays the saved
/// arguments before tail-calling the callee. Returns the two FuncId maps
/// consumed by the body-emission pass.
#[allow(clippy::too_many_arguments)]
fn declare_mid_flight_conts<T: Types<Ty = Ty>, M: cranelift_module::Module>(
    t: &mut T,
    m: &mut M,
    module: &Module,
    module_plan: &ModulePlan,
    spec_registry: &SpecRegistry,
    spec_fnidx: &[Option<usize>],
    param_reprs: &[Vec<ArgRepr>],
    native_abi_fns: &HashSet<FnId>,
    closure_capture_counts: &HashMap<FnId, usize>,
) -> Result<(MidFlightContFnIds, MidFlightContFnIds), CodegenError> {
    let mut mid_flight_cont_fn_ids: HashMap<(u32, Vec<MidFlightArgShape>), FuncId> = HashMap::new();
    let mut mid_flight_cont_tail_fn_ids: HashMap<(u32, Vec<MidFlightArgShape>), FuncId> = HashMap::new();
    for (caller_sid, caller_key) in spec_registry.iter() {
        let Some(caller_idx) = spec_fnidx[caller_sid.0 as usize] else {
            continue;
        };
        let Some(fn_types) = module_plan.specs.get(caller_key) else {
            continue;
        };
        let f = &module.fns[caller_idx];
        for blk in &f.blocks {
            if let Term::TailCall {
                ident,
                callee: _,
                args,
                is_back_edge: true,
                ..
            } = &blk.terminator
            {
                if !fn_types.reachable_blocks.contains(&blk.id) {
                    continue;
                };
                let cid = CallsiteId {
                    caller: caller_key.fn_id,
                    ident: ident.clone(),
                    slot: EmitSlot::Direct,
                };
                let Some(target) = fn_types.local_call_target(&cid) else {
                    continue;
                };
                if !native_abi_fns.contains(&target.fn_id) {
                    continue;
                }
                let Some(callee_sid) = spec_registry.resolve_spec_key(t, target) else {
                    continue;
                };
                let callee_sid = callee_sid.0;
                let mut arg_shapes: Vec<MidFlightArgShape> = param_reprs[callee_sid as usize]
                    .iter()
                    .take(args.len())
                    .copied()
                    .map(MidFlightArgShape::Value)
                    .collect();
                if closure_capture_counts.contains_key(&target.fn_id) {
                    arg_shapes.push(MidFlightArgShape::HeapRef);
                }
                arg_shapes.push(MidFlightArgShape::HeapRef);
                let key = (callee_sid, arg_shapes);
                if mid_flight_cont_fn_ids.contains_key(&key) {
                    continue;
                }
                let cont_name = format!("fz_mid_flight_cont_fn_{}_{}", callee_sid, mid_flight_cont_fn_ids.len());
                let mut cont_sig = Signature::new(CallConv::SystemV);
                cont_sig.params.push(AbiParam::new(types::I64));
                cont_sig.returns.push(AbiParam::new(types::I64));
                let cont_id = m
                    .declare_function(&cont_name, Linkage::Local, &cont_sig)
                    .map_err(|e| CodegenError::new(format!("declare {}: {}", cont_name, e)))?;
                let cont_tail_name = format!("{cont_name}_tail");
                let mut cont_tail_sig = Signature::new(CallConv::Tail);
                cont_tail_sig.params.push(AbiParam::new(types::I64));
                cont_tail_sig.returns.push(AbiParam::new(types::I64));
                let cont_tail_id = m
                    .declare_function(&cont_tail_name, Linkage::Local, &cont_tail_sig)
                    .map_err(|e| CodegenError::new(format!("declare {}: {}", cont_tail_name, e)))?;
                mid_flight_cont_fn_ids.insert(key.clone(), cont_id);
                mid_flight_cont_tail_fn_ids.insert(key, cont_tail_id);
            }
        }
    }
    Ok((mid_flight_cont_fn_ids, mid_flight_cont_tail_fn_ids))
}

pub(crate) fn prepare_module_for_authoritative_plan<
    T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes + VisibilityTypes,
>(
    t: &mut T,
    module: &Module,
    tel: &dyn Telemetry,
) -> Module {
    #[cfg(test)]
    fn assert_post_transform_planner_consistency<T: Types<Ty = Ty> + ClosureTypes + RenderTypes>(
        t: &mut T,
        module: &Module,
        context: &str,
    ) {
        assert_module_planner_consistent(t, module, context);
    }

    let mut working = module.clone();
    let capabilities = plan_callable_capabilities(t, &working);
    rewrite_known_target_closures(t, &mut working, &capabilities);
    #[cfg(not(test))]
    inline_module_with_plan(&mut working, &capabilities);
    #[cfg(test)]
    if !INLINE_DISABLED.with(|d| d.get()) {
        inline_module_with_plan(&mut working, &capabilities);
        assert_post_transform_planner_consistency(
            t,
            &working,
            "inline_module_with_plan in prepare_module_for_authoritative_plan",
        );
    }
    fuse_blocks_with_telemetry(&mut working, tel);
    #[cfg(not(test))]
    let _ = reduce_module_with_telemetry(t, &mut working, tel);
    #[cfg(test)]
    if !REDUCER_DISABLED.with(|d| d.get()) {
        let _ = reduce_module_with_telemetry(t, &mut working, tel);
    }
    inline_single_use_conts(&mut working);
    #[cfg(test)]
    assert_post_transform_planner_consistency(
        t,
        &working,
        "inline_single_use_conts in prepare_module_for_authoritative_plan",
    );
    truncate_diverging_blocks(module.module_path(), &mut working, tel);
    fold_module(&mut working);
    dce_module_with_telemetry(&mut working, tel);
    #[cfg(test)]
    assert_post_transform_planner_consistency(
        t,
        &working,
        "dce_module_with_telemetry in prepare_module_for_authoritative_plan",
    );
    dce_module_level(&mut working);
    #[cfg(test)]
    assert_post_transform_planner_consistency(t, &working, "dce_module_level in prepare_module_for_authoritative_plan");
    working
}

#[allow(dead_code)]
pub(crate) fn compile_with_backend_impl<
    B: Backend,
    T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes + VisibilityTypes,
>(
    t: &mut T,
    module: &Module,
    backend: B,
    tel: &dyn Telemetry,
) -> Result<B::Output, CodegenError> {
    if let Some(edge) = module.external_call_edges.first() {
        return Err(CodegenError::new(format!(
            "unresolved external module call `{}`",
            edge.target
        )));
    }
    let working = prepare_module_for_authoritative_plan(t, module, tel);
    let module_plan = plan_module(t, &working, tel);
    compile_with_backend_preplanned_impl(t, working, module_plan, backend, tel)
}

pub(crate) fn compile_with_backend_preplanned<
    B: Backend,
    T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes + VisibilityTypes,
>(
    t: &mut T,
    module: &Module,
    module_plan: &ModulePlan,
    backend: B,
    tel: &dyn Telemetry,
) -> Result<B::Output, CodegenError> {
    compile_with_backend_preplanned_impl(t, module.clone(), module_plan.clone(), backend, tel)
}

fn compile_with_backend_preplanned_impl<
    B: Backend,
    T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes + VisibilityTypes,
>(
    t: &mut T,
    mut working: Module,
    mut module_plan: ModulePlan,
    mut backend: B,
    tel: &dyn Telemetry,
) -> Result<B::Output, CodegenError> {
    if let Some(edge) = working.external_call_edges.first() {
        return Err(CodegenError::new(format!(
            "unresolved external module call `{}`",
            edge.target
        )));
    }

    let compile_nonce = next_compile_nonce();
    let _compile_span = tel.span(
        &["fz", "compile"],
        crate::metadata! {
            compile_nonce: compile_nonce,
            module_path: working.module_path().to_owned(),
        },
    );

    let runtime = declare_runtime_symbols(backend.module_mut())?;

    let mut fbctx = FunctionBuilderContext::new();

    emit_main_trampoline(backend.module_mut(), &mut fbctx, &runtime)?;
    emit_drain_dtor_entry(backend.module_mut(), &mut fbctx, &runtime)?;
    emit_entry_thunk(backend.module_mut(), &mut fbctx, &runtime)?;
    emit_halt_cont_bodies(backend.module_mut(), &mut fbctx, &runtime)?;

    let user_schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    user_schemas.borrow_mut().closure_env(0);
    let (tuple_arities, tuple_schema_ids, bs_tuple_arity1_schema, bs_tuple_arity3_schema) =
        collect_tuple_arities_and_register_schemas(&working, &user_schemas);
    let named_schema_ids = {
        let mut ids = HashMap::new();
        let mut reg = user_schemas.borrow_mut();
        for (name, fields) in &working.struct_schemas {
            let id = reg.register(Schema::named_struct(name.clone(), fields.clone()));
            ids.insert(name.clone(), id);
        }
        ids
    };

    #[cfg(debug_assertions)]
    let call_shapes_pre = snapshot_call_shapes(&working);
    lower_destinations(&mut working);
    verify_module(&working).map_err(|errors| {
        CodegenError::new(format!(
            "destination-passing IR invariant failed:\n{}",
            errors.iter().map(ToString::to_string).collect::<Vec<_>>().join("\n")
        ))
    })?;
    #[cfg(debug_assertions)]
    assert_no_new_call_shapes(&working, &call_shapes_pre);
    let diagnostics = resolve_module_types(t, &working, &mut module_plan);
    if let Some(diagnostic) = diagnostics.into_iter().next() {
        return Err(CodegenError::new(diagnostic.message).with_span(diagnostic.primary.span));
    }
    let module = &working;

    let planned_program = materialize_program(t, module, &module_plan, tel);
    let spec_registry = planned_program.spec_registry();
    let spec_count = planned_program.spec_count();
    let spec_keys = planned_program.spec_keys();
    let spec_fnidx = planned_program.spec_fn_indices();
    let spec_fn_types = planned_program.spec_plans();
    let abi_facts = AbiFacts::derive(module, &planned_program);

    let callable_entries = planned_program.callable_entries();

    let schemas = build_per_spec_schemas(t, module, spec_count, &spec_fnidx, &spec_fn_types);
    let frame_sizes: Vec<u32> = schemas.iter().map(|s| s.allocation_payload_size() as u32).collect();
    let return_tys = derive_return_tys(t, &spec_keys, &spec_fnidx, &module_plan);

    let param_reprs = derive_param_reprs(
        t,
        module,
        spec_count,
        &spec_fnidx,
        &spec_fn_types,
        &spec_keys,
        &abi_facts.cont_fns,
    );
    let tagged_return_specs = compute_tagged_return_specs(
        t,
        module,
        &spec_fnidx,
        &spec_fn_types,
        spec_registry,
        &abi_facts.closure_capture_counts,
    );
    let return_reprs = build_return_reprs(t, &return_tys, &tagged_return_specs);
    let tagged_slot0_cont_specs = compute_tagged_slot0_cont_specs(
        t,
        module,
        spec_count,
        &spec_fnidx,
        &spec_fn_types,
        spec_registry,
        &return_reprs,
    );
    let param_reprs = refine_param_reprs_for_tagging(param_reprs, &tagged_slot0_cont_specs);

    let fn_sigs = build_fn_sigs(
        module,
        spec_count,
        spec_fnidx,
        spec_keys,
        &param_reprs,
        &abi_facts.native_fns,
        &abi_facts.cont_fns,
        &abi_facts.closure_capture_counts,
        &abi_facts.cont_extras_count,
    );

    let linkage = backend.fn_linkage();
    let fn_ids = declare_spec_fns(backend.module_mut(), linkage, spec_count, spec_fnidx, &fn_sigs)?;
    let callable_entry_fn_ids =
        declare_callable_entry_fns(backend.module_mut(), callable_entries, &param_reprs, spec_keys)?;

    let (mid_flight_cont_fn_ids, mid_flight_cont_tail_fn_ids) = declare_mid_flight_conts(
        t,
        backend.module_mut(),
        module,
        &module_plan,
        spec_registry,
        spec_fnidx,
        &param_reprs,
        &abi_facts.native_fns,
        &abi_facts.closure_capture_counts,
    )?;

    let bs_const_data: RefCell<HashMap<Vec<u8>, BsConstSyms>> = RefCell::new(HashMap::new());
    let reachable = planned_program.reachable_specs();

    let (matcher_fn_ids, receive_matched_sites) = declare_matcher_fns(backend.module_mut(), module, tel)?;
    let verifier_isa = host_isa();

    for sid in 0..spec_count {
        let Some(fn_idx) = spec_fnidx[sid] else {
            continue;
        };
        let func_id = *fn_ids.get(&(sid as u32)).unwrap();
        let mut ctx = backend.module_mut().make_context();
        ctx.func.signature = fn_sigs[sid].clone();

        if !reachable.contains(&(sid as u32)) {
            use cranelift_codegen::ir::TrapCode;
            use cranelift_frontend::FunctionBuilder;
            {
                let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
                let entry = b.create_block();
                b.append_block_params_for_function_params(entry);
                b.switch_to_block(entry);
                b.seal_block(entry);
                b.ins().trap(TrapCode::user(1).unwrap());
                b.finalize();
            }
            backend
                .module_mut()
                .define_function(func_id, &mut ctx)
                .map_err(|e| CodegenError::new(format!("define unreached fz_fn_{}: {}", sid, e)))?;
            backend.module_mut().clear_context(&mut ctx);
            continue;
        }
        let ft = spec_fn_types[sid].expect("non-sentinel spec must have SpecPlan");
        let planned_body = planned_program.executable_body(SpecId(sid as u32));
        let f = &planned_body.body;
        debug_assert_eq!(planned_body.spec_id.0, sid as u32);
        debug_assert_eq!(planned_body.fn_idx, fn_idx);
        debug_assert_eq!(planned_body.fn_id, f.id);
        debug_assert_eq!(&planned_body.spec_key, &spec_keys[sid]);

        let want_asm = ASM_RECORD.with(|c| c.borrow().is_some());
        if want_asm {
            ctx.set_disasm(true);
        }
        #[cfg(debug_assertions)]
        emit_and_assert_spec_dispatch_coverage(tel, f, ft, planned_body.spec_id.0, &planned_body.spec_key);
        let display_name = if planned_body.spec_id.0 == planned_body.fn_id.0 {
            f.name.clone()
        } else {
            format!("{}_s{}", f.name, planned_body.spec_id.0)
        };
        let cg_env = CodegenEnv {
            telemetry: tel,
            runtime: &runtime,
            module,
            fn_types: ft,
            active_spec_id: planned_body.spec_id.0,
            active_body_fn_id: planned_body.fn_id,
            active_body_name: &display_name,
            spec_registry,
            fn_ids: &fn_ids,
            callable_entry_fn_ids: &callable_entry_fn_ids,
            mid_flight_cont_tail_fn_ids: &mid_flight_cont_tail_fn_ids,
            tuple_schema_ids: &tuple_schema_ids,
            named_schema_ids: &named_schema_ids,
            bs_const_data: &bs_const_data,
            param_reprs: &param_reprs,
            return_reprs: &return_reprs,
            spec_keys,
            native_abi_fns: &abi_facts.native_fns,
            cont_target_fns: &abi_facts.cont_target_fns,
            cont_fns: &abi_facts.cont_fns,
            closure_capture_counts: &abi_facts.closure_capture_counts,
            cont_extras_count: &abi_facts.cont_extras_count,
            matcher_fn_ids: &matcher_fn_ids,
        };
        {
            let _span = tel.span(
                &["fz", "codegen", "lower_function"],
                crate::metadata! {
                    body_kind: "fz_spec",
                    module_path: module.module_path().to_owned(),
                    fn_name: display_name.clone(),
                    fn_id: planned_body.fn_id.0 as u64,
                    spec_id: planned_body.spec_id.0 as u64,
                },
            );
            compile_fn(
                backend.module_mut(),
                t,
                &mut ctx,
                &mut fbctx,
                &cg_env,
                &schemas,
                f,
                planned_body.spec_id.0,
                &module.source,
            )?;
            let (block_count, instruction_count) = cranelift_body_stats(&ctx.func);
            tel.execute(
                &["fz", "codegen", "function_lowered"],
                &crate::measurements! {
                    fn_id: planned_body.fn_id.0 as u64,
                    spec_id: planned_body.spec_id.0 as u64,
                    block_count: block_count as u64,
                    instruction_count: instruction_count as u64,
                    fz_block_count: f.blocks.len() as u64,
                },
                &crate::metadata! {
                    body_kind: "fz_spec",
                    module_path: module.module_path().to_owned(),
                    fn_name: display_name.clone(),
                },
            );
        }
        IR_TEXT_RECORD.with(|c| {
            if let Some(v) = c.borrow_mut().as_mut() {
                ctx.func.name = ir::UserFuncName::user(0, func_id.as_u32());
                let raw = ctx.func.display().to_string();
                let key_tys = codegen_key_to_tys(t, &spec_keys[sid].input);
                let header = build_typer_header(
                    t,
                    f,
                    ft,
                    &key_tys,
                    &spec_keys[sid].demand,
                    &return_tys[sid],
                    &param_reprs[sid],
                    return_reprs[sid],
                );
                let func_names = snapshot_func_names(backend.module_mut().declarations());
                let annotated = VALUE_DESCR_RECORD.with(|vd| {
                    let b = vd.borrow();
                    match b.as_ref() {
                        Some(map) => annotate_clif_dump(&raw, map, &func_names, &header),
                        None => {
                            let empty = HashMap::new();
                            annotate_clif_dump(&raw, &empty, &func_names, &header)
                        }
                    }
                });
                v.push((display_name.clone(), annotated));
            }
        });
        let fn_span = module.source.fn_span_of(f.id);
        cranelift_codegen::verifier::verify_function(&ctx.func, verifier_isa.as_ref()).map_err(|e| {
            CodegenError::new(format!(
                "verify {}:\n{}\n--- IR ---\n{}",
                display_name,
                e,
                ctx.func.display()
            ))
            .with_span(fn_span)
        })?;
        backend
            .module_mut()
            .define_function(func_id, &mut ctx)
            .map_err(|e| CodegenError::new(format!("define {}: {}", display_name, e)).with_span(fn_span))?;
        if want_asm
            && let Some(cc) = ctx.compiled_code()
            && let Some(vcode) = cc.vcode.as_ref()
        {
            ASM_RECORD.with(|c| {
                if let Some(v) = c.borrow_mut().as_mut() {
                    v.push((display_name.clone(), vcode.clone()));
                }
            });
        }
        backend.module_mut().clear_context(&mut ctx);
    }

    emit_matcher_bodies(
        backend.module_mut(),
        &mut fbctx,
        module,
        &runtime,
        &tuple_schema_ids,
        &matcher_fn_ids,
        &receive_matched_sites,
        tel,
    )?;

    let main_fn_id = module.fn_by_name("main").map(|f| f.id);

    let static_closure_targets =
        collect_static_closure_targets(callable_entries, &spec_keys, &callable_entry_fn_ids, &return_reprs);

    let diagnostics = collect_diagnostics(t, module, &module_plan, tel);
    let halt_reprs = compute_halt_reprs(
        t,
        module,
        spec_count,
        &spec_fnidx,
        &spec_fn_types,
        &spec_registry,
        &return_reprs,
    );
    let fn_halt_kinds = derive_fn_halt_kinds(module, &halt_reprs);
    emit_mid_flight_cont_bodies(
        backend.module_mut(),
        &mut fbctx,
        &runtime,
        &fn_ids,
        &mid_flight_cont_fn_ids,
        &mid_flight_cont_tail_fn_ids,
    )?;
    emit_callable_entry_bodies(
        backend.module_mut(),
        &mut fbctx,
        &runtime,
        &fn_ids,
        &callable_entry_fn_ids,
        callable_entries,
        &param_reprs,
        &spec_keys,
        tel,
        module.module_path(),
    )?;
    let resume_id = emit_resume(backend.module_mut(), &mut fbctx, &runtime)?;

    let metadata = CompiledMetadata {
        fn_ids,
        user_schemas,
        frame_sizes,
        atom_names: module.atom_names.clone(),
        bs_tuple_arity1_schema,
        bs_tuple_arity3_schema,
        tuple_arities: tuple_arities.iter().map(|&a| a as u32).collect(),
        named_schemas: module
            .struct_schemas
            .iter()
            .map(|(name, fields)| (name.clone(), fields.clone()))
            .collect(),
        diagnostics,
        main_fn_id,
        static_closure_targets,
        entry_thunk_id: runtime.entry_thunk_id,
        main_trampoline_id: runtime.main_trampoline_id,
        drain_dtor_entry_id: runtime.drain_dtor_entry_id,
        halt_cont_body_ids: [
            runtime.halt_cont_body_strict_id,
            runtime.halt_cont_body_i64_id,
            runtime.halt_cont_body_f64_id,
        ],
        fn_halt_kinds,
        resume_id,
    };

    backend.emit_metadata_carriers(&mut fbctx, &metadata)?;
    backend.finalize(metadata)
}
