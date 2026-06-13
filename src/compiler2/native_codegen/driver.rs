use super::receive::{DispatchRuntimeHelpers, declare_receive_dispatch, emit_receive_dispatch_body};
use super::*;
use crate::diag::Diagnostics;
use crate::fz_ir::{BlockId, DirectCallTarget, FnId, Module, Prim, Stmt, Term};
use crate::telemetry::value::opaque;
use crate::telemetry::{Telemetry, TelemetryExt as _};
use crate::types::{ClosureTypes, LiteralTypes, RenderTypes, Types, VisibilityTypes};
use cranelift_codegen::ir::{self, AbiParam, InstBuilder, Signature, condcodes::IntCC, types};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::FunctionBuilderContext;
use cranelift_module::{FuncId, Linkage, Module as ClModule};
use fz_runtime::heap::{FieldKind, Schema, SchemaRegistry};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

/// Walk every fn body collecting tuple arities used by MakeTuple /
/// DestTupleBegin / RuntimeTypePredicate facts, detecting any bitstring prim, then
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
                    Prim::TypeTest(_, _) => panic!("compiler2 native program should not carry legacy Prim::TypeTest"),
                    Prim::RuntimeTypeTest(_, descr) => {
                        tuple_arities.extend(descr.tuple_arities.values.iter().copied());
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

/// Build per-body frame schemas, refining entry-param kinds from each body's
/// settled `NativeBody.value_types`. The dense body id for FnId K lands at
/// index K (invariant) so any code path that uses fn_id.0 as a schema_id
/// continues to hit the right schema. Sentinel slots get a zero-field
/// placeholder schema; they're never reached at runtime.
fn build_per_spec_schemas<T: Types<Ty = Ty>>(t: &mut T, body_slots: &[Option<NativeCodegenBody<'_>>]) -> Vec<Schema> {
    let mut schemas: Vec<Schema> = Vec::with_capacity(body_slots.len());
    for body_slot in body_slots {
        let Some(body_slot) = body_slot.as_ref() else {
            schemas.push(build_frame_schema("__sentinel", &[]));
            continue;
        };
        let f = body_slot.body;
        let entry_block = f.block(f.entry);
        let mut kinds: Vec<FieldKind> = entry_block.params.iter().map(|_| FieldKind::AnyValue).collect();
        for (j, p) in entry_block.params.iter().enumerate() {
            let param_ty = body_slot
                .native_body
                .value_types
                .get(p)
                .copied()
                .unwrap_or_else(|| t.any());
            match ArgRepr::from_ty(t, &param_ty) {
                ArgRepr::RawF64 => kinds[j] = FieldKind::RawF64,
                ArgRepr::RawInt => kinds[j] = FieldKind::RawI64,
                _ => {}
            }
        }
        schemas.push(build_frame_schema(&f.name, &kinds));
    }
    schemas
}

/// Per-spec Cranelift Signature. Native fns get typed-arity i64s +
/// host_ctx; uniform fns get (i64, i64) -> i64. Sentinel slots get the
/// uniform sig — they're never declared.
///
/// Closure-target fn shape is gated on native (uniform closure targets
/// still go through the existing stub adapter).
#[allow(clippy::too_many_arguments)]
fn build_fn_sigs(module: &Module, surface: &NativeCodegenSurface<'_>) -> Vec<Signature> {
    surface
        .body_slots
        .iter()
        .map(|body_slot| match body_slot {
            Some(body_slot) => {
                let f = &module.fns[body_slot.fn_idx];
                let is_native = surface.native_abi_fns.contains(&f.id);
                let demand_abi = NativeDemandAbi::new(body_slot.native_body);
                build_fn_signature(
                    &surface.param_reprs[body_slot.codegen_id as usize],
                    is_native,
                    surface.cont_fns.contains(&f.id),
                    if is_native {
                        surface.closure_capture_counts.get(&f.id).copied()
                    } else {
                        None
                    },
                    Some(demand_abi.continuation_extras()),
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
    surface: &NativeCodegenSurface<'_>,
    fn_ids: &HashMap<u32, FuncId>,
    callable_entry_fn_ids: &HashMap<u32, FuncId>,
) -> Vec<(u32, u32, FuncId, u32)> {
    let mut targets = BTreeMap::new();
    for (&cl_sid, _) in surface
        .callable_entries
        .iter()
        .filter(|(_, entry)| entry.capture_count == 0)
    {
        let fn_id = surface.body_fn_id(cl_sid);
        let body_fid = *callable_entry_fn_ids
            .get(&cl_sid)
            .expect("zero-cap closure spec must have a callable-entry FuncId");
        let halt_kind = surface.return_reprs[cl_sid as usize].halt_kind();
        targets.insert(cl_sid, (fn_id.0, body_fid, halt_kind));
    }

    for body_slot in &surface.body_slots {
        let Some(body_slot) = body_slot.as_ref() else {
            continue;
        };
        let sid = body_slot.codegen_id;
        if surface.closure_capture_counts.get(&body_slot.fn_id) != Some(&0) {
            continue;
        }
        targets.entry(sid).or_insert_with(|| {
            let body_fid = *fn_ids
                .get(&sid)
                .expect("zero-cap closure-shaped spec must have a direct body FuncId");
            let halt_kind = surface.return_reprs[sid as usize].halt_kind();
            (body_slot.fn_id.0, body_fid, halt_kind)
        });
    }

    targets
        .into_iter()
        .map(|(sid, (fn_id, body_fid, halt_kind))| (sid, fn_id, body_fid, halt_kind))
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
    surface: &NativeCodegenSurface<'_>,
) -> Result<HashMap<u32, FuncId>, CodegenError> {
    let mut callable_entry_fn_ids = HashMap::new();
    for (&body_sid, entry) in &surface.callable_entries {
        let arg_count = surface.param_reprs[body_sid as usize]
            .len()
            .saturating_sub(entry.capture_count);
        let sig = build_callable_entry_signature(arg_count);
        let name = format!("fz_callable_entry_{}_s{}", surface.body_fn_id(body_sid).0, body_sid);
        let func_id = m
            .declare_function(&name, Linkage::Local, &sig)
            .map_err(|e| CodegenError::new(format!("declare {name}: {e}")))?;
        callable_entry_fn_ids.insert(body_sid, func_id);
    }
    Ok(callable_entry_fn_ids)
}

#[derive(Default)]
pub(super) struct BoundaryReturnAdapters {
    ids: HashMap<(ArgRepr, ArgRepr), FuncId>,
}

impl BoundaryReturnAdapters {
    pub(super) fn id_for(&self, source: ArgRepr, dest: ArgRepr) -> Option<FuncId> {
        (source != dest)
            .then(|| self.ids.get(&(source, dest)).copied())
            .flatten()
    }

    fn insert(&mut self, source: ArgRepr, dest: ArgRepr, func_id: FuncId) {
        let previous = self.ids.insert((source, dest), func_id);
        debug_assert!(
            previous.is_none(),
            "duplicate boundary return adapter for {source:?} -> {dest:?}"
        );
    }

    fn entries(&self) -> impl Iterator<Item = ((ArgRepr, ArgRepr), FuncId)> + '_ {
        self.ids
            .iter()
            .map(|(&(source, dest), &func_id)| ((source, dest), func_id))
    }
}

fn build_boundary_return_adapter_signature(source: ArgRepr) -> Signature {
    let mut sig = Signature::new(CallConv::Tail);
    push_repr_param(&mut sig, source);
    sig.params.push(AbiParam::new(types::I64)); // self
    sig.returns.push(AbiParam::new(types::I64));
    sig
}

fn delivered_shape(surface: &NativeCodegenSurface<'_>, body_sid: u32, is_cont_fn: bool) -> DeliveredShape {
    let body = surface.body(body_sid).native_body;
    NativeDemandAbi::new(body).returned_shape(is_cont_fn)
}

fn collect_boundary_return_adapter_pairs(surface: &NativeCodegenSurface<'_>) -> BTreeSet<(ArgRepr, ArgRepr)> {
    let mut pairs = BTreeSet::new();
    for &body_sid in surface.callable_entries.keys() {
        let source = surface.return_reprs[body_sid as usize];
        if source != ArgRepr::ValueRef {
            pairs.insert((source, ArgRepr::ValueRef));
        }
    }
    for body_slot in &surface.body_slots {
        let Some(body_slot) = body_slot.as_ref() else {
            continue;
        };
        let caller_sid = body_slot.codegen_id;
        let caller_is_cont = surface.cont_fns.contains(&body_slot.fn_id);
        let caller_shape = delivered_shape(surface, caller_sid, caller_is_cont);
        for block in &body_slot.body.blocks {
            let Term::TailCall {
                callee: DirectCallTarget::Local(callee),
                ..
            } = &block.terminator
            else {
                continue;
            };
            if !surface.native_abi_fns.contains(callee) {
                continue;
            }
            let Some(callee_sid) = surface.body_id_for_fn(*callee) else {
                continue;
            };
            let callee_is_cont = surface.cont_fns.contains(callee);
            let callee_shape = delivered_shape(surface, callee_sid, callee_is_cont);
            if let (DeliveredShape::Value(callee_repr), DeliveredShape::Value(caller_repr)) =
                (&callee_shape, &caller_shape)
                && callee_repr != caller_repr
            {
                pairs.insert((*callee_repr, *caller_repr));
            }
        }
    }
    pairs
}

fn declare_boundary_return_adapters<M: cranelift_module::Module>(
    m: &mut M,
    surface: &NativeCodegenSurface<'_>,
) -> Result<BoundaryReturnAdapters, CodegenError> {
    let mut adapters = BoundaryReturnAdapters::default();
    for (source, dest) in collect_boundary_return_adapter_pairs(surface) {
        let func_id = declare_boundary_return_adapter(m, source, dest)?;
        adapters.insert(source, dest, func_id);
    }
    Ok(adapters)
}

fn declare_boundary_return_adapter<M: cranelift_module::Module>(
    m: &mut M,
    source: ArgRepr,
    dest: ArgRepr,
) -> Result<FuncId, CodegenError> {
    let sig = build_boundary_return_adapter_signature(source);
    let name = format!("fz_boundary_return_{}_to_{}", source.as_str(), dest.as_str());
    m.declare_function(&name, Linkage::Local, &sig)
        .map_err(|e| CodegenError::new(format!("declare {name}: {e}")))
}

fn emit_boundary_return_adapter_bodies<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    runtime: &RuntimeRefs,
    adapters: &BoundaryReturnAdapters,
) -> Result<(), CodegenError> {
    for ((source, dest), adapter_id) in adapters.entries() {
        let sig = build_boundary_return_adapter_signature(source);
        let name = format!("boundary_return_{}_to_{}", source.as_str(), dest.as_str());
        emit_fn_body(m, fbctx, sig, adapter_id, |m, b| {
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);
            let params = b.block_params(entry).to_vec();
            let source_value = params[0];
            let self_value = params[1];
            let mut shim_cache = CodegenCache::default();
            let mut cg = CodegenFn::for_runtime_shim(runtime, b, m, &mut shim_cache);
            let binding = match source {
                ArgRepr::ValueRef => CodegenValue::AnyRef(source_value),
                ArgRepr::RawInt | ArgRepr::RawF64 | ArgRepr::RawAtom => {
                    CodegenValue::from_abi_value(source_value, source)
                }
                ArgRepr::Condition => unreachable!("condition is never a boundary return ABI"),
            };
            let outer_cont = cg.closure_capture_ref_at(self_value, 0);
            let code = cg.closure_code_ref(outer_cont);
            let mut cont_sig = Signature::new(CallConv::Tail);
            push_repr_param(&mut cont_sig, dest);
            cont_sig.params.push(AbiParam::new(types::I64));
            cont_sig.returns.push(AbiParam::new(types::I64));
            let sig_ref = cg.b.func.import_signature(cont_sig);
            let mut cont_args = Vec::with_capacity(2);
            cg.push_binding_as_abi_arg(&mut cont_args, binding, dest);
            cont_args.push(outer_cont);
            cg.b.ins().return_call_indirect(sig_ref, code, &cont_args);
        })
        .map_err(|e| CodegenError::new(format!("define {name}: {e}")))?;
    }
    Ok(())
}

fn emit_callable_entry_bodies<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    runtime: &RuntimeRefs,
    fn_ids: &HashMap<u32, FuncId>,
    callable_entry_fn_ids: &HashMap<u32, FuncId>,
    return_adapters: &BoundaryReturnAdapters,
    surface: &NativeCodegenSurface<'_>,
    tel: &dyn Telemetry,
    module_path: &str,
) -> Result<(), CodegenError> {
    for (&body_sid, entry) in &surface.callable_entries {
        let body_func_id = *fn_ids
            .get(&body_sid)
            .ok_or_else(|| CodegenError::new(format!("missing direct body FuncId for spec {body_sid}")))?;
        let callable_entry_id = *callable_entry_fn_ids
            .get(&body_sid)
            .ok_or_else(|| CodegenError::new(format!("missing callable-entry FuncId for spec {body_sid}")))?;
        let reprs = &surface.param_reprs[body_sid as usize];
        let arg_reprs = &reprs[entry.capture_count..];
        let return_repr = surface.return_reprs[body_sid as usize];
        let return_adapter_id = if return_repr == ArgRepr::ValueRef {
            None
        } else {
            Some(return_adapters.id_for(return_repr, ArgRepr::ValueRef).ok_or_else(|| {
                CodegenError::new(format!(
                    "missing callable return adapter for spec {body_sid} return {}",
                    return_repr.as_str()
                ))
            })?)
        };
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
                module_path: module_path,
                fn_name: entry_name.as_str(),
                body_fn_id: surface.body_fn_id(body_sid).0 as u64,
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
            let target_cont = if let Some(adapter_id) = return_adapter_id {
                let adapter_addr = cg.func_addr(adapter_id);
                let adapter_schema = cg.b.ins().iconst(types::I32, 0);
                let captured_count = cg.b.ins().iconst(types::I32, 1);
                let halt_kind = cg.b.ins().iconst(types::I32, 0);
                let adapter_cont = cg.alloc_closure(adapter_schema, captured_count, halt_kind, adapter_addr);
                let outer_cont = cg.materialize_cont(cont_value);
                cg.store_closure_capture_ref_word(adapter_cont, 0, outer_cont);
                adapter_cont
            } else {
                cont_value
            };
            direct_args.push(self_value);
            direct_args.push(target_cont);
            cg.b.ins().return_call(body_fref, &direct_args);
        })
        .map_err(|e| CodegenError::new(format!("define {entry_name}: {e}")))?;
    }
    Ok(())
}

fn emit_codegen_abi_contracts(surface: &NativeCodegenSurface<'_>, tel: &dyn Telemetry) {
    for body_slot in &surface.body_slots {
        let Some(body_slot) = body_slot.as_ref() else {
            continue;
        };
        let sid = body_slot.codegen_id as usize;
        let f = &surface.module.fns[body_slot.fn_idx];
        tel.execute(
            &["fz", "codegen", "abi_contract"],
            &crate::measurements! {
                spec_id: sid as u64,
                fn_id: f.id.0 as u64,
                param_count: surface.param_reprs[sid].len() as u64,
                capture_count: surface.closure_capture_counts.get(&f.id).copied().unwrap_or(0) as u64,
            },
            &crate::metadata! {
                module_path: surface.module.module_path(),
                fn_name: f.name.as_str(),
                body_origin: crate::telemetry::opaque_debug(&body_slot.native_body.origin),
                entry_abi: crate::telemetry::opaque_debug(&body_slot.native_body.entry_abi),
                param_reprs: crate::telemetry::opaque_debug(&surface.param_reprs[sid]),
                return_repr: surface.return_reprs[sid].as_str(),
                is_native: surface.native_abi_fns.contains(&f.id),
                is_cont_fn: surface.cont_fns.contains(&f.id),
                is_closure_target: surface.closure_capture_counts.contains_key(&f.id),
            },
        );
    }
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
        // Select halt_cont_body_addr by kind. Branchless via four
        // func_addrs + a tiny dispatch — keeps the thunk a leaf.
        let a_strict = cg.func_addr(runtime.halt_cont_body_strict_id);
        let a_i64 = cg.func_addr(runtime.halt_cont_body_i64_id);
        let a_f64 = cg.func_addr(runtime.halt_cont_body_f64_id);
        let a_atom = cg.func_addr(runtime.halt_cont_body_atom_id);
        let one = cg.b.ins().iconst(types::I32, 1);
        let two = cg.b.ins().iconst(types::I32, 2);
        let three = cg.b.ins().iconst(types::I32, 3);
        let is_i64 = cg.b.ins().icmp(IntCC::Equal, kind, one);
        let is_f64 = cg.b.ins().icmp(IntCC::Equal, kind, two);
        let is_atom = cg.b.ins().icmp(IntCC::Equal, kind, three);
        let pick_i64_or_tagged = cg.b.ins().select(is_i64, a_i64, a_strict);
        let pick_f64 = cg.b.ins().select(is_f64, a_f64, pick_i64_or_tagged);
        let hcb_addr = cg.b.ins().select(is_atom, a_atom, pick_f64);
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

/// Emit four fz_halt_cont_body fns, one per repr. Generic ValueRef
/// bodies receive `(value_ref, self)`; RawInt / RawF64 / RawAtom variants stay
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
        (
            runtime.halt_cont_body_atom_id,
            types::I64,
            runtime.halt_implicit_atom_id,
        ),
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
    body_slots: &[Option<NativeCodegenBody<'_>>],
    fn_sigs: &[Signature],
) -> Result<HashMap<u32, FuncId>, CodegenError> {
    let mut fn_ids: HashMap<u32, FuncId> = HashMap::new();
    for (sid, body_slot) in body_slots.iter().enumerate() {
        if body_slot.is_none() {
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

/// Pre-pass over Term::ReceiveMatched sites: one receive-dispatch FuncId per
/// site, keyed by `(fn_id.0, block_id.0)`. Declared up front so the
/// park-site terminator arm can take a `func_addr` of an as-yet-unemitted
/// symbol; the body is emitted in a post-fn-loop pass.
type ReceiveDispatchFnIds = HashMap<(u32, u32), FuncId>;
type ReceiveMatchedSites = Vec<(FnId, BlockId)>;
type MidFlightContFnIds = HashMap<(u32, Vec<MidFlightArgShape>), FuncId>;

fn declare_receive_dispatch_fns<M: cranelift_module::Module>(
    m: &mut M,
    module: &Module,
    tel: &dyn Telemetry,
) -> Result<(ReceiveDispatchFnIds, ReceiveMatchedSites), CodegenError> {
    let mut dispatch_fn_ids: HashMap<(u32, u32), FuncId> = HashMap::new();
    let mut receive_matched_sites: Vec<(FnId, BlockId)> = Vec::new();
    for f in &module.fns {
        for blk in &f.blocks {
            let Term::ReceiveMatched {
                clauses,
                dispatch,
                after,
                pinned,
                captures,
                ..
            } = &blk.terminator
            else {
                continue;
            };
            let name = format!("fz_receive_dispatch_fn_{}_b{}", f.id.0, blk.id.0);
            let m_id = declare_receive_dispatch(m, &name)?;
            dispatch_fn_ids.insert((f.id.0, blk.id.0), m_id);
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
                    dispatch_input_count: dispatch.input_count as u64,
                    dispatch_prepared_key_count: dispatch.prepared_keys.len() as u64,
                    dispatch_node_count: dispatch.graph.nodes.len() as u64,
                },
                &crate::metadata! {
                    module_path: module.module_path(),
                    fn_name: f.name.as_str(),
                    dispatch: opaque(dispatch),
                },
            );
        }
    }
    Ok((dispatch_fn_ids, receive_matched_sites))
}

/// Emit receive-dispatch fn bodies for every Term::ReceiveMatched site
/// discovered in the pre-pass above. Dispatch fns were declared before the
/// fn-compilation loop so the park-site terminator arm could take
/// `func_addr` of the still-undefined symbols. Bodies are pure leaf fns
/// (no allocation, no extern).
#[allow(clippy::too_many_arguments)]
fn emit_receive_dispatch_bodies<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    module: &Module,
    runtime: &RuntimeRefs,
    tuple_schema_ids: &HashMap<usize, u32>,
    named_schema_ids: &HashMap<String, u32>,
    dispatch_fn_ids: &HashMap<(u32, u32), FuncId>,
    receive_matched_sites: &[(FnId, BlockId)],
    tel: &dyn Telemetry,
) -> Result<(), CodegenError> {
    for (fn_id, blk_id) in receive_matched_sites {
        let f = module.fn_by_id(*fn_id);
        let blk = f.blocks.iter().find(|b| b.id == *blk_id).unwrap();
        let Term::ReceiveMatched {
            clauses,
            pinned,
            dispatch,
            ..
        } = &blk.terminator
        else {
            unreachable!("receive_matched_sites holds only Term::ReceiveMatched terms");
        };
        let m_id = dispatch_fn_ids[&(fn_id.0, blk_id.0)];
        let display_name = format!("fz_receive_dispatch_fn_{}_b{}", fn_id.0, blk_id.0);
        let (block_count, instruction_count) = {
            let _span = tel.span(
                &["fz", "codegen", "lower_function"],
                crate::metadata! {
                    body_kind: "receive_dispatch",
                    module_path: module.module_path(),
                    fn_name: display_name.as_str(),
                    fn_id: fn_id.0 as u64,
                    block_id: blk_id.0 as u64,
                },
            );
            emit_receive_dispatch_body(
                m,
                fbctx,
                m_id,
                module,
                tuple_schema_ids,
                named_schema_ids,
                pinned.as_slice(),
                clauses.as_slice(),
                dispatch,
                &DispatchRuntimeHelpers {
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
                dispatch_input_count: dispatch.input_count as u64,
                dispatch_prepared_key_count: dispatch.prepared_keys.len() as u64,
                dispatch_node_count: dispatch.graph.nodes.len() as u64,
            },
            &crate::metadata! {
                body_kind: "receive_dispatch",
                module_path: module.module_path(),
                fn_name: display_name,
                dispatch: opaque(dispatch),
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
/// native callee. The native codegen surface precomputes the unique
/// `(callee_sid, arg_shapes)` keys; compiler2 native codegen only declares the
/// actual functions.
fn declare_mid_flight_conts<M: cranelift_module::Module>(
    m: &mut M,
    surface: &NativeCodegenSurface<'_>,
) -> Result<(MidFlightContFnIds, MidFlightContFnIds), CodegenError> {
    let mut mid_flight_cont_fn_ids: HashMap<(u32, Vec<MidFlightArgShape>), FuncId> = HashMap::new();
    let mut mid_flight_cont_tail_fn_ids: HashMap<(u32, Vec<MidFlightArgShape>), FuncId> = HashMap::new();
    for key in &surface.mid_flight_cont_keys {
        let callee_sid = key.0;
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
        mid_flight_cont_tail_fn_ids.insert(key.clone(), cont_tail_id);
    }
    Ok((mid_flight_cont_fn_ids, mid_flight_cont_tail_fn_ids))
}

pub(crate) fn compile_with_backend_native_program<
    B: Backend,
    T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes + VisibilityTypes,
>(
    t: &mut T,
    program: &crate::compiler2::NativeProgram,
    backend: B,
    tel: &dyn Telemetry,
) -> Result<B::Output, CodegenError> {
    let surface = prepare_native_codegen_surface_from_native_program(t, program);
    compile_with_backend_surface(t, &surface, backend, tel)
}

fn build_codegen_return_repr(body: &crate::compiler2::NativeBody) -> ArgRepr {
    match &body.return_abi {
        crate::compiler2::ReturnAbi::Value(repr) => arg_repr_from_compiler2(*repr),
        crate::compiler2::ReturnAbi::TupleFields(_) => ArgRepr::ValueRef,
    }
}

fn build_codegen_callable_entries<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    program: &crate::compiler2::NativeProgram,
) -> BTreeMap<u32, NativeCallableEntrySurface> {
    let mut entries = BTreeMap::new();
    for entry in &program.callable_boundaries {
        let codegen_id = entry.target_fn.0;
        let capture_tys = entry
            .target
            .activation
            .input
            .iter()
            .copied()
            .take(entry.capture_count)
            .map(|ty| {
                let erased = t.erase_closure_identity(&ty);
                t.alpha_normalize_vars(&erased)
            })
            .collect::<Vec<_>>();
        let capture_key = crate::types::key_slots_from_tys(capture_tys);
        let next = NativeCallableEntrySurface {
            target_fn: entry.target_fn,
            capture_count: entry.capture_count,
            capture_key,
        };
        if let Some(previous) = entries.insert(codegen_id, next.clone()) {
            debug_assert_eq!(previous, next);
        }
    }
    entries
}

fn build_codegen_closure_capture_counts(program: &crate::compiler2::NativeProgram) -> HashMap<FnId, usize> {
    let mut counts = HashMap::new();
    for entry in &program.callable_boundaries {
        counts.insert(entry.target_fn, entry.capture_count);
    }
    counts
}

fn collect_codegen_mid_flight_cont_keys(
    program: &crate::compiler2::NativeProgram,
    param_reprs: &[Vec<ArgRepr>],
    closure_capture_counts: &HashMap<FnId, usize>,
) -> Vec<(u32, Vec<MidFlightArgShape>)> {
    let mut keys = HashSet::new();
    for function in &program.module.fns {
        for block in &function.blocks {
            let Term::TailCall {
                callee,
                args,
                is_back_edge: true,
                ..
            } = &block.terminator
            else {
                continue;
            };
            let Some(callee) = callee.local_fn_id() else {
                continue;
            };
            let callee_sid = callee.0;
            let Some(callee_reprs) = param_reprs.get(callee_sid as usize) else {
                continue;
            };
            let mut arg_shapes = callee_reprs
                .iter()
                .take(args.len())
                .copied()
                .map(MidFlightArgShape::Value)
                .collect::<Vec<_>>();
            if closure_capture_counts.contains_key(&callee) {
                arg_shapes.push(MidFlightArgShape::HeapRef);
            }
            arg_shapes.push(MidFlightArgShape::HeapRef);
            keys.insert((callee_sid, arg_shapes));
        }
    }
    let mut out = keys.into_iter().collect::<Vec<_>>();
    out.sort_by(|left, right| left.0.cmp(&right.0).then(left.1.len().cmp(&right.1.len())));
    out
}

fn prepare_native_codegen_surface_from_native_program<'a>(
    t: &mut impl ClosureTypes<Ty = Ty>,
    program: &'a crate::compiler2::NativeProgram,
) -> NativeCodegenSurface<'a> {
    let max_fn_id = program
        .module
        .fns
        .iter()
        .map(|function| function.id.0 as usize)
        .max()
        .unwrap_or(0);
    let mut body_slots = (0..=max_fn_id).map(|_| None).collect::<Vec<_>>();
    let mut param_reprs = Vec::with_capacity(max_fn_id + 1);
    let mut return_reprs = Vec::with_capacity(max_fn_id + 1);
    param_reprs.resize(max_fn_id + 1, Vec::new());
    return_reprs.resize(max_fn_id + 1, ArgRepr::ValueRef);

    for body in &program.bodies {
        let codegen_id = body.fn_id.0 as usize;
        let function = program.module.fn_by_id(body.fn_id);
        let fn_idx = *program
            .module
            .fn_idx
            .get(&body.fn_id)
            .expect("Compiler2 native body must exist in the native module");
        body_slots[codegen_id] = Some(NativeCodegenBody {
            codegen_id: body.fn_id.0,
            fn_idx,
            fn_id: body.fn_id,
            native_body: body,
            body: function,
            display_name: function.name.clone(),
        });
        param_reprs[codegen_id] = body.param_reprs.iter().copied().map(arg_repr_from_compiler2).collect();
        return_reprs[codegen_id] = build_codegen_return_repr(body);
    }

    let closure_capture_counts = build_codegen_closure_capture_counts(program);
    let native_abi_fns = program
        .module
        .fns
        .iter()
        .map(|function| function.id)
        .collect::<HashSet<_>>();
    let cont_fns = program
        .bodies
        .iter()
        .filter_map(|body| match body.entry_abi {
            crate::compiler2::NativeEntryAbi::Continuation { .. } => Some(body.fn_id),
            crate::compiler2::NativeEntryAbi::Direct => None,
        })
        .collect::<HashSet<_>>();
    let cont_target_fns = native_abi_fns.clone();
    let fn_halt_kinds = program
        .bodies
        .iter()
        .map(|body| (body.fn_id.0, build_codegen_return_repr(body).halt_kind()))
        .collect();

    NativeCodegenSurface {
        module: &program.module,
        diagnostics: Diagnostics::new(),
        main_fn_id: Some(program.entry),
        spec_count: program.bodies.len(),
        body_slots,
        callable_entries: build_codegen_callable_entries(t, program),
        mid_flight_cont_keys: collect_codegen_mid_flight_cont_keys(program, &param_reprs, &closure_capture_counts),
        param_reprs,
        return_reprs,
        native_abi_fns,
        cont_target_fns,
        cont_fns,
        closure_capture_counts,
        fn_halt_kinds,
    }
}

pub(crate) fn compile_with_backend_surface<
    B: Backend,
    T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes + VisibilityTypes,
>(
    t: &mut T,
    surface: &NativeCodegenSurface<'_>,
    mut backend: B,
    tel: &dyn Telemetry,
) -> Result<B::Output, CodegenError> {
    // Enclosing span: the denominator that makes codegen wall time account as
    // compile = declare + per-spec(lower + define) + emit_runtime + finalize.
    // Parent linkage is threaded by the bus from the open-span stack, so every
    // phase span below nests under this one automatically.
    let _compile_span = tel.span(
        &["fz", "codegen", "compile"],
        crate::metadata! {
            module_path: surface.module.module_path(),
            backend: backend.kind(),
            spec_count: surface.spec_count as u64,
        },
    );
    let declare_span = tel.span(
        &["fz", "codegen", "declare"],
        crate::metadata! { module_path: surface.module.module_path() },
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
        collect_tuple_arities_and_register_schemas(surface.module, &user_schemas);
    let named_schema_ids = {
        let mut ids = HashMap::new();
        let mut reg = user_schemas.borrow_mut();
        for (name, fields) in &surface.module.struct_schemas {
            let id = reg.register(Schema::named_struct(name.clone(), fields.clone()));
            ids.insert(name.clone(), id);
        }
        ids
    };

    let module = surface.module;
    let body_slots = &surface.body_slots;

    let schemas = build_per_spec_schemas(t, body_slots);
    let frame_sizes: Vec<u32> = schemas.iter().map(|s| s.allocation_payload_size() as u32).collect();

    emit_codegen_abi_contracts(surface, tel);

    let fn_sigs = build_fn_sigs(module, surface);

    let linkage = backend.fn_linkage();
    let fn_ids = declare_spec_fns(backend.module_mut(), linkage, body_slots, &fn_sigs)?;
    let callable_entry_fn_ids = declare_callable_entry_fns(backend.module_mut(), surface)?;
    let boundary_return_adapters = declare_boundary_return_adapters(backend.module_mut(), surface)?;

    let (mid_flight_cont_fn_ids, mid_flight_cont_tail_fn_ids) =
        declare_mid_flight_conts(backend.module_mut(), surface)?;

    let bs_const_data: RefCell<HashMap<Vec<u8>, BsConstSyms>> = RefCell::new(HashMap::new());
    let (receive_dispatch_fn_ids, receive_matched_sites) =
        declare_receive_dispatch_fns(backend.module_mut(), module, tel)?;
    let verifier_isa = host_isa();
    drop(declare_span);

    for body_slot in body_slots {
        let Some(body_slot) = body_slot.as_ref() else {
            continue;
        };
        let sid = body_slot.codegen_id;
        let func_id = *fn_ids.get(&sid).unwrap();
        let mut ctx = backend.module_mut().make_context();
        ctx.func.signature = fn_sigs[sid as usize].clone();

        let f = body_slot.body;
        debug_assert_eq!(body_slot.fn_id, f.id);

        let display_name = &body_slot.display_name;
        let cg_env = CodegenEnv {
            telemetry: tel,
            runtime: &runtime,
            surface,
            module,
            active_spec_id: sid,
            active_body_fn_id: body_slot.fn_id,
            active_body_name: display_name,
            fn_ids: &fn_ids,
            callable_entry_fn_ids: &callable_entry_fn_ids,
            boundary_return_adapters: &boundary_return_adapters,
            mid_flight_cont_tail_fn_ids: &mid_flight_cont_tail_fn_ids,
            tuple_schema_ids: &tuple_schema_ids,
            named_schema_ids: &named_schema_ids,
            bs_const_data: &bs_const_data,
            param_reprs: &surface.param_reprs,
            return_reprs: &surface.return_reprs,
            native_abi_fns: &surface.native_abi_fns,
            cont_target_fns: &surface.cont_target_fns,
            cont_fns: &surface.cont_fns,
            closure_capture_counts: &surface.closure_capture_counts,
            receive_dispatch_fn_ids: &receive_dispatch_fn_ids,
        };
        let cranelift_instruction_count;
        {
            let _span = tel.span(
                &["fz", "codegen", "lower_function"],
                crate::metadata! {
                    body_kind: "fz_spec",
                    module_path: module.module_path(),
                    fn_name: display_name.as_str(),
                    fn_id: body_slot.fn_id.0 as u64,
                    spec_id: sid as u64,
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
                sid,
                &module.source,
            )?;
            let (block_count, instruction_count) = cranelift_body_stats(&ctx.func);
            cranelift_instruction_count = instruction_count;
            tel.execute(
                &["fz", "codegen", "function_lowered"],
                &crate::measurements! {
                    fn_id: body_slot.fn_id.0 as u64,
                    spec_id: sid as u64,
                    block_count: block_count as u64,
                    instruction_count: instruction_count as u64,
                    fz_block_count: f.blocks.len() as u64,
                },
                &crate::metadata! {
                    body_kind: "fz_spec",
                    module_path: module.module_path(),
                    fn_name: display_name.as_str(),
                },
            );
        }
        let fn_span = module.source.fn_span_of(f.id);
        // The native-compile step: verify the lowered Cranelift IR, then hand it
        // to the backend to produce machine code. This is the dominant per-spec
        // cost and was previously the unattributed gap between `lower_function`
        // spans; its stop payload carries the emitted code size.
        let define_span = tel.span(
            &["fz", "codegen", "define_function"],
            crate::metadata! {
                body_kind: "fz_spec",
                module_path: module.module_path(),
                fn_name: display_name.as_str(),
                fn_id: body_slot.fn_id.0 as u64,
                spec_id: sid as u64,
            },
        );
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
        let code_bytes = ctx.compiled_code().map(|cc| cc.code_buffer().len() as u64).unwrap_or(0);
        define_span.stop_with(
            &crate::measurements! {
                fn_id: body_slot.fn_id.0 as u64,
                spec_id: sid as u64,
                instruction_count: cranelift_instruction_count as u64,
                code_bytes: code_bytes,
            },
            &crate::metadata! {
                body_kind: "fz_spec",
                module_path: module.module_path(),
                fn_name: display_name.as_str(),
            },
        );
        backend.module_mut().clear_context(&mut ctx);
    }

    let emit_runtime_span = tel.span(
        &["fz", "codegen", "emit_runtime"],
        crate::metadata! { module_path: module.module_path() },
    );
    emit_receive_dispatch_bodies(
        backend.module_mut(),
        &mut fbctx,
        module,
        &runtime,
        &tuple_schema_ids,
        &named_schema_ids,
        &receive_dispatch_fn_ids,
        &receive_matched_sites,
        tel,
    )?;

    let static_closure_targets = collect_static_closure_targets(surface, &fn_ids, &callable_entry_fn_ids);

    emit_mid_flight_cont_bodies(
        backend.module_mut(),
        &mut fbctx,
        &runtime,
        &fn_ids,
        &mid_flight_cont_fn_ids,
        &mid_flight_cont_tail_fn_ids,
    )?;
    emit_boundary_return_adapter_bodies(backend.module_mut(), &mut fbctx, &runtime, &boundary_return_adapters)?;
    emit_callable_entry_bodies(
        backend.module_mut(),
        &mut fbctx,
        &runtime,
        &fn_ids,
        &callable_entry_fn_ids,
        &boundary_return_adapters,
        surface,
        tel,
        module.module_path(),
    )?;
    let resume_id = emit_resume(backend.module_mut(), &mut fbctx, &runtime)?;
    drop(emit_runtime_span);

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
        diagnostics: surface.diagnostics.clone(),
        main_fn_id: surface.main_fn_id,
        static_closure_targets,
        entry_thunk_id: runtime.entry_thunk_id,
        main_trampoline_id: runtime.main_trampoline_id,
        drain_dtor_entry_id: runtime.drain_dtor_entry_id,
        halt_cont_body_ids: [
            runtime.halt_cont_body_strict_id,
            runtime.halt_cont_body_i64_id,
            runtime.halt_cont_body_f64_id,
            runtime.halt_cont_body_atom_id,
        ],
        fn_halt_kinds: surface.fn_halt_kinds.clone(),
        resume_id,
    };

    let finalize_span = tel.span(
        &["fz", "codegen", "finalize"],
        crate::metadata! { module_path: module.module_path() },
    );
    backend.emit_metadata_carriers(&mut fbctx, &metadata)?;
    let output = backend.finalize(metadata)?;
    drop(finalize_span);
    Ok(output)
}
