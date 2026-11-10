use super::receive::{declare_receive_dispatch, emit_receive_dispatch_body};
use super::*;
use crate::diag::Diagnostics;
use crate::fz_ir::{BlockId, FnId, Module, Prim, Term};
use crate::telemetry::{RawSpanStop1 as _, RawSpanTelemetry, TelemetryExt as _};
use crate::types::{ClosureTypes, LiteralTypes, RenderTypes, Types};
use cranelift_codegen::ir::{self, AbiParam, InstBuilder, Signature, condcodes::IntCC, types};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::FunctionBuilderContext;
use cranelift_module::{DataId, FuncId, Linkage, Module as ClModule};
use fz_runtime::any_value::ValueKind;
use fz_runtime::heap::{FieldKind, Schema, SchemaRegistry};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

/// Walk every fn body collecting tuple arities used by MakeTuple /
/// RuntimeTypeTest facts, then registering a deterministic-id Schema per arity
/// in `user_schemas`.
///
/// Returns `(tuple_arities, tuple_schema_ids)`. BTreeSet iteration keeps
/// assignment order deterministic so the AOT runtime's ids match what codegen
/// baked in. The bitstring reader's arity-1 and arity-3 tuples are already the
/// registry's first two schemas, so they are listed here only when a program
/// uses those arities itself.
fn collect_tuple_arities_and_register_schemas(
    module: &Module,
    user_schemas: &RefCell<SchemaRegistry>,
) -> (BTreeSet<usize>, HashMap<usize, u32>) {
    let mut tuple_arities: BTreeSet<usize> = BTreeSet::new();
    for f in &module.fns {
        for blk in &f.blocks {
            for stmt in &blk.stmts {
                match stmt.prim() {
                    Prim::MakeTuple(args) => {
                        tuple_arities.insert(args.len());
                    }
                    Prim::RuntimeTypeTest(_, descr) => {
                        tuple_arities.extend(descr.tuple_arities_at_every_depth());
                    }
                    _ => {}
                }
            }
        }
    }
    let mut tuple_schema_ids: HashMap<usize, u32> = HashMap::new();
    {
        let mut reg = user_schemas.borrow_mut();
        for &arity in &tuple_arities {
            let id = reg.register(Schema::tuple_of_arity(arity));
            tuple_schema_ids.insert(arity, id);
        }
    }
    (tuple_arities, tuple_schema_ids)
}

/// Build per-body frame schemas, refining entry-param kinds from each body's
/// settled `NativeBody.value_types`. The dense body id for FnId K lands at
/// index K (invariant) so any code path that uses fn_id.0 as a schema_id
/// continues to hit the right schema. Sentinel slots get a zero-field
/// placeholder schema; they're never reached at runtime.
fn build_per_spec_schemas(body_slots: &[Option<NativeCodegenBody<'_>>]) -> Vec<Schema> {
    let mut schemas: Vec<Schema> = Vec::with_capacity(body_slots.len());
    for body_slot in body_slots {
        let Some(body_slot) = body_slot.as_ref() else {
            schemas.push(build_frame_schema("__sentinel", &[]));
            continue;
        };
        let f = body_slot.body;
        let entry_block = f.block(f.entry);
        let mut kinds: Vec<FieldKind> = entry_block.params.iter().map(|_| FieldKind::AnyValue).collect();
        for (j, repr) in body_slot.native_body.param_reprs.iter().copied().enumerate() {
            match arg_repr_from_compiler2(repr) {
                ArgRepr::RawF64 => kinds[j] = FieldKind::RawF64,
                ArgRepr::RawInt => kinds[j] = FieldKind::RawI64,
                _ => {}
            }
        }
        schemas.push(build_frame_schema(&f.name, &kinds));
    }
    schemas
}

/// Per-spec Cranelift Signature. A native fn gets its typed args plus the
/// continuation, in `Tail`; a uniform fn gets the trampoline's
/// `(frame_ptr, host_ctx) -> i64` in the target's C convention. A sentinel slot
/// is never declared, so its signature is only a placeholder.
fn build_fn_sigs<M: cranelift_module::Module>(
    m: &mut M,
    module: &Module,
    surface: &NativeCodegenSurface<'_>,
) -> Vec<Signature> {
    surface
        .body_slots
        .iter()
        .map(|body_slot| match body_slot {
            Some(body_slot) => {
                let f = &module.fns[body_slot.fn_idx];
                let is_native = surface.native_abi_fns.contains(&f.id);
                build_fn_signature(
                    m,
                    &surface.param_reprs[body_slot.codegen_id as usize],
                    is_native,
                    surface.cont_fns.contains(&f.id),
                    Some(continuation_entry_extra_count(body_slot.native_body)),
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

/// Define one read-only static closure per zero-capture callable boundary,
/// keyed by boundary id. The code pointer is the boundary's own function
/// (closure-target sig `(args, self, cont) tail`), not a C-convention stub. The
/// object acts both as `self` for direct callers (zero-cap bodies ignore self)
/// and as the value a thin function reference evaluates to.
///
/// The header carries the boundary's halt kind, so a task launched from the
/// closure picks the matching halt continuation, and its `arity`, so a rendered
/// closure reports its own parameter count.
fn define_zero_capture_closures<M: cranelift_module::Module>(
    m: &mut M,
    surface: &NativeCodegenSurface<'_>,
    callable_boundary_fn_ids: &HashMap<u32, FuncId>,
) -> Result<HashMap<u32, DataId>, CodegenError> {
    let mut data_ids = HashMap::new();
    for (&boundary_id, boundary) in surface
        .callable_boundaries
        .iter()
        .filter(|(_, boundary)| boundary.capture_count == 0)
    {
        let body_fid = *callable_boundary_fn_ids
            .get(&boundary_id)
            .expect("zero-cap closure boundary must have a callable-boundary FuncId");
        let halt_kind = boundary.task_halt_repr.unwrap_or(ArgRepr::ValueRef).halt_kind();
        let arity = boundary.arg_reprs.len() as u32;
        let data_id = define_static_closure(
            m,
            &format!("fz_static_closure_{boundary_id}"),
            boundary.denotation,
            halt_kind,
            arity,
            body_fid,
        )?;
        data_ids.insert(boundary_id, data_id);
    }
    Ok(data_ids)
}

fn build_callable_boundary_signature(arg_count: usize) -> Signature {
    let mut sig = Signature::new(CallConv::Tail);
    for _ in 0..arg_count {
        sig.params.push(AbiParam::new(types::I64));
    }
    sig.params.push(AbiParam::new(types::I64)); // self
    sig.params.push(AbiParam::new(types::I64)); // cont
    sig.returns.push(AbiParam::new(types::I64));
    sig
}

fn declare_callable_boundary_fns<M: cranelift_module::Module>(
    m: &mut M,
    surface: &NativeCodegenSurface<'_>,
) -> Result<HashMap<u32, FuncId>, CodegenError> {
    let mut callable_boundary_fn_ids = HashMap::new();
    for (&boundary_id, boundary) in &surface.callable_boundaries {
        let arg_count = boundary.arg_reprs.len();
        let sig = build_callable_boundary_signature(arg_count);
        let name = format!("fz_callable_boundary_{}_b{}", boundary.target_fn.0, boundary_id);
        let func_id = m
            .declare_function(&name, Linkage::Local, &sig)
            .map_err(|e| CodegenError::new(format!("declare {name}: {e}")))?;
        callable_boundary_fn_ids.insert(boundary_id, func_id);
    }
    Ok(callable_boundary_fn_ids)
}

fn emit_callable_boundary_bodies<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    fn_ids: &HashMap<u32, FuncId>,
    callable_boundary_fn_ids: &HashMap<u32, FuncId>,
    surface: &NativeCodegenSurface<'_>,
) -> Result<(), CodegenError> {
    for (&boundary_id, boundary) in &surface.callable_boundaries {
        let body_sid = surface.body_id_for_fn(boundary.target_fn).ok_or_else(|| {
            CodegenError::new(format!("missing direct body id for callable boundary {}", boundary_id))
        })?;
        let body_func_id = *fn_ids
            .get(&body_sid)
            .ok_or_else(|| CodegenError::new(format!("missing direct body FuncId for spec {body_sid}")))?;
        let callable_boundary_id = *callable_boundary_fn_ids
            .get(&boundary_id)
            .ok_or_else(|| CodegenError::new(format!("missing callable-boundary FuncId for boundary {boundary_id}")))?;
        let arg_reprs = boundary.arg_reprs.as_slice();
        let sig = build_callable_boundary_signature(arg_reprs.len());
        let boundary_name = format!("callable_boundary_b{boundary_id}");
        emit_fn_body(m, fbctx, sig, callable_boundary_id, |m, b| {
            let entry_block = b.create_block();
            b.append_block_params_for_function_params(entry_block);
            b.switch_to_block(entry_block);
            b.seal_block(entry_block);
            let params = b.block_params(entry_block).to_vec();
            let self_value = params[arg_reprs.len()];
            let cont_value = params[arg_reprs.len() + 1];
            let mut shim_cache = CodegenCache::default();
            let mut cg = CodegenFn::new(b, m, &mut shim_cache);
            let body_fref = cg.func_ref(body_func_id);
            let mut direct_args: Vec<ir::Value> =
                Vec::with_capacity(boundary.capture_reprs.len() + arg_reprs.len() + 1);
            for (index, repr) in boundary.capture_reprs.iter().copied().enumerate() {
                let binding = cg.closure_capture_as_binding(self_value, index, repr);
                cg.push_binding_as_abi_arg(&mut direct_args, binding, repr);
            }
            for (idx, repr) in arg_reprs.iter().copied().enumerate() {
                let binding = CodegenValue::AnyRef(params[idx]);
                cg.push_binding_as_abi_arg(&mut direct_args, binding, repr);
            }
            direct_args.push(cont_value);
            cg.b.ins().return_call(body_fref, &direct_args);
        })
        .map_err(|e| CodegenError::new(format!("define {boundary_name}: {e}")))?;
    }
    Ok(())
}

/// The bodies codegen emits itself and then calls or takes the address of:
/// the four halt-cont bodies, the entry thunk, the main trampoline and the
/// dtor-drain entry. They are declared `Local` with written-out signatures
/// because they are not Rust functions — there is no item to read a signature
/// off, so their calling conventions are chosen here: `Tail` for the bodies fz
/// code enters, and the target's C convention for the entry the host calls by
/// address.
#[derive(Clone, Copy)]
pub(crate) struct LocalBodies {
    /// Halt-cont bodies, indexed by halt kind: ValueRef, RawInt, RawF64,
    /// RawAtom.
    pub(crate) halt_cont_body_ids: [FuncId; 4],
    /// The read-only halt continuation closures, indexed like
    /// `halt_cont_body_ids` and pointing at the bodies above.
    pub(crate) halt_cont_data_ids: [DataId; 4],
    pub(crate) entry_thunk_id: FuncId,
    pub(crate) main_trampoline_id: FuncId,
    pub(crate) drain_dtor_entry_id: FuncId,
}

impl LocalBodies {
    /// The body a return repr halts through. A halt kind indexes both the
    /// bodies and the continuation closures that point at them.
    pub(crate) fn halt_cont_body_id(&self, repr: ArgRepr) -> FuncId {
        self.halt_cont_body_ids[repr.halt_kind() as usize]
    }

    /// The program's one halt continuation closure for a return repr.
    pub(crate) fn halt_cont_data_id(&self, repr: ArgRepr) -> DataId {
        self.halt_cont_data_ids[repr.halt_kind() as usize]
    }
}

fn declare_local_bodies<M: cranelift_module::Module>(m: &mut M) -> Result<LocalBodies, CodegenError> {
    let drain_sig = drain_dtor_entry_signature(m);
    let mut declare = |name: &str, sig: Signature| -> Result<FuncId, CodegenError> {
        m.declare_function(name, Linkage::Local, &sig)
            .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))
    };
    // A halt-cont body takes `(value, self)`, with the value in the lane its
    // halt kind names, and is the definition emitted by `emit_halt_cont_bodies`.
    let halt_cont_sig = |repr: ArgRepr| {
        let mut sig = Signature::new(CallConv::Tail);
        push_repr_param(&mut sig, repr);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        sig
    };
    let strict_id = declare("fz_halt_cont_body_strict", halt_cont_sig(ArgRepr::ValueRef))?;
    let i64_id = declare("fz_halt_cont_body_i64", halt_cont_sig(ArgRepr::RawInt))?;
    let f64_id = declare("fz_halt_cont_body_f64", halt_cont_sig(ArgRepr::RawF64))?;
    let atom_id = declare("fz_halt_cont_body_atom", halt_cont_sig(ArgRepr::RawAtom))?;

    // The entry thunk is resumed like any continuation, so it has the
    // resume-shaped closure-target signature `(self) -> i64`.
    let mut entry_thunk_sig = Signature::new(CallConv::Tail);
    entry_thunk_sig.params.push(AbiParam::new(types::I64));
    entry_thunk_sig.returns.push(AbiParam::new(types::I64));
    let entry_thunk_id = declare("fz_entry_thunk", entry_thunk_sig)?;

    let mut main_trampoline_sig = Signature::new(CallConv::Tail);
    main_trampoline_sig.params.push(AbiParam::new(types::I64));
    main_trampoline_sig.params.push(AbiParam::new(types::I64));
    main_trampoline_sig.returns.push(AbiParam::new(types::I64));
    let main_trampoline_id = declare("fz_main_trampoline", main_trampoline_sig)?;

    // The scheduler calls the drain entry per pending dtor at task exit.
    let drain_dtor_entry_id = declare("fz_drain_dtor_entry", drain_sig)?;

    let halt_cont_body_ids = [strict_id, i64_id, f64_id, atom_id];
    let halt_cont_data_ids = define_halt_conts(m, halt_cont_body_ids)?;

    Ok(LocalBodies {
        halt_cont_body_ids,
        halt_cont_data_ids,
        entry_thunk_id,
        main_trampoline_id,
        drain_dtor_entry_id,
    })
}

/// Define the four halt continuation closures, one per halt kind. A
/// continuation is applied to exactly the one value it receives, so its arity
/// is 1.
fn define_halt_conts<M: cranelift_module::Module>(
    m: &mut M,
    halt_cont_body_ids: [FuncId; 4],
) -> Result<[DataId; 4], CodegenError> {
    const NAMES: [&str; 4] = [
        "fz_halt_cont_strict",
        "fz_halt_cont_i64",
        "fz_halt_cont_f64",
        "fz_halt_cont_atom",
    ];
    let mut data_ids = Vec::with_capacity(4);
    for (kind, body_id) in halt_cont_body_ids.into_iter().enumerate() {
        data_ids.push(define_static_closure(
            m,
            NAMES[kind],
            fz_runtime::any_value::ClosureDenotationId::INTERNAL,
            kind as u32,
            1,
            body_id,
        )?);
    }
    Ok(data_ids.try_into().expect("four halt kinds"))
}

/// Emit fz_main_trampoline. The closure-target body for a main-style
/// entry's synthetic inner closure. The inner closure carries the raw
/// `(cont)` main fn pointer in capture[0] (a raw int, so GC never treats it
/// as a heap reference). Closure-target sig `(self, cont) tail`: read main_fp
/// from capture[0] and `call_indirect Tail main_fp(cont)`, entering the uniform
/// entry-thunk + `fz_resume` dispatch path without forcing a closure-target
/// body onto the entry fn itself.
fn emit_main_trampoline<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    locals: &LocalBodies,
) -> Result<(), CodegenError> {
    let mut sig = Signature::new(CallConv::Tail);
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    emit_fn_body(m, fbctx, sig, locals.main_trampoline_id, |m, b| {
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let self_cl = b.block_params(entry)[0];
        let cont = b.block_params(entry)[1];
        let mut shim_cache = CodegenCache::default();
        let mut cg = CodegenFn::new(b, m, &mut shim_cache);
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

/// The scheduler holds the drain entry's address in an `extern "C"` fn pointer
/// and calls it once per pending dtor at task exit, so the target names the
/// convention. Sig: `(closure:i64, payload_ref:i64) -> i64`.
fn drain_dtor_entry_signature<M: cranelift_module::Module>(m: &mut M) -> Signature {
    let mut sig = m.make_signature();
    sig.params.push(AbiParam::new(types::I64)); // closure
    sig.params.push(AbiParam::new(types::I64)); // payload_ref
    sig.returns.push(AbiParam::new(types::I64));
    sig
}

/// Emit fz_drain_dtor_entry. The scheduler-callable shim that invokes a 1-arg
/// resource dtor closure with its payload. Picks a
/// Strict halt-cont, reads the body addr through
/// the closure ABI, and Tail-CC indirect-calls
/// `(payload_ref, closure, halt_cl)`. Result is discarded by the caller.
fn emit_drain_dtor_entry<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    locals: &LocalBodies,
) -> Result<(), CodegenError> {
    let sig = drain_dtor_entry_signature(m);
    emit_fn_body(m, fbctx, sig, locals.drain_dtor_entry_id, |m, b| {
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let closure = b.block_params(entry)[0];
        let payload_ref = b.block_params(entry)[1];
        let mut shim_cache = CodegenCache::default();
        let mut cg = CodegenFn::new(b, m, &mut shim_cache);
        // Strict halt-cont (kind=0). Dtor return is discarded;
        // ValueRef avoids RawInt/F64 unboxing.
        let halt_cl = cg.halt_cont_ref(locals, ArgRepr::ValueRef);
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
/// Closure header (word 0, see `closure_header_word`): the low 32 bits hold
/// four clear bits, then flags, then arity; the high 32 bits hold the
/// denotation. Flags low 14 bits = captured_count; high 2 bits = halt_kind.
fn emit_entry_thunk<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    locals: &LocalBodies,
) -> Result<(), CodegenError> {
    let mut sig = Signature::new(CallConv::Tail);
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    emit_fn_body(m, fbctx, sig, locals.entry_thunk_id, |m, b| {
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let self_cl = b.block_params(entry)[0];
        let mut shim_cache = CodegenCache::default();
        let mut cg = CodegenFn::new(b, m, &mut shim_cache);
        // capture[0] is the inner closure to launch.
        let zero_idx = cg.b.ins().iconst(types::I64, 0);
        let closure = cg.closure_capture_ref(self_cl, zero_idx);
        let kind = cg.closure_halt_kind_ref(closure);
        // Select the halt continuation by kind. Branchless via four
        // addresses + a tiny dispatch — keeps the thunk a leaf.
        let [a_strict, a_i64, a_f64, a_atom] = [ArgRepr::ValueRef, ArgRepr::RawInt, ArgRepr::RawF64, ArgRepr::RawAtom]
            .map(|repr| data_addr(cg.jmod, locals.halt_cont_data_id(repr), cg.b));
        let one = cg.b.ins().iconst(types::I32, 1);
        let two = cg.b.ins().iconst(types::I32, 2);
        let three = cg.b.ins().iconst(types::I32, 3);
        let is_i64 = cg.b.ins().icmp(IntCC::Equal, kind, one);
        let is_f64 = cg.b.ins().icmp(IntCC::Equal, kind, two);
        let is_atom = cg.b.ins().icmp(IntCC::Equal, kind, three);
        let pick_i64_or_tagged = cg.b.ins().select(is_i64, a_i64, a_strict);
        let pick_f64 = cg.b.ins().select(is_f64, a_f64, pick_i64_or_tagged);
        let hcb_addr = cg.b.ins().select(is_atom, a_atom, pick_f64);
        let halt_cl = cg.heap_ref_word_from_addr(hcb_addr, ValueKind::CLOSURE);
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
    locals: &LocalBodies,
) -> Result<(), CodegenError> {
    for repr in [ArgRepr::ValueRef, ArgRepr::RawInt, ArgRepr::RawF64, ArgRepr::RawAtom] {
        let mut sig = Signature::new(CallConv::Tail);
        push_repr_param(&mut sig, repr);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        emit_fn_body(m, fbctx, sig, locals.halt_cont_body_id(repr), |m, b| {
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);
            let value = b.block_params(entry)[0];
            let mut shim_cache = CodegenCache::default();
            let mut cg = CodegenFn::new(b, m, &mut shim_cache);
            cg.halt_implicit(repr, value);
            let zero = cg.b.ins().iconst(types::I64, 0);
            cg.b.ins().return_(&[zero]);
        })
        .map_err(|e| CodegenError::new(format!("define halt_cont_body: {}", e)))?;
    }
    Ok(())
}

/// The scheduler holds `fz_resume`'s address in an `extern "C"` fn pointer, so
/// the target names the convention. Sig: `(cont:i64) -> i64`.
fn resume_signature<M: cranelift_module::Module>(m: &mut M) -> Signature {
    let mut sig = m.make_signature();
    sig.params.push(AbiParam::new(types::I64)); // cont
    sig.returns.push(AbiParam::new(types::I64));
    sig
}

/// Single `fz_resume(cont) -> i64` shim. Bound args live in
/// the outcome closure env, so the shim sig is fixed regardless of
/// clause arity. Body:
///     code = call fz_closure_code_ref(cont)
///     call_indirect Tail(cont) -> i64
///     return result
fn emit_resume<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
) -> Result<FuncId, CodegenError> {
    let sig = resume_signature(m);
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
        let mut cg = CodegenFn::new(b, m, &mut shim_cache);
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
) -> Result<(ReceiveDispatchFnIds, ReceiveMatchedSites), CodegenError> {
    let mut dispatch_fn_ids: HashMap<(u32, u32), FuncId> = HashMap::new();
    let mut receive_matched_sites: Vec<(FnId, BlockId)> = Vec::new();
    for f in &module.fns {
        for blk in &f.blocks {
            let Term::ReceiveMatched { .. } = &blk.terminator else {
                continue;
            };
            let name = format!("fz_receive_dispatch_fn_{}_b{}", f.id.0, blk.id.0);
            let m_id = declare_receive_dispatch(m, &name)?;
            dispatch_fn_ids.insert((f.id.0, blk.id.0), m_id);
            receive_matched_sites.push((f.id, blk.id));
        }
    }
    Ok((dispatch_fn_ids, receive_matched_sites))
}

/// Emit receive-dispatch fn bodies for every Term::ReceiveMatched site
/// discovered in the pre-pass above. Dispatch fns were declared before the
/// fn-compilation loop so the park-site terminator arm could take
/// `func_addr` of the still-undefined symbols. A body never parks and runs
/// no `receive` of its own, so it always returns to its caller; it can still
/// call a runtime boxing extern when a test needs a raw scalar as an
/// `AnyValueRef`.
fn emit_receive_dispatch_bodies<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    module: &Module,
    tuple_schema_ids: &HashMap<usize, u32>,
    named_schema_ids: &HashMap<fz_runtime::module_name::ModuleName, u32>,
    dispatch_fn_ids: &HashMap<(u32, u32), FuncId>,
    receive_matched_sites: &[(FnId, BlockId)],
    tel: &impl RawSpanTelemetry,
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
        {
            let _span = tel.raw_span2_0(&["fz", "codegen", "lower_function"], module, fn_id);
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
            )?;
        }
    }
    Ok(())
}

/// Emit the Tail-CC body for every declared mid-flight continuation. The body
/// replays each argument from the closure capture array
/// and `return_call_indirect`s the callee body with its narrow ABI.
fn emit_mid_flight_cont_bodies<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    fn_ids: &HashMap<u32, FuncId>,
    mid_flight_cont_tail_fn_ids: &HashMap<(u32, Vec<MidFlightArgShape>), FuncId>,
) -> Result<(), CodegenError> {
    for ((callee_sid, arg_shapes), tail_id) in mid_flight_cont_tail_fn_ids.clone() {
        let callee_fid = *fn_ids
            .get(&callee_sid)
            .ok_or_else(|| CodegenError::new(format!("missing callee FuncId {callee_sid}")))?;
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
            let mut cg = CodegenFn::new(b, m, &mut shim_cache);
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

/// Declare the Tail-CC continuation for every back-edge TailCall to a
/// native callee. The native codegen surface precomputes the unique
/// `(callee_sid, arg_shapes)` keys; compiler2 native codegen only declares the
/// actual functions.
fn declare_mid_flight_conts<M: cranelift_module::Module>(
    m: &mut M,
    surface: &NativeCodegenSurface<'_>,
) -> Result<MidFlightContFnIds, CodegenError> {
    let mut mid_flight_cont_tail_fn_ids: HashMap<(u32, Vec<MidFlightArgShape>), FuncId> = HashMap::new();
    for key in &surface.mid_flight_cont_keys {
        let callee_sid = key.0;
        let cont_name = format!(
            "fz_mid_flight_cont_fn_{}_{}_tail",
            callee_sid,
            mid_flight_cont_tail_fn_ids.len()
        );
        let mut cont_sig = Signature::new(CallConv::Tail);
        cont_sig.params.push(AbiParam::new(types::I64));
        cont_sig.returns.push(AbiParam::new(types::I64));
        let cont_id = m
            .declare_function(&cont_name, Linkage::Local, &cont_sig)
            .map_err(|e| CodegenError::new(format!("declare {}: {}", cont_name, e)))?;
        mid_flight_cont_tail_fn_ids.insert(key.clone(), cont_id);
    }
    Ok(mid_flight_cont_tail_fn_ids)
}

pub(crate) fn compile_with_backend_native_program<
    B: Backend,
    T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes,
>(
    t: &mut T,
    program: &crate::compiler2::NativeProgram,
    backend: B,
    tel: &impl RawSpanTelemetry,
    output: &mut dyn super::super::dump::RequestedOutputSink,
) -> Result<B::Output, CodegenError> {
    let surface = prepare_native_codegen_surface_from_native_program(t, program)?;
    compile_with_backend_surface(t, &surface, backend, tel, output)
}

fn build_codegen_callable_boundaries<T: Types<Ty = Ty> + ClosureTypes>(
    _t: &mut T,
    program: &crate::compiler2::NativeProgram,
) -> BTreeMap<u32, NativeCallableBoundarySurface> {
    let mut boundaries = BTreeMap::new();
    for boundary in &program.callable_boundaries {
        let boundary_id = boundary.id().as_u32();
        let next = NativeCallableBoundarySurface {
            boundary_id: boundary.id(),
            denotation: boundary.denotation,
            source_origin: std::sync::Arc::clone(&boundary.source_origin),
            identity_fn: boundary.identity_fn,
            shape: boundary.shape.clone(),
            target_fn: boundary.wrapper_fn,
            capture_count: boundary.capture_reprs.len(),
            capture_reprs: boundary
                .capture_reprs
                .iter()
                .copied()
                .map(arg_repr_from_compiler2)
                .collect(),
            arg_reprs: vec![ArgRepr::ValueRef; boundary.call_arity],
            task_halt_repr: boundary.task_halt_repr.map(arg_repr_from_compiler2),
        };
        if let Some(previous) = boundaries.insert(boundary_id, next.clone()) {
            debug_assert_eq!(previous, next);
        }
    }
    boundaries
}

fn collect_codegen_mid_flight_cont_keys(
    program: &crate::compiler2::NativeProgram,
    param_reprs: &[Vec<ArgRepr>],
) -> Vec<(u32, Vec<MidFlightArgShape>)> {
    let entry_abis = program
        .bodies
        .iter()
        .map(|body| (body.fn_id, body.entry_abi.clone()))
        .collect::<HashMap<_, _>>();
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
            let arg_shapes = match entry_abis.get(&callee) {
                Some(crate::compiler2::NativeEntryAbi::Continuation { extra_params }) => callee_reprs
                    .iter()
                    .take(*extra_params)
                    .copied()
                    .map(MidFlightArgShape::Value)
                    .chain(std::iter::once(MidFlightArgShape::HeapRef))
                    .collect::<Vec<_>>(),
                _ => {
                    let mut shapes = callee_reprs
                        .iter()
                        .take(args.len())
                        .copied()
                        .map(MidFlightArgShape::Value)
                        .collect::<Vec<_>>();
                    shapes.push(MidFlightArgShape::HeapRef);
                    shapes
                }
            };
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
) -> Result<NativeCodegenSurface<'a>, CodegenError> {
    let max_fn_id = program
        .module
        .fns
        .iter()
        .map(|function| function.id.0 as usize)
        .max()
        .unwrap_or(0);
    let mut body_slots = (0..=max_fn_id).map(|_| None).collect::<Vec<_>>();
    let mut param_reprs = Vec::with_capacity(max_fn_id + 1);
    let mut halt_reprs = Vec::with_capacity(max_fn_id + 1);
    let mut return_diverges = Vec::with_capacity(max_fn_id + 1);
    param_reprs.resize(max_fn_id + 1, Vec::new());
    halt_reprs.resize(max_fn_id + 1, ArgRepr::ValueRef);
    return_diverges.resize(max_fn_id + 1, false);

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
        halt_reprs[codegen_id] = native_return_halt_repr(body);
        return_diverges[codegen_id] = t.is_empty(&body.return_ty);
    }

    let callable_boundaries = build_codegen_callable_boundaries(t, program);
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
        .map(|body| (body.fn_id.0, native_return_halt_repr(body).halt_kind()))
        .collect();

    Ok(NativeCodegenSurface {
        module: &program.module,
        diagnostics: Diagnostics::new(),
        main_fn_id: Some(program.entry),
        body_slots,
        callable_boundaries,
        mid_flight_cont_keys: collect_codegen_mid_flight_cont_keys(program, &param_reprs),
        param_reprs,
        halt_reprs,
        return_diverges,
        native_abi_fns,
        cont_target_fns,
        cont_fns,
        fn_halt_kinds,
    })
}

pub(crate) fn compile_with_backend_surface<
    B: Backend,
    T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes,
>(
    t: &mut T,
    surface: &NativeCodegenSurface<'_>,
    mut backend: B,
    tel: &impl RawSpanTelemetry,
    output: &mut dyn super::super::dump::RequestedOutputSink,
) -> Result<B::Output, CodegenError> {
    // Enclosing span: the denominator that makes codegen wall time account as
    // compile = declare + per-spec(lower + define) + emit_runtime + finalize.
    // Parent linkage is threaded by the bus from the open-span stack, so every
    // phase span below nests under this one automatically.
    let _compile_span = tel.raw_span1_0(&["fz", "codegen", "compile"], surface.module);
    let declare_span = tel.raw_span1_0(&["fz", "codegen", "declare"], surface.module);
    let locals = declare_local_bodies(backend.module_mut())?;

    let mut fbctx = FunctionBuilderContext::new();

    emit_main_trampoline(backend.module_mut(), &mut fbctx, &locals)?;
    emit_drain_dtor_entry(backend.module_mut(), &mut fbctx, &locals)?;
    emit_entry_thunk(backend.module_mut(), &mut fbctx, &locals)?;
    emit_halt_cont_bodies(backend.module_mut(), &mut fbctx, &locals)?;

    let user_schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let (tuple_arities, tuple_schema_ids) = collect_tuple_arities_and_register_schemas(surface.module, &user_schemas);
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

    let schemas = build_per_spec_schemas(body_slots);
    let frame_sizes: Vec<u32> = schemas.iter().map(|s| s.allocation_payload_size() as u32).collect();

    let fn_sigs = build_fn_sigs(backend.module_mut(), module, surface);

    let linkage = backend.fn_linkage();
    let fn_ids = declare_spec_fns(backend.module_mut(), linkage, body_slots, &fn_sigs)?;
    let callable_boundary_fn_ids = declare_callable_boundary_fns(backend.module_mut(), surface)?;
    let static_closure_data_ids =
        define_zero_capture_closures(backend.module_mut(), surface, &callable_boundary_fn_ids)?;
    let mid_flight_cont_tail_fn_ids = declare_mid_flight_conts(backend.module_mut(), surface)?;

    let bs_const_data: RefCell<HashMap<Vec<u8>, BsConstSyms>> = RefCell::new(HashMap::new());
    let (receive_dispatch_fn_ids, receive_matched_sites) = declare_receive_dispatch_fns(backend.module_mut(), module)?;
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
            locals: &locals,
            surface,
            module,
            active_spec_id: sid,
            active_body_fn_id: body_slot.fn_id,
            active_body_name: display_name,
            fn_ids: &fn_ids,
            callable_boundary_fn_ids: &callable_boundary_fn_ids,
            static_closure_data_ids: &static_closure_data_ids,
            mid_flight_cont_tail_fn_ids: &mid_flight_cont_tail_fn_ids,
            tuple_schema_ids: &tuple_schema_ids,
            named_schema_ids: &named_schema_ids,
            bs_const_data: &bs_const_data,
            param_reprs: &surface.param_reprs,
            halt_reprs: &surface.halt_reprs,
            return_diverges: &surface.return_diverges,
            native_abi_fns: &surface.native_abi_fns,
            cont_target_fns: &surface.cont_target_fns,
            cont_fns: &surface.cont_fns,
            receive_dispatch_fn_ids: &receive_dispatch_fn_ids,
        };
        {
            let _span = tel.raw_span2_0(&["fz", "codegen", "lower_function"], module, &body_slot.fn_id);
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
        }
        let fn_span = module.source.fn_span_of(f.id);
        // The native-compile step: verify the lowered Cranelift IR, then hand it
        // to the backend to produce machine code. This is the dominant per-spec
        // cost and was previously the unattributed gap between `lower_function`
        // spans; its stop payload carries the emitted code size.
        let define_span = tel.raw_span1_1(&["fz", "codegen", "define_function"], &body_slot.fn_id);
        if output.wants_clif() {
            output.clif(module, body_slot.fn_id, &ctx.func);
        }
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
        define_span.stop1(&ctx);
        backend.module_mut().clear_context(&mut ctx);
    }

    let emit_runtime_span = tel.raw_span1_0(&["fz", "codegen", "emit_runtime"], module);
    emit_receive_dispatch_bodies(
        backend.module_mut(),
        &mut fbctx,
        module,
        &tuple_schema_ids,
        &named_schema_ids,
        &receive_dispatch_fn_ids,
        &receive_matched_sites,
        tel,
    )?;

    emit_mid_flight_cont_bodies(backend.module_mut(), &mut fbctx, &fn_ids, &mid_flight_cont_tail_fn_ids)?;
    emit_callable_boundary_bodies(
        backend.module_mut(),
        &mut fbctx,
        &fn_ids,
        &callable_boundary_fn_ids,
        surface,
    )?;
    let resume_id = emit_resume(backend.module_mut(), &mut fbctx)?;
    drop(emit_runtime_span);

    let metadata = CompiledMetadata {
        closure_denotations: surface
            .callable_boundaries
            .values()
            .map(|boundary| (boundary.denotation, std::sync::Arc::clone(&boundary.source_origin)))
            .collect(),
        fn_ids,
        user_schemas,
        frame_sizes,
        atom_names: module.atom_names.clone(),
        tuple_arities: tuple_arities.iter().map(|&a| a as u32).collect(),
        named_schemas: module
            .struct_schemas
            .iter()
            .map(|(name, fields)| (name.clone(), fields.clone()))
            .collect(),
        diagnostics: surface.diagnostics.clone(),
        main_fn_id: surface.main_fn_id,
        entry_thunk_id: locals.entry_thunk_id,
        main_trampoline_id: locals.main_trampoline_id,
        drain_dtor_entry_id: locals.drain_dtor_entry_id,
        fn_halt_kinds: surface.fn_halt_kinds.clone(),
        resume_id,
    };

    let finalize_span = tel.raw_span1_0(&["fz", "codegen", "finalize"], module);
    backend.emit_metadata_carriers(&mut fbctx, &metadata)?;
    let output = backend.finalize(metadata)?;
    drop(finalize_span);
    Ok(output)
}

#[cfg(test)]
#[path = "driver_test.rs"]
mod driver_test;
