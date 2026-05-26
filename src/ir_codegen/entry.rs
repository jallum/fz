//! Split from src/ir_codegen.rs (fz-ame.7). Mechanical move only.

#![allow(unused_imports)]

use super::*;
use crate::fz_ir::{BinOp, Const, FnId, Module, Prim, Stmt, Term, UnOp};
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
use fz_runtime::heap::{FieldDescriptor, FieldKind, Schema};
use std::collections::HashMap;
use std::sync::Arc;

pub(crate) struct EntryHarnessOut {
    pub(super) var_env: HashMap<u32, CodegenValue>,
    /// Some for uniform fns; None for native.
    pub(super) frame_ptr: Option<ir::Value>,
    /// Some for uniform fns; None for native.
    pub(super) host_ctx: Option<ir::Value>,
    /// Some for native fns (trailing cont SSA); None for uniform.
    pub(super) cont_param: Option<ir::Value>,
    pub(super) tuple_field_params: HashMap<(u32, u32), CodegenValue>,
    pub(super) list_tail_param: Option<ir::Value>,
}

pub(crate) fn build_entry_harness<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    env: &CodegenEnv<'_>,
    schemas: &[Schema],
    f: &crate::fz_ir::FnIr,
    this_spec_id: u32,
    is_native: bool,
    is_cont_fn: bool,
    closure_target_n_caps: Option<usize>,
    entry_cl: ir::Block,
) -> EntryHarnessOut {
    let param_reprs = env.param_reprs;
    let entry_blk = f.blocks.iter().find(|blk| blk.id == f.entry).unwrap();
    let mut var_env: HashMap<u32, CodegenValue> = HashMap::new();
    let mut tuple_field_params: HashMap<(u32, u32), CodegenValue> = HashMap::new();
    let my_schema = &schemas[this_spec_id as usize];

    // (frame_ptr, host_ctx) — uniform fns get both from entry block_params;
    // native fns have no frame and no frame_ptr (None). fz-ul4.27.16: the
    // 9 downstream consumer sites are each gated on `is_native` or on a
    // terminator type that natively_callable excludes from native fns,
    // so unwrapping the Option below is invariant-safe. Any future code
    // path that violates this surfaces immediately as a panic at codegen.
    // host_ctx is Some only for uniform fns (always the second block param).
    // Native fns always have host_ctx = None; they use fz_halt_implicit (TLS).
    // fz-cps.1.a (fz-siu.1.1): `cont_param` is the trailing i64 in the
    // native-tier signature. Threaded but unused in .1.1; .1.2+ consume it.
    let demand_abi = DemandAbi::new(&env.spec_keys[this_spec_id as usize]);
    let has_list_tail_dest = demand_abi.has_list_tail_native_param(is_native, is_cont_fn);
    let (frame_ptr, host_ctx, cont_param, list_tail_param): (
        Option<ir::Value>,
        Option<ir::Value>,
        Option<ir::Value>,
        Option<ir::Value>,
    ) = if is_native {
        let params: Vec<ir::Value> = b.block_params(entry_cl).to_vec();
        let my_param_reprs = &param_reprs[this_spec_id as usize];
        if is_cont_fn {
            // fz-cps.1.2 cont fn entry harness per §2.1:
            //   params[0..N] = extras     → fz_param[0..N]
            //   params[N]    = self       → closure ptr
            // Closure env layout:
            //   self+8  : code_ptr
            //   self+16 : outer_cont       (synthetic; not in fz_param)
            //   self+24 : user_cap[0]      -> fz_param[N]
            //   self+32 : user_cap[1]      -> fz_param[N+1]
            //   ...
            //
            // fz-70q.3 — extras_count defaults to 1 (single-input
            // Receive cont) but ReceiveMatched lowering overrides via
            // `cont_extras_count`: body / guard fns set it to
            // bound_arity; after-body sets 0.
            let tuple_fields = demand_abi.tuple_field_arity();
            let extras_count = tuple_fields
                .unwrap_or_else(|| env.cont_extras_count.get(&f.id).copied().unwrap_or(1));
            // fz-ul4.27.22.3: cont sig matches my_param_reprs[i]'s
            // Cranelift type directly. Producer's Term::Return uses the
            // same sig (return_reprs[producer_sid] = my_param_reprs[0]
            // via the typer's cont_input_key seam agreement). No coerce
            // at entry — value already in body's expected repr.
            let mut param_cursor = 0;
            if let Some(field_count) = tuple_fields {
                let tuple_param = entry_blk
                    .params
                    .first()
                    .expect("TupleFields cont requires tuple slot0");
                for (i, repr) in my_param_reprs.iter().copied().enumerate().take(field_count) {
                    let binding = take_param_binding(b, &params, &mut param_cursor, repr);
                    tuple_field_params.insert((tuple_param.0, i as u32), binding);
                }
            } else {
                for (i, p) in entry_blk.params.iter().take(extras_count).enumerate() {
                    let repr = my_param_reprs[i];
                    var_env.insert(p.0, take_param_binding(b, &params, &mut param_cursor, repr));
                }
            }
            let self_val = params[param_cursor];
            let first_capture_param = if tuple_fields.is_some() {
                1
            } else {
                extras_count
            };
            let has_appended_list_tail = demand_abi.carries_list_tail_capture();
            let user_captures = entry_blk.params.len().saturating_sub(first_capture_param);
            let captured_count = 1 + user_captures + usize::from(has_appended_list_tail);
            for (i, p) in entry_blk
                .params
                .iter()
                .enumerate()
                .skip(first_capture_param)
            {
                let capture_idx = 1 + i - first_capture_param;
                let repr_idx = if tuple_fields.is_some() {
                    extras_count + i - first_capture_param
                } else {
                    i
                };
                let binding = load_closure_capture_as_binding(
                    b,
                    jmod,
                    env.runtime,
                    self_val,
                    captured_count,
                    capture_idx,
                    my_param_reprs[repr_idx],
                );
                var_env.insert(p.0, binding);
            }
            let list_tail_val = if has_appended_list_tail {
                let idx = 1 + user_captures;
                let index = b.ins().iconst(types::I64, idx as i64);
                let fref =
                    jmod.declare_func_in_func(env.runtime.closure_get_capture_ref_id, b.func);
                let inst = b.ins().call(fref, &[self_val, index]);
                Some(b.inst_results(inst)[0])
            } else {
                None
            };
            let host_ctx = None;
            (None, host_ctx, Some(self_val), list_tail_val)
        } else if let Some(n_caps) = closure_target_n_caps {
            // fz-cps.1.2 closure-target fn entry harness per §2.1.
            // fz_params order:
            //   fz_params[0..n_caps]             = captures
            //   fz_params[n_caps..n_caps+n_args] = args
            // Cranelift sig: `(args..., self, cont) tail`.
            //   params[0..n_args]  = args
            //   params[n_args]     = self  (closure ptr)
            //   params[n_args+1]   = cont  (cont SSA)
            let _n_args = entry_blk.params.len().saturating_sub(n_caps);
            let mut param_cursor = 0;
            for (j, p) in entry_blk.params.iter().enumerate().skip(n_caps) {
                let repr = my_param_reprs[j];
                var_env.insert(p.0, take_param_binding(b, &params, &mut param_cursor, repr));
            }
            let self_val = params[param_cursor];
            let list_tail_val = if has_list_tail_dest {
                Some(params[param_cursor + 1])
            } else {
                None
            };
            let cont_val = params[param_cursor + 1 + usize::from(has_list_tail_dest)];
            // Captures are ordinary schema fields in the closure env.
            // The body reads each capture as an opaque ref and coerces to
            // its narrow capture repr internally.
            for (k, p) in entry_blk.params.iter().enumerate().take(n_caps) {
                let binding = load_closure_capture_as_binding(
                    b,
                    jmod,
                    env.runtime,
                    self_val,
                    n_caps,
                    k,
                    my_param_reprs[k],
                );
                var_env.insert(p.0, binding);
            }
            debug_assert_eq!(
                param_cursor,
                my_param_reprs[n_caps..]
                    .iter()
                    .map(ArgRepr::abi_arity)
                    .sum::<usize>()
            );
            let _ = self_val;
            (None, None, Some(cont_val), list_tail_val)
        } else {
            let mut param_cursor = 0;
            for (i, p) in entry_blk.params.iter().enumerate() {
                let repr = my_param_reprs[i];
                var_env.insert(p.0, take_param_binding(b, &params, &mut param_cursor, repr));
            }
            let (host_ctx, cont_idx) = (None, param_cursor);
            let list_tail_val = if has_list_tail_dest {
                Some(params[cont_idx])
            } else {
                None
            };
            let cont_idx = cont_idx + usize::from(has_list_tail_dest);
            (None, host_ctx, Some(params[cont_idx]), list_tail_val)
        }
    } else {
        let frame_ptr = b.block_params(entry_cl)[0];
        let host_ctx = b.block_params(entry_cl)[1];

        // Load entry params from frame slots [1..N+1] (offsets 24, 32, ...).
        // fz-ul4.27.5.2/3: RawF64 slots load as raw f64 (ArgRepr::RawF64);
        // RawI64 slots load as raw i64 (ArgRepr::RawInt — unshifted payload).
        // Everything else loads as one-word ValueRef (ArgRepr::ValueRef).
        for (i, p) in entry_blk.params.iter().enumerate() {
            let off = HEADER_SIZE + ((i as i32 + 1) * SLOT_BYTES);
            let slot_kind = &my_schema.fields[i + 1].kind;
            let binding = match slot_kind {
                FieldKind::RawF64 => {
                    let f = b
                        .ins()
                        .load(types::F64, MemFlags::trusted(), frame_ptr, off);
                    CodegenValue::from_abi_value(f, ArgRepr::RawF64)
                }
                FieldKind::RawI64 => {
                    let n = b
                        .ins()
                        .load(types::I64, MemFlags::trusted(), frame_ptr, off);
                    CodegenValue::from_abi_value(n, ArgRepr::RawInt)
                }
                _ => {
                    let value_ref = b
                        .ins()
                        .load(types::I64, MemFlags::trusted(), frame_ptr, off);
                    CodegenValue::any_ref(value_ref)
                }
            };
            var_env.insert(p.0, binding);
        }
        // fz-cps.1.a: uniform fns do not yet have a cont SSA value; the
        // cont still lives in slot 0 of `frame_ptr` until fz-siu.1.5.
        (Some(frame_ptr), Some(host_ctx), None, None)
    };
    EntryHarnessOut {
        var_env,
        frame_ptr,
        host_ctx,
        cont_param,
        tuple_field_params,
        list_tail_param,
    }
}
