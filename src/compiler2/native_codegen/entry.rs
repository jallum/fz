//! Entry-block harness: bind entry params and load closure captures.

use super::*;
use crate::fz_ir::FnIr;
use cranelift_codegen::ir::{self, InstBuilder, MemFlags, types};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module as ClModule;
use fz_runtime::heap::{FieldKind, Schema};
use std::collections::HashMap;

pub(crate) struct EntryHarnessOut {
    pub(super) var_env: HashMap<u32, CodegenValue>,
    /// Some for uniform fns; None for native.
    pub(super) frame_ptr: Option<ir::Value>,
    /// Some for uniform fns; None for native.
    pub(super) host_ctx: Option<ir::Value>,
    /// Some for native fns (trailing cont SSA); None for uniform.
    pub(super) cont_param: Option<ir::Value>,
    pub(super) tuple_field_params: HashMap<(u32, u32), CodegenValue>,
}

pub(crate) fn build_entry_harness<M: ClModule>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    env: &CodegenEnv<'_>,
    schemas: &[Schema],
    f: &FnIr,
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

    // (frame_ptr, host_ctx) are Some only for uniform fns (both from
    // entry block_params). Native fns have no frame; they reach halt via
    // fz_halt_implicit (TLS). Downstream consumers gate on `is_native`
    // (or on a terminator type the planned ABI facts exclude), so unwrapping
    // the Option panics loudly at codegen if any future path violates
    // the invariant. `cont_param` is the trailing i64 in the native-tier
    // signature.
    let demand_abi = NativeDemandAbi::new(env.body_native(this_spec_id));
    let (frame_ptr, host_ctx, cont_param): (Option<ir::Value>, Option<ir::Value>, Option<ir::Value>) = if is_native {
        let params: Vec<ir::Value> = body.b.block_params(entry_cl).to_vec();
        let my_param_reprs = &param_reprs[this_spec_id as usize];
        if is_cont_fn {
            harness_cont_fn(
                body,
                entry_blk,
                &params,
                my_param_reprs,
                &demand_abi,
                &mut var_env,
                &mut tuple_field_params,
            )
        } else if let Some(n_caps) = closure_target_n_caps {
            harness_closure_target(body, entry_blk, &params, my_param_reprs, n_caps, &mut var_env)
        } else {
            harness_plain_native(body.b, entry_blk, &params, my_param_reprs, &mut var_env)
        }
    } else {
        let frame_ptr = body.b.block_params(entry_cl)[0];
        let host_ctx = body.b.block_params(entry_cl)[1];

        // Load entry params from frame slots [1..N+1] (offsets 24, 32, ...).
        // RawF64 slots load as raw f64; RawI64 slots load as raw i64
        // (unshifted payload); everything else loads as one-word ValueRef.
        for (i, p) in entry_blk.params.iter().enumerate() {
            let off = HEADER_SIZE + ((i as i32 + 1) * SLOT_BYTES);
            let slot_kind = &my_schema.fields[i + 1].kind;
            let binding = match slot_kind {
                FieldKind::RawF64 => {
                    let f = body.b.ins().load(types::F64, MemFlags::trusted(), frame_ptr, off);
                    CodegenValue::from_abi_value(f, ArgRepr::RawF64)
                }
                FieldKind::RawI64 => {
                    let n = body.b.ins().load(types::I64, MemFlags::trusted(), frame_ptr, off);
                    CodegenValue::from_abi_value(n, ArgRepr::RawInt)
                }
                _ => {
                    let value_ref = body.b.ins().load(types::I64, MemFlags::trusted(), frame_ptr, off);
                    CodegenValue::any_ref(value_ref)
                }
            };
            var_env.insert(p.0, binding);
        }
        // Uniform fns do not have a cont SSA value; the cont lives in
        // slot 0 of `frame_ptr`.
        (Some(frame_ptr), Some(host_ctx), None)
    };
    EntryHarnessOut {
        var_env,
        frame_ptr,
        host_ctx,
        cont_param,
        tuple_field_params,
    }
}

/// Cont fn entry harness:
///   params[0..N] = extras     -> fz_param[0..N]
///   params[N]    = self       -> closure ptr
/// Closure env layout:
///   self+8  : code_ptr
///   self+16 : outer_cont       (synthetic; not in fz_param)
///   self+24 : user_cap[0]      -> fz_param[N]
///   self+32 : user_cap[1]      -> fz_param[N+1]
///   ...
///
/// extras_count defaults to 1 (single-input call continuation), unless the
/// settled continuation entry ABI says otherwise.
/// Cont sig matches my_param_reprs[i]'s Cranelift type directly;
/// producer's Term::Return uses the same sig, so no coerce at
/// entry.
///
/// Returns (frame_ptr, host_ctx, cont_param).
fn harness_cont_fn<M: ClModule>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    entry_blk: &crate::fz_ir::Block,
    params: &[ir::Value],
    my_param_reprs: &[ArgRepr],
    demand_abi: &NativeDemandAbi<'_>,
    var_env: &mut HashMap<u32, CodegenValue>,
    tuple_field_params: &mut HashMap<(u32, u32), CodegenValue>,
) -> (Option<ir::Value>, Option<ir::Value>, Option<ir::Value>) {
    let tuple_fields = demand_abi.tuple_field_arity();
    let extras_count = demand_abi.continuation_extras();
    let mut param_cursor = 0;
    if let Some(field_count) = tuple_fields {
        let tuple_param = entry_blk.params.first().expect("TupleFields cont requires tuple slot0");
        for (i, repr) in my_param_reprs.iter().copied().enumerate().take(field_count) {
            let binding = take_param_binding(body.b, params, &mut param_cursor, repr);
            tuple_field_params.insert((tuple_param.0, i as u32), binding);
        }
    } else {
        for (i, p) in entry_blk.params.iter().take(extras_count).enumerate() {
            let repr = my_param_reprs[i];
            var_env.insert(p.0, take_param_binding(body.b, params, &mut param_cursor, repr));
        }
    }
    let self_val = params[param_cursor];
    let first_capture_param = if tuple_fields.is_some() { 1 } else { extras_count };
    for (i, p) in entry_blk.params.iter().enumerate().skip(first_capture_param) {
        let capture_idx = 1 + i - first_capture_param;
        let repr_idx = if tuple_fields.is_some() {
            extras_count + i - first_capture_param
        } else {
            i
        };
        let binding = body.closure_capture_as_binding(self_val, capture_idx, my_param_reprs[repr_idx]);
        var_env.insert(p.0, binding);
    }
    (None, None, Some(self_val))
}

/// Closure-target fn entry harness.
/// fz_params order:
///   fz_params[0..n_caps]             = captures
///   fz_params[n_caps..n_caps+n_args] = args
/// Cranelift sig: `(args..., self, cont) tail`.
///   params[0..n_args]  = args
///   params[n_args]     = self  (closure ptr)
///   params[n_args+1]   = cont  (cont SSA)
///
/// Captures are ordinary schema fields in the closure env. The body
/// reads each capture as an opaque ref and coerces to its narrow
/// capture repr internally.
///
/// Returns (frame_ptr, host_ctx, cont_param).
fn harness_closure_target<M: ClModule>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    entry_blk: &crate::fz_ir::Block,
    params: &[ir::Value],
    my_param_reprs: &[ArgRepr],
    n_caps: usize,
    var_env: &mut HashMap<u32, CodegenValue>,
) -> (Option<ir::Value>, Option<ir::Value>, Option<ir::Value>) {
    let _n_args = entry_blk.params.len().saturating_sub(n_caps);
    let mut param_cursor = 0;
    for (j, p) in entry_blk.params.iter().enumerate().skip(n_caps) {
        let repr = my_param_reprs[j];
        var_env.insert(p.0, take_param_binding(body.b, params, &mut param_cursor, repr));
    }
    let self_val = params[param_cursor];
    let cont_val = params[param_cursor + 1];
    for (k, p) in entry_blk.params.iter().enumerate().take(n_caps) {
        let binding = body.closure_capture_as_binding(self_val, k, my_param_reprs[k]);
        var_env.insert(p.0, binding);
    }
    debug_assert_eq!(
        param_cursor,
        my_param_reprs[n_caps..].iter().map(ArgRepr::abi_arity).sum::<usize>()
    );
    let _ = self_val;
    (None, None, Some(cont_val))
}

/// Plain native fn entry harness.
/// Cranelift sig: `(args..., cont) tail`.
/// All entry block params map 1:1 to leading Cranelift params via
/// each ArgRepr's abi_arity; the trailing slot carries the cont SSA.
///
/// Returns (frame_ptr, host_ctx, cont_param).
fn harness_plain_native(
    b: &mut FunctionBuilder<'_>,
    entry_blk: &crate::fz_ir::Block,
    params: &[ir::Value],
    my_param_reprs: &[ArgRepr],
    var_env: &mut HashMap<u32, CodegenValue>,
) -> (Option<ir::Value>, Option<ir::Value>, Option<ir::Value>) {
    let mut param_cursor = 0;
    for (i, p) in entry_blk.params.iter().enumerate() {
        let repr = my_param_reprs[i];
        var_env.insert(p.0, take_param_binding(b, params, &mut param_cursor, repr));
    }
    let cont_idx = param_cursor;
    (None, None, Some(params[cont_idx]))
}
