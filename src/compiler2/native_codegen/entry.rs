//! Entry-block harness: bind entry params and load closure captures.

use super::*;
use crate::fz_ir::FnIr;
use cranelift_codegen::ir;
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module as ClModule;
use std::collections::HashMap;

pub(crate) struct EntryHarnessOut {
    pub(super) var_env: HashMap<u32, CodegenValue>,
    /// The trailing i64 of the signature: the caller's continuation, or for a
    /// continuation fn its own closure (`self`).
    pub(super) cont_param: ir::Value,
}

pub(crate) fn build_entry_harness<M: ClModule>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    f: &FnIr,
    this_spec_id: u32,
    is_cont_fn: bool,
    entry_cl: ir::Block,
) -> EntryHarnessOut {
    let param_reprs = env.param_reprs;
    let entry_blk = f.blocks.iter().find(|blk| blk.id == f.entry).unwrap();
    let mut var_env: HashMap<u32, CodegenValue> = HashMap::new();
    let params: Vec<ir::Value> = body.b.block_params(entry_cl).to_vec();
    let my_param_reprs = &param_reprs[this_spec_id as usize];
    let cont_param = if is_cont_fn {
        let continuation_extra_count = continuation_entry_extra_count(env.body_native(this_spec_id));
        harness_cont_fn(
            body,
            entry_blk,
            &params,
            my_param_reprs,
            continuation_extra_count,
            &mut var_env,
        )
    } else {
        harness_plain_native(body.b, entry_blk, &params, my_param_reprs, &mut var_env)
    };
    EntryHarnessOut { var_env, cont_param }
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
/// Tuple-field delivered continuations publish one entry block param per field,
/// not one synthetic tuple param. If the semantic program wants a tuple value,
/// native lowering reconstructs it explicitly in the body with `Prim::MakeTuple`.
///
/// Returns the closure's own pointer (`self`), which is the fn's `cont_param`.
fn harness_cont_fn<M: ClModule>(
    body: &mut CodegenFn<'_, '_, M>,
    entry_blk: &crate::fz_ir::Block,
    params: &[ir::Value],
    my_param_reprs: &[ArgRepr],
    extras_count: usize,
    var_env: &mut HashMap<u32, CodegenValue>,
) -> ir::Value {
    let mut param_cursor = 0;
    for (i, p) in entry_blk.params.iter().take(extras_count).enumerate() {
        let repr = my_param_reprs[i];
        var_env.insert(p.0, take_param_binding(body.b, params, &mut param_cursor, repr));
    }
    let self_val = params[param_cursor];
    for (i, p) in entry_blk.params.iter().enumerate().skip(extras_count) {
        let capture_idx = 1 + i - extras_count;
        let repr_idx = i;
        let binding = body.closure_capture_as_binding(self_val, capture_idx, my_param_reprs[repr_idx]);
        var_env.insert(p.0, binding);
    }
    self_val
}

/// Plain native fn entry harness.
/// Cranelift sig: `(args..., cont) tail`.
/// All entry block params map 1:1 to leading Cranelift params via
/// each ArgRepr's abi_arity; the trailing slot carries the cont SSA.
///
/// Returns the trailing cont SSA value.
fn harness_plain_native(
    b: &mut FunctionBuilder<'_>,
    entry_blk: &crate::fz_ir::Block,
    params: &[ir::Value],
    my_param_reprs: &[ArgRepr],
    var_env: &mut HashMap<u32, CodegenValue>,
) -> ir::Value {
    let mut param_cursor = 0;
    for (i, p) in entry_blk.params.iter().enumerate() {
        let repr = my_param_reprs[i];
        var_env.insert(p.0, take_param_binding(b, params, &mut param_cursor, repr));
    }
    let cont_idx = param_cursor;
    params[cont_idx]
}
