//! Entry-block harness: bind entry params and load closure captures.

use super::*;
use crate::fast_hash::HashMap;
use crate::fz_ir::FnIr;
use cranelift_codegen::ir;
use cranelift_module::Module as ClModule;

pub(crate) struct EntryHarnessOut {
    pub(super) var_env: HashMap<u32, CodegenValue>,
    /// The caller's continuation: the signature's trailing i64, or for a
    /// continuation fn the outer continuation read from its frame.
    pub(super) cont_param: ir::Value,
    /// A continuation fn's own closure (the frame it runs in).
    pub(super) self_ref: Option<ir::Value>,
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
    let entry_blk = f.block(f.entry);
    let mut var_env: HashMap<u32, CodegenValue> = HashMap::default();
    let params: Vec<ir::Value> = body.b.block_params(entry_cl).to_vec();
    let my_param_reprs = &param_reprs[this_spec_id as usize];
    let mut self_ref = None;
    let cont_param = if is_cont_fn {
        let continuation_extra_count = continuation_entry_extra_count(env.body_native(this_spec_id));
        let in_frame = env.body_native(this_spec_id).frame.is_some();
        let (outer, own) = harness_cont_fn(
            body,
            entry_blk,
            &params,
            my_param_reprs,
            continuation_extra_count,
            in_frame,
            &mut var_env,
        );
        self_ref = Some(own);
        outer
    } else {
        harness_plain_native(entry_blk, &params, my_param_reprs, &mut var_env)
    };
    EntryHarnessOut {
        var_env,
        cont_param,
        self_ref,
    }
}

/// Cont fn entry harness:
///   params[0..N] = extras     -> fz_param[0..N]
///   params[N]    = self       -> closure ptr (the frame; given back after the reads)
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
/// Every capture and the outer continuation are read into registers first,
/// then the frame is released (see `release_resumed_frame`), unless the frame
/// is a body frame (`in_frame`): other continuations of the body still read it,
/// so it is never released at a resume. Returns the outer continuation, which
/// is the fn's `cont_param`, and the frame the fn runs in.
fn harness_cont_fn<M: ClModule>(
    body: &mut CodegenFn<'_, '_, M>,
    entry_blk: &crate::fz_ir::Block,
    params: &[ir::Value],
    my_param_reprs: &[ArgRepr],
    extras_count: usize,
    in_frame: bool,
    var_env: &mut HashMap<u32, CodegenValue>,
) -> (ir::Value, ir::Value) {
    let mut param_cursor = 0;
    for (i, p) in entry_blk.params.iter().take(extras_count).enumerate() {
        let repr = my_param_reprs[i];
        var_env.insert(p.0, take_param_binding(params, &mut param_cursor, repr));
    }
    let self_val = params[param_cursor];
    let slot_count = 1 + entry_blk.params.len() - extras_count;
    let count = if in_frame {
        CaptureCount::InHeader
    } else {
        CaptureCount::Compiled(slot_count)
    };
    for (i, p) in entry_blk.params.iter().enumerate().skip(extras_count) {
        let capture_idx = 1 + i - extras_count;
        let repr_idx = i;
        let binding = body.closure_capture_as_binding(self_val, capture_idx, my_param_reprs[repr_idx], count);
        var_env.insert(p.0, binding);
    }
    if in_frame {
        return (body.outer_cont_ref(self_val), self_val);
    }
    let ref_slots: Vec<usize> = (extras_count..entry_blk.params.len())
        .filter(|&i| my_param_reprs[i] == ArgRepr::ValueRef)
        .map(|i| 1 + i - extras_count)
        .collect();
    if outer_cont_read_after_release() {
        release_resumed_frame(body, self_val, &ref_slots, slot_count);
        return (body.outer_cont_ref(self_val), self_val);
    }
    let outer_cont = body.outer_cont_ref(self_val);
    release_resumed_frame(body, self_val, &ref_slots, slot_count);
    (outer_cont, self_val)
}

/// Plain native fn entry harness.
/// Cranelift sig: `(args..., cont) tail`.
/// All entry block params map 1:1 to leading Cranelift params via
/// each ArgRepr's abi_arity; the trailing slot carries the cont SSA.
///
/// Returns the trailing cont SSA value.
fn harness_plain_native(
    entry_blk: &crate::fz_ir::Block,
    params: &[ir::Value],
    my_param_reprs: &[ArgRepr],
    var_env: &mut HashMap<u32, CodegenValue>,
) -> ir::Value {
    let mut param_cursor = 0;
    for (i, p) in entry_blk.params.iter().enumerate() {
        let repr = my_param_reprs[i];
        var_env.insert(p.0, take_param_binding(params, &mut param_cursor, repr));
    }
    let cont_idx = param_cursor;
    params[cont_idx]
}

#[cfg(test)]
#[path = "entry_test.rs"]
mod entry_test;
