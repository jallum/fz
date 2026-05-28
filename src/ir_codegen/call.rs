//! Call, return, halt, and frame-slot emission helpers.

use super::*;
use cranelift_codegen::ir::{self, BlockArg, InstBuilder, MemFlags, condcodes::IntCC, types};
use cranelift_frontend::FunctionBuilder;
use fz_runtime::heap::Schema;
use std::collections::HashMap;

pub(crate) fn emit_halt_for_binding<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    var_env: &HashMap<u32, CodegenValue>,
    cache: &mut CodegenCache,
    var: u32,
    binding: CodegenValue,
) {
    let mut body = cx.body(b, jmod, cache);
    match binding.repr() {
        ArgRepr::RawInt => {
            body.halt_implicit(ArgRepr::RawInt, binding.value());
        }
        ArgRepr::RawF64 => {
            body.halt_implicit(ArgRepr::RawF64, binding.value());
        }
        ArgRepr::ValueRef | ArgRepr::Condition => {
            let value_ref = body.any_ref_for_var(var_env, var);
            body.halt_implicit(ArgRepr::ValueRef, value_ref);
        }
    }
}

pub(crate) fn emit_halt_from_codegen_value<M: cranelift_module::Module>(
    body: &mut CodegenFnBody<'_, '_, '_, M>,
    value: CodegenValue,
) {
    match value {
        CodegenValue::RawInt(value) => {
            body.halt_implicit(ArgRepr::RawInt, value);
        }
        CodegenValue::RawF64(value) => {
            body.halt_implicit(ArgRepr::RawF64, value);
        }
        value => {
            let value_ref = body.value_as_any_ref(value);
            body.halt_implicit(ArgRepr::ValueRef, value_ref);
        }
    }
}

/// Term::Return: load my cont_ptr from frame[16]. If null, halt.
/// Otherwise write `val` to cont_frame[24] (continuation's "result" slot —
/// always entry param 0) and return cont_ptr.
///
/// `frame_ptr` is `Option` because native fns don't have a frame; the
/// natively_callable invariant guarantees this helper is never reached
/// from a native fn body. Unwrapping with `.expect()` turns any future
/// invariant break into a loud panic at codegen time rather than a
/// silent load-from-zero.
pub(crate) fn emit_return<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    cache: &mut CodegenCache,
    frame_ptr: Option<ir::Value>,
    value: CodegenValue,
) {
    let frame_ptr = frame_ptr
        .expect("emit_return reached from native-fn body — natively_callable invariant violated");
    let cont_ptr = b
        .ins()
        .load(types::I64, MemFlags::trusted(), frame_ptr, HEADER_SIZE);
    // One `iconst.i64 0` serves both the null-compare and the halt-branch
    // return sentinel; SSA dominance lets the halt block reuse it.
    let zero = b.ins().iconst(types::I64, 0);
    let is_null = b.ins().icmp(IntCC::Equal, cont_ptr, zero);

    let halt_blk = b.create_block();
    let invoke_blk = b.create_block();
    let no_args: Vec<BlockArg> = Vec::new();
    b.ins()
        .brif(is_null, halt_blk, &no_args, invoke_blk, &no_args);

    // halt: record the strict value and return null (reusing `zero`).
    b.switch_to_block(halt_blk);
    b.seal_block(halt_blk);
    {
        let mut body = cx.body(b, jmod, cache);
        emit_halt_from_codegen_value(&mut body, value);
    }
    b.ins().return_(&[zero]);

    // invoke: write val to cont[24], return cont_ptr.
    b.switch_to_block(invoke_blk);
    b.seal_block(invoke_blk);
    cx.body(b, jmod, cache)
        .store_frame_value_dynamic(cont_ptr, SLOT_BYTES as u32, value);
    b.ins().return_(&[cont_ptr]);
}

/// Specialized emit_return for fns whose cont_ptr is statically known
/// to be null at runtime — fns never used as a cont target anywhere in
/// the module can only be invoked as the trampoline entry, which writes
/// null into slot 0. Skips the load/icmp/brif dispatch and the dead
/// invoke-branch entirely; records the strict halt value and returns null.
///
/// Takes no `frame_ptr` because none is read.
pub(crate) fn emit_halt_and_return_null<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    cache: &mut CodegenCache,
    value: CodegenValue,
) {
    {
        let mut body = cx.body(b, jmod, cache);
        emit_halt_from_codegen_value(&mut body, value);
    }
    let null = b.ins().iconst(types::I64, 0);
    b.ins().return_(&[null]);
}

/// Term::Call: allocate continuation frame + callee frame. Continuation
/// frame = [my_cont_ptr, result_placeholder, ...captured]. Callee frame =
/// [cont_frame_ptr, ...args]. Return callee frame ptr.
pub(crate) fn emit_call<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    schemas: &[Schema],
    frame_ptr: Option<ir::Value>,
    callee_id: u32,
    args: &[CodegenValue],
    cont: Option<(u32, &[CodegenValue])>,
    cache: &mut CodegenCache,
) {
    let frame_ptr = frame_ptr
        .expect("emit_call reached from native-fn body — natively_callable invariant violated");
    // Read my cont_ptr from current frame[16] — this becomes the cont frame's cont_ptr.
    let my_cont = b
        .ins()
        .load(types::I64, MemFlags::trusted(), frame_ptr, HEADER_SIZE);

    let cont_frame_val = match cont {
        Some((cont_fn_id, captured)) => {
            let cont_schema = &schemas[cont_fn_id as usize];
            let sid = b.ins().iconst(types::I32, cont_fn_id as i64);
            let sz = b
                .ins()
                .iconst(types::I32, cont_schema.allocation_payload_size() as i64);
            let cf = cx.body(b, jmod, cache).alloc_frame(sid, sz);
            // Slot 0 (offset 16): cont_ptr = my_cont (my own continuation).
            b.ins().store(MemFlags::trusted(), my_cont, cf, HEADER_SIZE);
            // Slot 1 (offset 24) is the continuation's "result" param —
            // left uninitialized; will be filled by callee's Term::Return.
            // Slots 2..K+2: captured vars in declaration order. Kind-aware
            // store so a typed-int / typed-float captured slot gets its
            // raw payload, not one-word ValueRef.
            cx.body(b, jmod, cache)
                .store_bindings_into_callee_frame(cont_schema, cf, captured, 2);
            cf
        }
        None => my_cont,
    };

    // Allocate callee frame.
    let callee_schema = &schemas[callee_id as usize];
    let sid = b.ins().iconst(types::I32, callee_id as i64);
    let sz = b
        .ins()
        .iconst(types::I32, callee_schema.allocation_payload_size() as i64);
    let callee_frame = cx.body(b, jmod, cache).alloc_frame(sid, sz);
    // Slot 0: cont_ptr = cont_frame_val.
    b.ins().store(
        MemFlags::trusted(),
        cont_frame_val,
        callee_frame,
        HEADER_SIZE,
    );
    // Slots 1..N+1: args. Each local binding is written according to the
    // callee frame schema.
    cx.body(b, jmod, cache)
        .store_bindings_into_callee_frame(callee_schema, callee_frame, args, 1);

    b.ins().return_(&[callee_frame]);
}

/// Term::TailCall: if callee shares schema with caller, overwrite caller's
/// frame in place. Otherwise allocate a new frame. Either way, cont_ptr is
/// preserved (the parent's continuation).
pub(crate) fn emit_tail_call<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    schemas: &[Schema],
    self_id: u32,
    frame_ptr: Option<ir::Value>,
    callee_id: u32,
    args: &[CodegenValue],
    cache: &mut CodegenCache,
) {
    let frame_ptr = frame_ptr.expect(
        "emit_tail_call reached from native-fn body — natively_callable invariant violated",
    );
    let callee_schema = &schemas[callee_id as usize];

    if self_id == callee_id {
        // Same schema: overwrite slots 1..N+1 with new args. Slot 0 (cont) stays.
        cx.body(b, jmod, cache)
            .store_bindings_into_callee_frame(callee_schema, frame_ptr, args, 1);
        b.ins().return_(&[frame_ptr]);
    } else {
        // Different schema: alloc fresh, copy cont_ptr, write args.
        let my_cont = b
            .ins()
            .load(types::I64, MemFlags::trusted(), frame_ptr, HEADER_SIZE);
        let sid = b.ins().iconst(types::I32, callee_id as i64);
        let sz = b
            .ins()
            .iconst(types::I32, callee_schema.allocation_payload_size() as i64);
        let nf = cx.body(b, jmod, cache).alloc_frame(sid, sz);
        b.ins().store(MemFlags::trusted(), my_cont, nf, HEADER_SIZE);
        cx.body(b, jmod, cache)
            .store_bindings_into_callee_frame(callee_schema, nf, args, 1);
        b.ins().return_(&[nf]);
    }
}

// Term::CallClosure / TailCallClosure lower directly inline: read
// code_ptr through the runtime ABI, then call_indirect through it with
// args, self, and cont. Captures stay inside the closure env and are
// projected by the callee's entry harness.
