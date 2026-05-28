//! Call, return, halt, and frame-slot emission helpers.

use super::*;
use cranelift_codegen::ir::{self, BlockArg, InstBuilder, MemFlags, condcodes::IntCC, types};
use cranelift_frontend::FunctionBuilder;
use fz_runtime::heap::{FieldKind, Schema};
use std::collections::HashMap;

pub(crate) fn emit_halt_for_binding<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    var_env: &HashMap<u32, CodegenValue>,
    cache: &mut CodegenCache,
    var: u32,
    binding: CodegenValue,
) {
    match binding.repr() {
        ArgRepr::RawInt => {
            let fref = jmod.declare_func_in_func(runtime.halt_implicit_i64_id, b.func);
            b.ins().call(fref, &[binding.value()]);
        }
        ArgRepr::RawF64 => {
            let fref = jmod.declare_func_in_func(runtime.halt_implicit_f64_id, b.func);
            b.ins().call(fref, &[binding.value()]);
        }
        ArgRepr::ValueRef | ArgRepr::Condition => {
            let value_ref = tagged_get(cx, var_env, b, jmod, runtime, var, cache);
            let fref = jmod.declare_func_in_func(runtime.halt_implicit_ref_id, b.func);
            b.ins().call(fref, &[value_ref]);
        }
    }
}

pub(crate) fn emit_halt_from_codegen_value<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    cache: &mut CodegenCache,
    value: CodegenValue,
) {
    match value {
        CodegenValue::RawInt(value) => {
            let fref = jmod.declare_func_in_func(runtime.halt_implicit_i64_id, b.func);
            b.ins().call(fref, &[value]);
        }
        CodegenValue::RawF64(value) => {
            let fref = jmod.declare_func_in_func(runtime.halt_implicit_f64_id, b.func);
            b.ins().call(fref, &[value]);
        }
        value => {
            let value_ref = codegen_value_as_any_ref(cx, b, jmod, runtime, cache, value);
            let fref = jmod.declare_func_in_func(runtime.halt_implicit_ref_id, b.func);
            b.ins().call(fref, &[value_ref]);
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
    runtime: &RuntimeRefs,
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
    emit_halt_from_codegen_value(cx, b, jmod, runtime, cache, value);
    b.ins().return_(&[zero]);

    // invoke: write val to cont[24], return cont_ptr.
    b.switch_to_block(invoke_blk);
    b.seal_block(invoke_blk);
    store_frame_value_dynamic(
        cx,
        b,
        jmod,
        runtime,
        cache,
        cont_ptr,
        SLOT_BYTES as u32,
        value,
    );
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
    runtime: &RuntimeRefs,
    cache: &mut CodegenCache,
    value: CodegenValue,
) {
    emit_halt_from_codegen_value(cx, b, jmod, runtime, cache, value);
    let null = b.ins().iconst(types::I64, 0);
    b.ins().return_(&[null]);
}

pub(crate) fn store_frame_value_dynamic<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    cache: &mut CodegenCache,
    frame: ir::Value,
    field_offset: u32,
    value: CodegenValue,
) {
    let value_ref = codegen_value_as_any_ref(cx, b, jmod, runtime, cache, value);
    b.ins()
        .store(MemFlags::trusted(), value_ref, frame, field_offset as i32);
}

/// Term::Call: allocate continuation frame + callee frame. Continuation
/// frame = [my_cont_ptr, result_placeholder, ...captured]. Callee frame =
/// [cont_frame_ptr, ...args]. Return callee frame ptr.
pub(crate) fn emit_call<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    schemas: &[Schema],
    frame_ptr: Option<ir::Value>,
    callee_id: u32,
    args: &[CodegenValue],
    cont: Option<(u32, &[CodegenValue])>,
    cache: &mut CodegenCache,
) {
    let frame_ptr = frame_ptr
        .expect("emit_call reached from native-fn body — natively_callable invariant violated");
    let alloc_fref = jmod.declare_func_in_func(runtime.alloc_id, b.func);

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
            let call_inst = b.ins().call(alloc_fref, &[sid, sz]);
            let cf = b.inst_results(call_inst)[0];
            // Slot 0 (offset 16): cont_ptr = my_cont (my own continuation).
            b.ins().store(MemFlags::trusted(), my_cont, cf, HEADER_SIZE);
            // Slot 1 (offset 24) is the continuation's "result" param —
            // left uninitialized; will be filled by callee's Term::Return.
            // Slots 2..K+2: captured vars in declaration order. Kind-aware
            // store so a typed-int / typed-float captured slot gets its
            // raw payload, not one-word ValueRef.
            store_bindings_into_callee_frame(
                cx,
                b,
                jmod,
                runtime,
                cont_schema,
                cf,
                captured,
                2,
                cache,
            );
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
    let call_inst = b.ins().call(alloc_fref, &[sid, sz]);
    let callee_frame = b.inst_results(call_inst)[0];
    // Slot 0: cont_ptr = cont_frame_val.
    b.ins().store(
        MemFlags::trusted(),
        cont_frame_val,
        callee_frame,
        HEADER_SIZE,
    );
    // Slots 1..N+1: args. Each local binding is written according to the
    // callee frame schema.
    store_bindings_into_callee_frame(
        cx,
        b,
        jmod,
        runtime,
        callee_schema,
        callee_frame,
        args,
        1,
        cache,
    );

    b.ins().return_(&[callee_frame]);
}

pub(crate) fn store_bindings_into_callee_frame<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    callee_schema: &Schema,
    callee_frame: ir::Value,
    args: &[CodegenValue],
    slot_base: usize,
    cache: &mut CodegenCache,
) {
    for (i, binding) in args.iter().copied().enumerate() {
        let slot_idx = slot_base + i;
        let off = HEADER_SIZE + SLOT_BYTES * (slot_idx as i32);
        match callee_schema.fields[slot_idx].kind {
            FieldKind::RawF64 => {
                let f = match binding.repr() {
                    ArgRepr::RawF64 => binding.value(),
                    ArgRepr::ValueRef if binding.known_kind().is_some() => {
                        b.ins()
                            .bitcast(types::F64, MemFlags::new(), binding.value())
                    }
                    _ => tagged_to_raw_f64_unsupported(b, binding.value()),
                };
                b.ins().store(MemFlags::trusted(), f, callee_frame, off);
            }
            FieldKind::RawI64 => {
                let n = match binding.repr() {
                    ArgRepr::RawInt => binding.value(),
                    ArgRepr::ValueRef if binding.known_kind().is_some() => binding.value(),
                    _ => panic!("RawI64 frame slot requires raw int binding"),
                };
                b.ins().store(MemFlags::trusted(), n, callee_frame, off);
            }
            FieldKind::AnyValue => {
                let value_ref = codegen_value_as_any_ref(cx, b, jmod, runtime, cache, binding);
                b.ins()
                    .store(MemFlags::trusted(), value_ref, callee_frame, off);
            }
            FieldKind::RawBytes(_) => {
                b.ins()
                    .store(MemFlags::trusted(), binding.value(), callee_frame, off);
            }
        }
    }
}

pub(crate) fn store_typed_args_into_callee_frame<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    cache: &mut CodegenCache,
    callee_schema: &Schema,
    callee_frame: ir::Value,
    args: &[(ir::Value, ArgRepr)],
    slot_base: usize,
) {
    for (i, &(value, from)) in args.iter().enumerate() {
        let slot_idx = slot_base + i;
        let off = HEADER_SIZE + SLOT_BYTES * (slot_idx as i32);
        match callee_schema.fields[slot_idx].kind {
            FieldKind::RawF64 => {
                let f = match from {
                    ArgRepr::RawF64 => value,
                    _ => tagged_to_raw_f64_unsupported(b, value),
                };
                b.ins().store(MemFlags::trusted(), f, callee_frame, off);
            }
            FieldKind::RawI64 => {
                let n = match from {
                    ArgRepr::RawInt => value,
                    _ => panic!("RawI64 frame slot requires raw int ABI value"),
                };
                b.ins().store(MemFlags::trusted(), n, callee_frame, off);
            }
            FieldKind::AnyValue => {
                let value_ref = match from {
                    ArgRepr::ValueRef => value,
                    ArgRepr::RawInt => emit_raw_int_as_abi_value_ref(cx, b, jmod, runtime, value),
                    ArgRepr::RawF64 => emit_raw_float_as_abi_value_ref(cx, b, jmod, runtime, value),
                    ArgRepr::Condition => {
                        let atom = bool_to_fz(b, cache, value);
                        emit_raw_atom_as_abi_value_ref(cx, b, jmod, runtime, atom)
                    }
                };
                b.ins()
                    .store(MemFlags::trusted(), value_ref, callee_frame, off);
            }
            FieldKind::RawBytes(_) => {
                b.ins().store(MemFlags::trusted(), value, callee_frame, off);
            }
        }
    }
}

/// Term::TailCall: if callee shares schema with caller, overwrite caller's
/// frame in place. Otherwise allocate a new frame. Either way, cont_ptr is
/// preserved (the parent's continuation).
pub(crate) fn emit_tail_call<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
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
        store_bindings_into_callee_frame(
            cx,
            b,
            jmod,
            runtime,
            callee_schema,
            frame_ptr,
            args,
            1,
            cache,
        );
        b.ins().return_(&[frame_ptr]);
    } else {
        // Different schema: alloc fresh, copy cont_ptr, write args.
        let my_cont = b
            .ins()
            .load(types::I64, MemFlags::trusted(), frame_ptr, HEADER_SIZE);
        let alloc_fref = jmod.declare_func_in_func(runtime.alloc_id, b.func);
        let sid = b.ins().iconst(types::I32, callee_id as i64);
        let sz = b
            .ins()
            .iconst(types::I32, callee_schema.allocation_payload_size() as i64);
        let call_inst = b.ins().call(alloc_fref, &[sid, sz]);
        let nf = b.inst_results(call_inst)[0];
        b.ins().store(MemFlags::trusted(), my_cont, nf, HEADER_SIZE);
        store_bindings_into_callee_frame(cx, b, jmod, runtime, callee_schema, nf, args, 1, cache);
        b.ins().return_(&[nf]);
    }
}

// Term::CallClosure / TailCallClosure lower directly inline: read
// code_ptr through the runtime ABI, then call_indirect through it with
// args, self, and cont. Captures stay inside the closure env and are
// projected by the callee's entry harness.
