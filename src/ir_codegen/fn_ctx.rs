//! Per-function semantic codegen context.
//!
//! Cranelift's `FunctionBuilder` owns the body currently being emitted.
//! Function-local imports, however, need both the module and the function
//! body. `CodegenFn` is the fz-owned boundary for "lower one fz function":
//! semantic lowering code should ask this context for operations, while
//! runtime helper calls remain an implementation detail behind those methods.

use super::*;
use cranelift_codegen::ir::{self, BlockArg, InstBuilder, MemFlags, condcodes::IntCC, types};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::FuncId;
use fz_runtime::heap::{FieldKind, Schema};
use std::collections::HashMap;

pub(crate) struct CodegenFn<'env> {
    runtime: &'env RuntimeRefs,
    imports: HashMap<FuncId, ir::FuncRef>,
}

pub(crate) struct CodegenFnBody<'a, 'env, 'fb, M>
where
    M: cranelift_module::Module,
{
    pub(super) cx: &'a mut CodegenFn<'env>,
    pub(super) b: &'a mut FunctionBuilder<'fb>,
    pub(super) jmod: &'a mut M,
    pub(super) cache: &'a mut CodegenCache,
}

pub(crate) struct CodegenFnSite<'a, 'env, 'fb, M>
where
    M: cranelift_module::Module,
{
    cx: &'a mut CodegenFn<'env>,
    b: &'a mut FunctionBuilder<'fb>,
    jmod: &'a mut M,
}

impl<'env> CodegenFn<'env> {
    pub(crate) fn new(env: &'env CodegenEnv<'_>) -> Self {
        Self {
            runtime: env.runtime,
            imports: HashMap::new(),
        }
    }

    /// Build a semantic context for generated runtime shim bodies, which
    /// have runtime refs but no fz `CodegenEnv`.
    pub(crate) fn for_runtime_shim(runtime: &'env RuntimeRefs) -> Self {
        Self {
            runtime,
            imports: HashMap::new(),
        }
    }

    pub(crate) fn body<'a, 'fb, M: cranelift_module::Module>(
        &'a mut self,
        b: &'a mut FunctionBuilder<'fb>,
        jmod: &'a mut M,
        cache: &'a mut CodegenCache,
    ) -> CodegenFnBody<'a, 'env, 'fb, M> {
        CodegenFnBody {
            cx: self,
            b,
            jmod,
            cache,
        }
    }

    pub(crate) fn site<'a, 'fb, M: cranelift_module::Module>(
        &'a mut self,
        b: &'a mut FunctionBuilder<'fb>,
        jmod: &'a mut M,
    ) -> CodegenFnSite<'a, 'env, 'fb, M> {
        CodegenFnSite { cx: self, b, jmod }
    }

    pub(crate) fn func_ref<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        id: FuncId,
    ) -> ir::FuncRef {
        *self
            .imports
            .entry(id)
            .or_insert_with(|| jmod.declare_func_in_func(id, b.func))
    }
}

/// One fz function body's call sites share a `CodegenFn` (runtime refs +
/// the function-local import table), a `FunctionBuilder`, and a module.
/// `CallSite` is the single home for the runtime-BIF operations they emit:
/// a view exposes `(cx, b, jmod)` via `parts`, and every operation is a
/// default method built on `call`/`call1`. Implementors only wire `parts`;
/// the operations are defined once here rather than mirrored per view.
pub(crate) trait CallSite<'env, 'fb, M: cranelift_module::Module> {
    fn parts(&mut self) -> (&mut CodegenFn<'env>, &mut FunctionBuilder<'fb>, &mut M);

    fn call(&mut self, id: FuncId, args: &[ir::Value]) -> ir::Inst {
        let (cx, b, jmod) = self.parts();
        let fref = cx.func_ref(b, jmod, id);
        b.ins().call(fref, args)
    }

    fn call1(&mut self, id: FuncId, args: &[ir::Value]) -> ir::Value {
        let inst = self.call(id, args);
        self.parts().1.inst_results(inst)[0]
    }

    fn ref_tag(&mut self, value_ref: ir::Value) -> ir::Value {
        let id = self.parts().0.runtime.type_of_id;
        self.call1(id, &[value_ref])
    }

    fn truthy_ref(&mut self, value_ref: ir::Value) -> ir::Value {
        let id = self.parts().0.runtime.truthy_ref_id;
        self.call1(id, &[value_ref])
    }

    fn mark_published_ref_aliased(&mut self, value_ref: ir::Value) -> ir::Value {
        let id = self.parts().0.runtime.mark_published_ref_aliased_id;
        self.call1(id, &[value_ref])
    }

    fn box_int_for_any(&mut self, raw: ir::Value) -> ir::Value {
        let id = self.parts().0.runtime.box_int_for_any_id;
        self.call1(id, &[raw])
    }

    fn box_float_for_any(&mut self, raw: ir::Value) -> ir::Value {
        let id = self.parts().0.runtime.box_float_for_any_id;
        self.call1(id, &[raw])
    }

    fn box_atom_for_any(&mut self, raw: ir::Value) -> ir::Value {
        let id = self.parts().0.runtime.box_atom_for_any_id;
        self.call1(id, &[raw])
    }

    fn unbox_int(&mut self, value_ref: ir::Value) -> ir::Value {
        let id = self.parts().0.runtime.unbox_int_id;
        self.call1(id, &[value_ref])
    }

    fn unbox_float(&mut self, value_ref: ir::Value) -> ir::Value {
        let id = self.parts().0.runtime.unbox_float_id;
        self.call1(id, &[value_ref])
    }

    fn unbox_atom(&mut self, value_ref: ir::Value) -> ir::Value {
        let id = self.parts().0.runtime.unbox_atom_id;
        self.call1(id, &[value_ref])
    }

    fn halt_implicit(&mut self, repr: ArgRepr, value: ir::Value) {
        let id = match repr {
            ArgRepr::RawInt => self.parts().0.runtime.halt_implicit_i64_id,
            ArgRepr::RawF64 => self.parts().0.runtime.halt_implicit_f64_id,
            ArgRepr::ValueRef => self.parts().0.runtime.halt_implicit_ref_id,
            ArgRepr::Condition => unreachable!("condition halt values must be materialized"),
        };
        self.call(id, &[value]);
    }

    fn alloc_frame(&mut self, schema_id: ir::Value, size: ir::Value) -> ir::Value {
        let id = self.parts().0.runtime.alloc_id;
        self.call1(id, &[schema_id, size])
    }

    fn get_halt_cont(&mut self, body_addr: ir::Value, halt_kind: ir::Value) -> ir::Value {
        let id = self.parts().0.runtime.get_halt_cont_id;
        self.call1(id, &[body_addr, halt_kind])
    }

    fn alloc_closure(
        &mut self,
        func_id: ir::Value,
        captured_count: ir::Value,
        halt_kind: ir::Value,
        code_addr: ir::Value,
    ) -> ir::Value {
        let id = self.parts().0.runtime.alloc_closure_id;
        self.call1(id, &[func_id, captured_count, halt_kind, code_addr])
    }

    fn list_cons_with(&mut self, cons_id: FuncId, args: &[ir::Value]) -> ir::Value {
        self.call1(cons_id, args)
    }

    fn list_head(&mut self, list_ref: ir::Value) -> ir::Value {
        let id = self.parts().0.runtime.list_head_fallback_id;
        self.call1(id, &[list_ref])
    }

    fn list_head_int(&mut self, list_ref: ir::Value) -> ir::Value {
        let id = self.parts().0.runtime.list_head_int_ref_id;
        self.call1(id, &[list_ref])
    }

    fn list_head_float(&mut self, list_ref: ir::Value) -> ir::Value {
        let id = self.parts().0.runtime.list_head_float_ref_id;
        self.call1(id, &[list_ref])
    }

    fn list_tail(&mut self, list_ref: ir::Value) -> ir::Value {
        let id = self.parts().0.runtime.list_tail_fallback_id;
        self.call1(id, &[list_ref])
    }

    fn list_reuse_or_cons_tail_ref(
        &mut self,
        source_ref: ir::Value,
        tail_ref: ir::Value,
    ) -> ir::Value {
        let id = self.parts().0.runtime.list_reuse_or_cons_tail_ref_id;
        self.call1(id, &[source_ref, tail_ref])
    }

    fn closure_capture_i64(&mut self, closure_ref: ir::Value, index: ir::Value) -> ir::Value {
        let id = self.parts().0.runtime.closure_get_capture_i64_id;
        self.call1(id, &[closure_ref, index])
    }

    fn closure_capture_f64(&mut self, closure_ref: ir::Value, index: ir::Value) -> ir::Value {
        let id = self.parts().0.runtime.closure_get_capture_f64_id;
        self.call1(id, &[closure_ref, index])
    }

    fn closure_capture_ref(&mut self, closure_ref: ir::Value, index: ir::Value) -> ir::Value {
        let id = self.parts().0.runtime.closure_get_capture_ref_id;
        self.call1(id, &[closure_ref, index])
    }

    fn closure_code_ref(&mut self, closure_ref: ir::Value) -> ir::Value {
        let id = self.parts().0.runtime.closure_code_ref_id;
        self.call1(id, &[closure_ref])
    }

    fn closure_halt_kind_ref(&mut self, closure_ref: ir::Value) -> ir::Value {
        let id = self.parts().0.runtime.closure_halt_kind_ref_id;
        self.call1(id, &[closure_ref])
    }

    fn set_closure_capture_ref(
        &mut self,
        closure_ref: ir::Value,
        index: ir::Value,
        value: ir::Value,
    ) {
        let id = self.parts().0.runtime.closure_set_capture_ref_id;
        self.call(id, &[closure_ref, index, value]);
    }

    fn set_closure_capture_i64(
        &mut self,
        closure_ref: ir::Value,
        index: ir::Value,
        value: ir::Value,
    ) {
        let id = self.parts().0.runtime.closure_set_capture_i64_id;
        self.call(id, &[closure_ref, index, value]);
    }

    fn set_closure_capture_f64(
        &mut self,
        closure_ref: ir::Value,
        index: ir::Value,
        value: ir::Value,
    ) {
        let id = self.parts().0.runtime.closure_set_capture_f64_id;
        self.call(id, &[closure_ref, index, value]);
    }

    fn materialize_cont(&mut self, value: ir::Value) -> ir::Value {
        let id = self.parts().0.runtime.materialize_cont_id;
        self.call1(id, &[value])
    }

    fn struct_set_field_int(
        &mut self,
        struct_bits: ir::Value,
        offset: ir::Value,
        value: ir::Value,
    ) {
        let id = self.parts().0.runtime.struct_set_field_int_id;
        self.call(id, &[struct_bits, offset, value]);
    }

    fn struct_set_field_float(
        &mut self,
        struct_bits: ir::Value,
        offset: ir::Value,
        value: ir::Value,
    ) {
        let id = self.parts().0.runtime.struct_set_field_float_id;
        self.call(id, &[struct_bits, offset, value]);
    }

    fn struct_set_field_atom(
        &mut self,
        struct_bits: ir::Value,
        offset: ir::Value,
        value: ir::Value,
    ) {
        let id = self.parts().0.runtime.struct_set_field_atom_id;
        self.call(id, &[struct_bits, offset, value]);
    }

    fn struct_set_field_ref(
        &mut self,
        struct_bits: ir::Value,
        offset: ir::Value,
        value: ir::Value,
    ) {
        let id = self.parts().0.runtime.struct_set_field_ref_id;
        self.call(id, &[struct_bits, offset, value]);
    }

    // -- value classification reads (cache-free) --

    fn value_truthy(&mut self, value: CodegenValue) -> ir::Value {
        use fz_runtime::any_value::ValueKind;
        if let CodegenValue::AnyRef(value_ref) = value {
            return self.truthy_ref(value_ref);
        }
        let (_, b, _) = self.parts();
        match value {
            CodegenValue::Condition(flag) => flag,
            CodegenValue::RawInt(_) | CodegenValue::RawF64(_) => b.ins().iconst(types::I8, 1),
            CodegenValue::Known {
                kind: ValueKind::NULL,
                ..
            } => b.ins().iconst(types::I8, 0),
            CodegenValue::Known {
                payload,
                kind: ValueKind::ATOM,
            } => {
                let is_false = b.ins().icmp_imm(
                    IntCC::Equal,
                    payload,
                    fz_runtime::any_value::FALSE_ATOM_ID as i64,
                );
                let is_nil = b.ins().icmp_imm(
                    IntCC::Equal,
                    payload,
                    fz_runtime::any_value::NIL_ATOM_ID as i64,
                );
                let falsey = b.ins().bor(is_false, is_nil);
                b.ins().bxor_imm(falsey, 1)
            }
            CodegenValue::Known { .. } => b.ins().iconst(types::I8, 1),
            CodegenValue::AnyRef(_) => unreachable!("handled above"),
        }
    }

    fn value_type_tag(&mut self, value: CodegenValue) -> ir::Value {
        use fz_runtime::any_value::ValueKind;
        if let CodegenValue::AnyRef(value_ref) = value {
            return self.ref_tag(value_ref);
        }
        let (_, b, _) = self.parts();
        match value {
            CodegenValue::RawInt(_) => b.ins().iconst(types::I8, ValueKind::INT.tag() as i64),
            CodegenValue::RawF64(_) => b.ins().iconst(types::I8, ValueKind::FLOAT.tag() as i64),
            CodegenValue::Condition(_) => b.ins().iconst(types::I8, ValueKind::ATOM.tag() as i64),
            CodegenValue::Known { payload, kind } => known_kind_ref_tag(b, payload, kind),
            CodegenValue::AnyRef(_) => unreachable!("handled above"),
        }
    }

    fn value_is_tag(
        &mut self,
        value: CodegenValue,
        tag: fz_runtime::any_value::ValueKind,
    ) -> ir::Value {
        let actual = self.value_type_tag(value);
        let (_, b, _) = self.parts();
        b.ins().icmp_imm(IntCC::Equal, actual, tag.tag() as i64)
    }

    fn value_atom_id_is(&mut self, value: CodegenValue, atom_id: u32) -> ir::Value {
        use fz_runtime::any_value::ValueKind;
        if let CodegenValue::AnyRef(value_ref) = value {
            // The AnyRef path interleaves block-building with an unbox BIF, so
            // each builder burst is scoped to release the borrow around the
            // `unbox_atom` call (which needs `&mut self`).
            let is_atom = self.value_is_tag(value, ValueKind::ATOM);
            let join_blk = {
                let (_, b, _) = self.parts();
                let atom_blk = b.create_block();
                let join_blk = b.create_block();
                b.append_block_param(join_blk, types::I8);
                let false8 = b.ins().iconst(types::I8, 0);
                let no_args: Vec<BlockArg> = Vec::new();
                b.ins().brif(
                    is_atom,
                    atom_blk,
                    &no_args,
                    join_blk,
                    &[BlockArg::Value(false8)],
                );
                b.switch_to_block(atom_blk);
                b.seal_block(atom_blk);
                join_blk
            };
            let atom = self.unbox_atom(value_ref);
            let (_, b, _) = self.parts();
            let found = b.ins().icmp_imm(IntCC::Equal, atom, atom_id as i64);
            b.ins().jump(join_blk, &[BlockArg::Value(found)]);
            b.switch_to_block(join_blk);
            b.seal_block(join_blk);
            return b.block_params(join_blk)[0];
        }
        let (_, b, _) = self.parts();
        match value {
            CodegenValue::Condition(flag) => {
                if atom_id == fz_runtime::any_value::TRUE_ATOM_ID {
                    return flag;
                }
                if atom_id == fz_runtime::any_value::FALSE_ATOM_ID {
                    return b.ins().bxor_imm(flag, 1);
                }
                b.ins().iconst(types::I8, 0)
            }
            CodegenValue::RawInt(_) | CodegenValue::RawF64(_) => b.ins().iconst(types::I8, 0),
            CodegenValue::Known {
                payload,
                kind: ValueKind::ATOM,
            } => b.ins().icmp_imm(IntCC::Equal, payload, atom_id as i64),
            CodegenValue::Known { .. } => b.ins().iconst(types::I8, 0),
            CodegenValue::AnyRef(_) => unreachable!("handled above"),
        }
    }

    fn value_raw_int(&mut self, value: CodegenValue) -> ir::Value {
        match value {
            CodegenValue::RawInt(value) => value,
            CodegenValue::Known {
                payload,
                kind: fz_runtime::any_value::ValueKind::INT,
            } => payload,
            CodegenValue::AnyRef(value_ref) => self.unbox_int(value_ref),
            _ => panic!("CodegenValue is not an int"),
        }
    }

    fn value_raw_float(&mut self, value: CodegenValue) -> ir::Value {
        match value {
            CodegenValue::RawF64(value) => value,
            CodegenValue::Known {
                payload,
                kind: fz_runtime::any_value::ValueKind::FLOAT,
            } => {
                let (_, b, _) = self.parts();
                b.ins().bitcast(types::F64, MemFlags::new(), payload)
            }
            CodegenValue::AnyRef(value_ref) => self.unbox_float(value_ref),
            _ => panic!("CodegenValue is not a float"),
        }
    }

    // -- ABI boxing / representation coercion (cache-free) --

    fn box_known_non_heap(
        &mut self,
        raw: ir::Value,
        kind: fz_runtime::any_value::ValueKind,
    ) -> ir::Value {
        use fz_runtime::any_value::ValueKind;
        if kind == ValueKind::INT {
            return self.box_int_for_any(raw);
        }
        if kind == ValueKind::FLOAT {
            let raw = {
                let (_, b, _) = self.parts();
                b.ins().bitcast(types::F64, MemFlags::new(), raw)
            };
            return self.box_float_for_any(raw);
        }
        if kind == ValueKind::ATOM {
            return self.box_atom_for_any(raw);
        }
        let (_, b, _) = self.parts();
        if kind == ValueKind::NULL {
            return b.ins().iconst(types::I64, 0);
        }
        if kind == ValueKind::LIST {
            let _ = raw;
            let word = fz_runtime::any_value::AnyValueRef::empty_list().raw_word();
            return b.ins().iconst(types::I64, word as i64);
        }
        unreachable!("heap refs must stay as CodegenValue::AnyRef")
    }

    fn coerce_binding_to(&mut self, binding: CodegenValue, to: ArgRepr) -> ir::Value {
        match (binding, to) {
            (CodegenValue::Known { payload, kind }, ArgRepr::ValueRef) => {
                self.box_known_non_heap(payload, kind)
            }
            (CodegenValue::Known { payload, .. }, ArgRepr::RawInt) => payload,
            (CodegenValue::Known { payload, .. }, ArgRepr::RawF64) => {
                let (_, b, _) = self.parts();
                b.ins().bitcast(types::F64, MemFlags::new(), payload)
            }
            (CodegenValue::Known { .. }, ArgRepr::Condition) => {
                unreachable!("condition is never a callee ABI target")
            }
            (CodegenValue::AnyRef(value), ArgRepr::ValueRef) => value,
            (CodegenValue::AnyRef(value), ArgRepr::RawInt) => self.unbox_int(value),
            (CodegenValue::AnyRef(value), ArgRepr::RawF64) => self.unbox_float(value),
            (CodegenValue::AnyRef(_), ArgRepr::Condition) => {
                unreachable!("condition is never a callee ABI target")
            }
            (CodegenValue::RawInt(value), ArgRepr::ValueRef) => self.box_int_for_any(value),
            (CodegenValue::RawF64(value), ArgRepr::ValueRef) => self.box_float_for_any(value),
            (CodegenValue::Condition(value), ArgRepr::ValueRef) => {
                let atom = {
                    let (_, b, _) = self.parts();
                    let true_v = b
                        .ins()
                        .iconst(types::I64, fz_runtime::any_value::TRUE_BITS as i64);
                    let false_v = b
                        .ins()
                        .iconst(types::I64, fz_runtime::any_value::FALSE_BITS as i64);
                    b.ins().select(value, true_v, false_v)
                };
                self.box_atom_for_any(atom)
            }
            (binding, to) => {
                if binding.repr() == to {
                    binding.value()
                } else {
                    self.coerce_to(binding.value(), binding.repr(), to)
                }
            }
        }
    }

    fn coerce_to(&mut self, val: ir::Value, from: ArgRepr, to: ArgRepr) -> ir::Value {
        if from == to {
            return val;
        }
        match (from, to) {
            (ArgRepr::ValueRef, ArgRepr::RawInt) => val,
            (ArgRepr::ValueRef, ArgRepr::RawF64) => {
                let (_, b, _) = self.parts();
                tagged_to_raw_f64_unsupported(b, val)
            }
            (ArgRepr::RawInt, ArgRepr::ValueRef) => self.box_int_for_any(val),
            (ArgRepr::RawF64, ArgRepr::ValueRef) => self.box_float_for_any(val),
            (ArgRepr::RawInt, ArgRepr::RawF64) => {
                let (_, b, _) = self.parts();
                b.ins().fcvt_from_sint(types::F64, val)
            }
            (ArgRepr::RawF64, ArgRepr::RawInt) => {
                let (_, b, _) = self.parts();
                b.ins().fcvt_to_sint(types::I64, val)
            }
            (ArgRepr::Condition, _) | (_, ArgRepr::Condition) => {
                unreachable!("Condition vars are never coerced")
            }
            (ArgRepr::ValueRef, ArgRepr::ValueRef)
            | (ArgRepr::RawInt, ArgRepr::RawInt)
            | (ArgRepr::RawF64, ArgRepr::RawF64) => {
                unreachable!("same-repr coerce: handled by early return")
            }
        }
    }

    // -- var-keyed raw extraction (cache-free) --

    fn as_raw_i64(&mut self, var_env: &HashMap<u32, CodegenValue>, v: u32) -> ir::Value {
        match *var_env.get(&v).expect("unbound var") {
            CodegenValue::RawInt(value) => value,
            CodegenValue::Known { payload, .. } => payload,
            CodegenValue::AnyRef(value_ref) => self.unbox_int(value_ref),
            _ => panic!("cannot read raw i64 from non-integer value"),
        }
    }

    fn as_raw_f64(&mut self, var_env: &HashMap<u32, CodegenValue>, v: u32) -> ir::Value {
        match *var_env.get(&v).expect("unbound var") {
            CodegenValue::RawF64(value) => value,
            CodegenValue::Known { payload, .. } => {
                let (_, b, _) = self.parts();
                b.ins().bitcast(types::F64, MemFlags::new(), payload)
            }
            CodegenValue::AnyRef(value_ref) => self.unbox_float(value_ref),
            other => {
                let (_, b, _) = self.parts();
                tagged_to_raw_f64_unsupported(b, other.value())
            }
        }
    }

    // -- closure capture access by usize index (cache-free) --

    fn index_const(&mut self, idx: usize) -> ir::Value {
        let (_, b, _) = self.parts();
        b.ins().iconst(types::I64, idx as i64)
    }

    fn closure_capture_i64_at(&mut self, closure_ref: ir::Value, idx: usize) -> ir::Value {
        let index = self.index_const(idx);
        self.closure_capture_i64(closure_ref, index)
    }

    fn closure_capture_f64_at(&mut self, closure_ref: ir::Value, idx: usize) -> ir::Value {
        let index = self.index_const(idx);
        self.closure_capture_f64(closure_ref, index)
    }

    fn closure_capture_ref_at(&mut self, closure_ref: ir::Value, idx: usize) -> ir::Value {
        let index = self.index_const(idx);
        self.closure_capture_ref(closure_ref, index)
    }

    fn closure_capture_as_binding(
        &mut self,
        closure_ref: ir::Value,
        idx: usize,
        repr: ArgRepr,
    ) -> CodegenValue {
        match repr {
            ArgRepr::RawInt => {
                CodegenValue::from_abi_value(self.closure_capture_i64_at(closure_ref, idx), repr)
            }
            ArgRepr::RawF64 => {
                CodegenValue::from_abi_value(self.closure_capture_f64_at(closure_ref, idx), repr)
            }
            ArgRepr::ValueRef => {
                CodegenValue::any_ref(self.closure_capture_ref_at(closure_ref, idx))
            }
            ArgRepr::Condition => unreachable!("closure captures are never condition-only"),
        }
    }

    fn outer_cont_ref(&mut self, closure_ref: ir::Value) -> ir::Value {
        self.closure_capture_ref_at(closure_ref, 0)
    }

    fn store_closure_capture_ref_word(
        &mut self,
        closure_ref: ir::Value,
        idx: usize,
        value: ir::Value,
    ) {
        let value = self.mark_published_ref_aliased(value);
        let index = self.index_const(idx);
        self.set_closure_capture_ref(closure_ref, index, value);
    }

    fn store_closure_capture_i64(&mut self, closure_ref: ir::Value, idx: usize, value: ir::Value) {
        let index = self.index_const(idx);
        self.set_closure_capture_i64(closure_ref, index, value);
    }

    fn store_closure_capture_f64(&mut self, closure_ref: ir::Value, idx: usize, value: ir::Value) {
        let index = self.index_const(idx);
        self.set_closure_capture_f64(closure_ref, index, value);
    }
}

impl<'a, 'env, 'fb, M: cranelift_module::Module> CallSite<'env, 'fb, M>
    for CodegenFnBody<'a, 'env, 'fb, M>
{
    fn parts(&mut self) -> (&mut CodegenFn<'env>, &mut FunctionBuilder<'fb>, &mut M) {
        (&mut *self.cx, &mut *self.b, &mut *self.jmod)
    }
}

impl<'a, 'env, 'fb, M: cranelift_module::Module> CallSite<'env, 'fb, M>
    for CodegenFnSite<'a, 'env, 'fb, M>
{
    fn parts(&mut self) -> (&mut CodegenFn<'env>, &mut FunctionBuilder<'fb>, &mut M) {
        (&mut *self.cx, &mut *self.b, &mut *self.jmod)
    }
}

impl<M> CodegenFnBody<'_, '_, '_, M>
where
    M: cranelift_module::Module,
{
    /// Materialize a value as an ABI `AnyValueRef` word. Cache-bearing:
    /// the `Condition` lane interns its `bool_to_fz` atom.
    pub(crate) fn value_as_any_ref(&mut self, value: CodegenValue) -> ir::Value {
        match value {
            CodegenValue::AnyRef(value) => value,
            CodegenValue::RawInt(value) => self.box_int_for_any(value),
            CodegenValue::RawF64(value) => self.box_float_for_any(value),
            CodegenValue::Condition(value) => {
                let atom = bool_to_fz(self.b, self.cache, value);
                self.box_atom_for_any(atom)
            }
            CodegenValue::Known { payload, kind } => self.box_known_non_heap(payload, kind),
        }
    }

    /// Materialize the var's binding as an ABI `AnyValueRef`, reusing a
    /// cached `iconst` for known raw-int constants.
    pub(crate) fn tagged_var(
        &mut self,
        var_env: &HashMap<u32, CodegenValue>,
        var: u32,
    ) -> ir::Value {
        match *var_env.get(&var).expect("unbound var") {
            CodegenValue::RawF64(value) => self.box_float_for_any(value),
            CodegenValue::RawInt(value) => {
                let raw = if let Some(&n) = self.cache.raw_int_consts.get(&var) {
                    cached_iconst(self.b, self.cache, n)
                } else {
                    value
                };
                self.box_int_for_any(raw)
            }
            CodegenValue::Known { payload, kind } => self.box_known_non_heap(payload, kind),
            CodegenValue::AnyRef(value) => value,
            CodegenValue::Condition(value) => {
                let atom = bool_to_fz(self.b, self.cache, value);
                self.box_atom_for_any(atom)
            }
        }
    }

    pub(crate) fn value_raw_atom(&mut self, value: CodegenValue) -> ir::Value {
        match value {
            CodegenValue::Condition(flag) => bool_to_fz(self.b, self.cache, flag),
            CodegenValue::Known {
                payload,
                kind: fz_runtime::any_value::ValueKind::ATOM,
            } => payload,
            CodegenValue::AnyRef(value_ref) => self.unbox_atom(value_ref),
            _ => panic!("CodegenValue is not an atom"),
        }
    }

    pub(crate) fn any_ref_for_var(
        &mut self,
        var_env: &HashMap<u32, CodegenValue>,
        var: u32,
    ) -> ir::Value {
        let binding = *var_env.get(&var).expect("unbound var");
        self.value_as_any_ref(binding)
    }

    /// Coerce a goto block argument to the repr its target param needs,
    /// returning the rebound value when it changes and `None` when the
    /// binding already matches.
    pub(crate) fn coerce_goto_arg(
        &mut self,
        vb: CodegenValue,
        want: ArgRepr,
    ) -> Option<CodegenValue> {
        if want == ArgRepr::ValueRef {
            Some(CodegenValue::any_ref(self.value_as_any_ref(vb)))
        } else if vb.repr() != want {
            Some(CodegenValue::from_abi_value(
                self.coerce_binding_to(vb, want),
                want,
            ))
        } else {
            None
        }
    }

    /// Empty-list ABI word, cached per function body.
    pub(crate) fn empty_list_ref(&mut self) -> ir::Value {
        emit_empty_list_value_ref_word(self.b, self.cache)
    }

    pub(crate) fn list_tail_ref_word(&mut self, tail: ListTailBits) -> ir::Value {
        match tail {
            ListTailBits::Empty => self.empty_list_ref(),
            ListTailBits::ValueRef(value) | ListTailBits::NonEmptyValueRef(value) => value,
        }
    }

    pub(crate) fn owned_cons_reuse_source(
        &self,
        head: crate::fz_ir::Var,
    ) -> Option<crate::fz_ir::Var> {
        self.cache.owned_cons_reuse_sources.get(&head.0).copied()
    }

    pub(crate) fn store_frame_value_dynamic(
        &mut self,
        frame: ir::Value,
        field_offset: u32,
        value: CodegenValue,
    ) {
        let value_ref = self.value_as_any_ref(value);
        self.b
            .ins()
            .store(MemFlags::trusted(), value_ref, frame, field_offset as i32);
    }

    pub(crate) fn store_frame_word(
        &mut self,
        frame: ir::Value,
        field_offset: u32,
        value: ir::Value,
    ) {
        self.b
            .ins()
            .store(MemFlags::trusted(), value, frame, field_offset as i32);
    }

    pub(crate) fn store_bindings_into_callee_frame(
        &mut self,
        callee_schema: &Schema,
        callee_frame: ir::Value,
        args: &[CodegenValue],
        slot_base: usize,
    ) {
        for (i, binding) in args.iter().copied().enumerate() {
            let slot_idx = slot_base + i;
            let off = HEADER_SIZE + SLOT_BYTES * (slot_idx as i32);
            match callee_schema.fields[slot_idx].kind {
                FieldKind::RawF64 => {
                    let f = match binding.repr() {
                        ArgRepr::RawF64 => binding.value(),
                        ArgRepr::ValueRef if binding.known_kind().is_some() => self
                            .b
                            .ins()
                            .bitcast(types::F64, MemFlags::new(), binding.value()),
                        _ => tagged_to_raw_f64_unsupported(self.b, binding.value()),
                    };
                    self.b
                        .ins()
                        .store(MemFlags::trusted(), f, callee_frame, off);
                }
                FieldKind::RawI64 => {
                    let n = match binding.repr() {
                        ArgRepr::RawInt => binding.value(),
                        ArgRepr::ValueRef if binding.known_kind().is_some() => binding.value(),
                        _ => panic!("RawI64 frame slot requires raw int binding"),
                    };
                    self.b
                        .ins()
                        .store(MemFlags::trusted(), n, callee_frame, off);
                }
                FieldKind::AnyValue => {
                    let value_ref = self.value_as_any_ref(binding);
                    self.b
                        .ins()
                        .store(MemFlags::trusted(), value_ref, callee_frame, off);
                }
                FieldKind::RawBytes(_) => {
                    self.b
                        .ins()
                        .store(MemFlags::trusted(), binding.value(), callee_frame, off);
                }
            }
        }
    }

    pub(crate) fn store_typed_args_into_callee_frame(
        &mut self,
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
                        _ => tagged_to_raw_f64_unsupported(self.b, value),
                    };
                    self.b
                        .ins()
                        .store(MemFlags::trusted(), f, callee_frame, off);
                }
                FieldKind::RawI64 => {
                    let n = match from {
                        ArgRepr::RawInt => value,
                        _ => panic!("RawI64 frame slot requires raw int ABI value"),
                    };
                    self.b
                        .ins()
                        .store(MemFlags::trusted(), n, callee_frame, off);
                }
                FieldKind::AnyValue => {
                    let value_ref = match from {
                        ArgRepr::ValueRef => value,
                        ArgRepr::RawInt => self.box_int_for_any(value),
                        ArgRepr::RawF64 => self.box_float_for_any(value),
                        ArgRepr::Condition => {
                            let atom = bool_to_fz(self.b, self.cache, value);
                            self.box_atom_for_any(atom)
                        }
                    };
                    self.b
                        .ins()
                        .store(MemFlags::trusted(), value_ref, callee_frame, off);
                }
                FieldKind::RawBytes(_) => {
                    self.b
                        .ins()
                        .store(MemFlags::trusted(), value, callee_frame, off);
                }
            }
        }
    }

    pub(crate) fn coerce_call_args(
        &mut self,
        args: &[crate::fz_ir::Var],
        callee_param_reprs: &[ArgRepr],
        var_env: &HashMap<u32, CodegenValue>,
    ) -> Vec<ir::Value> {
        let mut out = Vec::with_capacity(args.len() + 1);
        for (i, av) in args.iter().enumerate() {
            let binding = *var_env.get(&av.0).expect("unbound call arg");
            self.push_binding_as_abi_arg(&mut out, binding, callee_param_reprs[i]);
        }
        out
    }

    pub(crate) fn push_binding_as_abi_arg(
        &mut self,
        out: &mut Vec<ir::Value>,
        binding: CodegenValue,
        to: ArgRepr,
    ) {
        if to == ArgRepr::ValueRef {
            let value_ref = match binding {
                CodegenValue::RawInt(value) => self.box_int_for_any(value),
                CodegenValue::RawF64(value) => self.box_float_for_any(value),
                CodegenValue::Condition(value) => {
                    let atom = bool_to_fz(self.b, self.cache, value);
                    self.box_atom_for_any(atom)
                }
                CodegenValue::AnyRef(value) => value,
                CodegenValue::Known { payload, kind } => self.box_known_non_heap(payload, kind),
            };
            out.push(value_ref);
        } else {
            out.push(self.coerce_binding_to(binding, to));
        }
    }

    /// Write `value` into field `field_idx` of the struct/tuple at
    /// `struct_bits`, picking the typed setter for the value's
    /// representation. Heap refs are published before the store.
    pub(crate) fn struct_set_field(
        &mut self,
        struct_bits: ir::Value,
        field_idx: usize,
        value: CodegenValue,
    ) {
        let offset = self
            .b
            .ins()
            .iconst(types::I32, (field_idx as i64) * SLOT_BYTES as i64);
        match value {
            CodegenValue::RawInt(raw)
            | CodegenValue::Known {
                payload: raw,
                kind: fz_runtime::any_value::ValueKind::INT,
            } => {
                self.struct_set_field_int(struct_bits, offset, raw);
            }
            CodegenValue::RawF64(raw) => {
                self.struct_set_field_float(struct_bits, offset, raw);
            }
            CodegenValue::Known {
                payload,
                kind: fz_runtime::any_value::ValueKind::FLOAT,
            } => {
                let raw = self.b.ins().bitcast(types::F64, MemFlags::new(), payload);
                self.struct_set_field_float(struct_bits, offset, raw);
            }
            CodegenValue::Known {
                payload,
                kind: fz_runtime::any_value::ValueKind::ATOM,
            } => {
                self.struct_set_field_atom(struct_bits, offset, payload);
            }
            other => {
                let value_ref = self.value_as_any_ref(other);
                let value_ref = self.mark_published_ref_aliased(value_ref);
                self.struct_set_field_ref(struct_bits, offset, value_ref);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelift_codegen::ir::AbiParam;
    use cranelift_codegen::settings;
    use cranelift_frontend::FunctionBuilderContext;
    use cranelift_jit::{JITBuilder, JITModule};
    use cranelift_module::{Linkage, Module};

    fn jit_module() -> JITModule {
        let flags = settings::Flags::new(settings::builder());
        let isa = cranelift_native::builder()
            .expect("host isa")
            .finish(flags)
            .expect("finish isa");
        JITModule::new(JITBuilder::with_isa(
            isa,
            cranelift_module::default_libcall_names(),
        ))
    }

    #[test]
    fn codegen_fn_reuses_func_ref_per_function() {
        let mut module = jit_module();
        let runtime = declare_runtime_symbols(&mut module).expect("declare runtime");
        let mut sig = module.make_signature();
        sig.returns.push(AbiParam::new(types::I64));
        let callee = module
            .declare_function("fz_import_test_callee", Linkage::Import, &sig)
            .expect("declare import");

        let mut ctx = module.make_context();
        ctx.func.signature = module.make_signature();
        let mut fbctx = FunctionBuilderContext::new();
        let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);

        let mut cx = CodegenFn::for_runtime_shim(&runtime);
        let first = cx.func_ref(&mut b, &mut module, callee);
        let second = cx.func_ref(&mut b, &mut module, callee);

        assert_eq!(first, second);
        b.finalize();
    }
}
