//! Per-function semantic codegen context.
//!
//! Cranelift's `FunctionBuilder` owns the body currently being emitted.
//! Function-local imports, however, need both the module and the function
//! body. `CodegenFn` is the fz-owned boundary for "lower one fz function":
//! semantic lowering code should ask this context for operations, while
//! runtime helper calls remain an implementation detail behind those methods.

use super::*;
use cranelift_codegen::ir::{self, InstBuilder, MemFlags, types};
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

    fn call_func<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        id: FuncId,
        args: &[ir::Value],
    ) -> ir::Inst {
        let fref = self.func_ref(b, jmod, id);
        b.ins().call(fref, args)
    }

    fn call_func1<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        id: FuncId,
        args: &[ir::Value],
    ) -> ir::Value {
        let inst = self.call_func(b, jmod, id, args);
        b.inst_results(inst)[0]
    }

    pub(super) fn ref_tag<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        value_ref: ir::Value,
    ) -> ir::Value {
        self.call_func1(b, jmod, self.runtime.type_of_id, &[value_ref])
    }

    pub(super) fn truthy_ref<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        value_ref: ir::Value,
    ) -> ir::Value {
        self.call_func1(b, jmod, self.runtime.truthy_ref_id, &[value_ref])
    }

    pub(super) fn mark_published_ref_aliased<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        value_ref: ir::Value,
    ) -> ir::Value {
        self.call_func1(
            b,
            jmod,
            self.runtime.mark_published_ref_aliased_id,
            &[value_ref],
        )
    }

    pub(super) fn box_int_for_any<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        raw: ir::Value,
    ) -> ir::Value {
        self.call_func1(b, jmod, self.runtime.box_int_for_any_id, &[raw])
    }

    pub(super) fn box_float_for_any<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        raw: ir::Value,
    ) -> ir::Value {
        self.call_func1(b, jmod, self.runtime.box_float_for_any_id, &[raw])
    }

    pub(crate) fn box_atom_for_any<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        raw: ir::Value,
    ) -> ir::Value {
        self.call_func1(b, jmod, self.runtime.box_atom_for_any_id, &[raw])
    }

    pub(crate) fn unbox_int<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        value_ref: ir::Value,
    ) -> ir::Value {
        self.call_func1(b, jmod, self.runtime.unbox_int_id, &[value_ref])
    }

    pub(crate) fn unbox_float<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        value_ref: ir::Value,
    ) -> ir::Value {
        self.call_func1(b, jmod, self.runtime.unbox_float_id, &[value_ref])
    }

    pub(crate) fn unbox_atom<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        value_ref: ir::Value,
    ) -> ir::Value {
        self.call_func1(b, jmod, self.runtime.unbox_atom_id, &[value_ref])
    }

    pub(crate) fn halt_implicit<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        repr: ArgRepr,
        value: ir::Value,
    ) {
        let id = match repr {
            ArgRepr::RawInt => self.runtime.halt_implicit_i64_id,
            ArgRepr::RawF64 => self.runtime.halt_implicit_f64_id,
            ArgRepr::ValueRef => self.runtime.halt_implicit_ref_id,
            ArgRepr::Condition => unreachable!("condition halt values must be materialized"),
        };
        self.call_func(b, jmod, id, &[value]);
    }

    pub(crate) fn alloc_frame<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        schema_id: ir::Value,
        size: ir::Value,
    ) -> ir::Value {
        self.call_func1(b, jmod, self.runtime.alloc_id, &[schema_id, size])
    }

    pub(crate) fn get_halt_cont<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        body_addr: ir::Value,
        halt_kind: ir::Value,
    ) -> ir::Value {
        self.call_func1(
            b,
            jmod,
            self.runtime.get_halt_cont_id,
            &[body_addr, halt_kind],
        )
    }

    pub(crate) fn alloc_closure<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        func_id: ir::Value,
        captured_count: ir::Value,
        halt_kind: ir::Value,
        code_addr: ir::Value,
    ) -> ir::Value {
        self.call_func1(
            b,
            jmod,
            self.runtime.alloc_closure_id,
            &[func_id, captured_count, halt_kind, code_addr],
        )
    }

    pub(crate) fn empty_list_ref(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        cache: &mut CodegenCache,
    ) -> ir::Value {
        emit_empty_list_value_ref_word(b, cache)
    }

    pub(crate) fn list_tail_ref_word(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        cache: &mut CodegenCache,
        tail: ListTailBits,
    ) -> ir::Value {
        match tail {
            ListTailBits::Empty => self.empty_list_ref(b, cache),
            ListTailBits::ValueRef(value) | ListTailBits::NonEmptyValueRef(value) => value,
        }
    }

    pub(crate) fn list_cons_with<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        cons_id: FuncId,
        args: &[ir::Value],
    ) -> ir::Value {
        self.call_func1(b, jmod, cons_id, args)
    }

    pub(crate) fn list_head<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        list_ref: ir::Value,
    ) -> ir::Value {
        self.call_func1(b, jmod, self.runtime.list_head_fallback_id, &[list_ref])
    }

    pub(crate) fn list_head_int<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        list_ref: ir::Value,
    ) -> ir::Value {
        self.call_func1(b, jmod, self.runtime.list_head_int_ref_id, &[list_ref])
    }

    pub(crate) fn list_head_float<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        list_ref: ir::Value,
    ) -> ir::Value {
        self.call_func1(b, jmod, self.runtime.list_head_float_ref_id, &[list_ref])
    }

    pub(crate) fn list_tail<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        list_ref: ir::Value,
    ) -> ir::Value {
        self.call_func1(b, jmod, self.runtime.list_tail_fallback_id, &[list_ref])
    }

    pub(crate) fn list_reuse_or_cons_tail_ref<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        source_ref: ir::Value,
        tail_ref: ir::Value,
    ) -> ir::Value {
        self.call_func1(
            b,
            jmod,
            self.runtime.list_reuse_or_cons_tail_ref_id,
            &[source_ref, tail_ref],
        )
    }

    pub(crate) fn closure_capture_i64<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        closure_ref: ir::Value,
        index: ir::Value,
    ) -> ir::Value {
        self.call_func1(
            b,
            jmod,
            self.runtime.closure_get_capture_i64_id,
            &[closure_ref, index],
        )
    }

    pub(crate) fn closure_capture_f64<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        closure_ref: ir::Value,
        index: ir::Value,
    ) -> ir::Value {
        self.call_func1(
            b,
            jmod,
            self.runtime.closure_get_capture_f64_id,
            &[closure_ref, index],
        )
    }

    pub(crate) fn closure_capture_ref<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        closure_ref: ir::Value,
        index: ir::Value,
    ) -> ir::Value {
        self.call_func1(
            b,
            jmod,
            self.runtime.closure_get_capture_ref_id,
            &[closure_ref, index],
        )
    }

    pub(crate) fn closure_code_ref<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        closure_ref: ir::Value,
    ) -> ir::Value {
        self.call_func1(b, jmod, self.runtime.closure_code_ref_id, &[closure_ref])
    }

    pub(crate) fn closure_halt_kind_ref<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        closure_ref: ir::Value,
    ) -> ir::Value {
        self.call_func1(
            b,
            jmod,
            self.runtime.closure_halt_kind_ref_id,
            &[closure_ref],
        )
    }

    pub(crate) fn set_closure_capture_ref<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        closure_ref: ir::Value,
        index: ir::Value,
        value: ir::Value,
    ) {
        self.call_func(
            b,
            jmod,
            self.runtime.closure_set_capture_ref_id,
            &[closure_ref, index, value],
        );
    }

    pub(crate) fn set_closure_capture_i64<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        closure_ref: ir::Value,
        index: ir::Value,
        value: ir::Value,
    ) {
        self.call_func(
            b,
            jmod,
            self.runtime.closure_set_capture_i64_id,
            &[closure_ref, index, value],
        );
    }

    pub(crate) fn set_closure_capture_f64<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        closure_ref: ir::Value,
        index: ir::Value,
        value: ir::Value,
    ) {
        self.call_func(
            b,
            jmod,
            self.runtime.closure_set_capture_f64_id,
            &[closure_ref, index, value],
        );
    }

    pub(crate) fn materialize_cont<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        value: ir::Value,
    ) -> ir::Value {
        self.call_func1(b, jmod, self.runtime.materialize_cont_id, &[value])
    }

    pub(crate) fn struct_set_field_int<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        struct_bits: ir::Value,
        offset: ir::Value,
        value: ir::Value,
    ) {
        self.call_func(
            b,
            jmod,
            self.runtime.struct_set_field_int_id,
            &[struct_bits, offset, value],
        );
    }

    pub(crate) fn struct_set_field_float<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        struct_bits: ir::Value,
        offset: ir::Value,
        value: ir::Value,
    ) {
        self.call_func(
            b,
            jmod,
            self.runtime.struct_set_field_float_id,
            &[struct_bits, offset, value],
        );
    }

    pub(crate) fn struct_set_field_atom<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        struct_bits: ir::Value,
        offset: ir::Value,
        value: ir::Value,
    ) {
        self.call_func(
            b,
            jmod,
            self.runtime.struct_set_field_atom_id,
            &[struct_bits, offset, value],
        );
    }

    pub(crate) fn struct_set_field_ref<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        struct_bits: ir::Value,
        offset: ir::Value,
        value: ir::Value,
    ) {
        self.call_func(
            b,
            jmod,
            self.runtime.struct_set_field_ref_id,
            &[struct_bits, offset, value],
        );
    }
}

impl<M> CodegenFnSite<'_, '_, '_, M>
where
    M: cranelift_module::Module,
{
    pub(crate) fn closure_capture_i64_at(
        &mut self,
        closure_ref: ir::Value,
        idx: usize,
    ) -> ir::Value {
        let index = self.b.ins().iconst(types::I64, idx as i64);
        self.cx
            .closure_capture_i64(self.b, self.jmod, closure_ref, index)
    }

    pub(crate) fn closure_capture_f64_at(
        &mut self,
        closure_ref: ir::Value,
        idx: usize,
    ) -> ir::Value {
        let index = self.b.ins().iconst(types::I64, idx as i64);
        self.cx
            .closure_capture_f64(self.b, self.jmod, closure_ref, index)
    }

    pub(crate) fn closure_capture_ref_at(
        &mut self,
        closure_ref: ir::Value,
        idx: usize,
    ) -> ir::Value {
        let index = self.b.ins().iconst(types::I64, idx as i64);
        self.cx
            .closure_capture_ref(self.b, self.jmod, closure_ref, index)
    }

    pub(crate) fn closure_capture_as_binding(
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

    pub(crate) fn outer_cont_ref(&mut self, closure_ref: ir::Value) -> ir::Value {
        self.closure_capture_ref_at(closure_ref, 0)
    }

    pub(crate) fn closure_code_ref(&mut self, closure_ref: ir::Value) -> ir::Value {
        self.cx.closure_code_ref(self.b, self.jmod, closure_ref)
    }

    pub(crate) fn closure_halt_kind_ref(&mut self, closure_ref: ir::Value) -> ir::Value {
        self.cx
            .closure_halt_kind_ref(self.b, self.jmod, closure_ref)
    }

    pub(crate) fn value_truthy(&mut self, value: CodegenValue) -> ir::Value {
        self.cx.value_truthy(self.b, self.jmod, value)
    }

    pub(crate) fn value_is_tag(
        &mut self,
        value: CodegenValue,
        tag: fz_runtime::any_value::ValueKind,
    ) -> ir::Value {
        self.cx.value_is_tag(self.b, self.jmod, value, tag)
    }

    pub(crate) fn value_atom_id_is(&mut self, value: CodegenValue, atom_id: u32) -> ir::Value {
        self.cx.value_atom_id_is(self.b, self.jmod, value, atom_id)
    }

    pub(crate) fn value_raw_int(&mut self, value: CodegenValue) -> ir::Value {
        self.cx.value_raw_int(self.b, self.jmod, value)
    }

    pub(crate) fn value_raw_float(&mut self, value: CodegenValue) -> ir::Value {
        self.cx.value_raw_float(self.b, self.jmod, value)
    }

    pub(crate) fn mark_published_ref_aliased(&mut self, value_ref: ir::Value) -> ir::Value {
        self.cx
            .mark_published_ref_aliased(self.b, self.jmod, value_ref)
    }

    pub(crate) fn store_closure_capture_ref_word(
        &mut self,
        closure_ref: ir::Value,
        idx: usize,
        value: ir::Value,
    ) {
        let value = self.cx.mark_published_ref_aliased(self.b, self.jmod, value);
        let index = self.b.ins().iconst(types::I64, idx as i64);
        self.cx
            .set_closure_capture_ref(self.b, self.jmod, closure_ref, index, value);
    }

    pub(crate) fn store_closure_capture_i64(
        &mut self,
        closure_ref: ir::Value,
        idx: usize,
        value: ir::Value,
    ) {
        let index = self.b.ins().iconst(types::I64, idx as i64);
        self.cx
            .set_closure_capture_i64(self.b, self.jmod, closure_ref, index, value);
    }

    pub(crate) fn store_closure_capture_f64(
        &mut self,
        closure_ref: ir::Value,
        idx: usize,
        value: ir::Value,
    ) {
        let index = self.b.ins().iconst(types::I64, idx as i64);
        self.cx
            .set_closure_capture_f64(self.b, self.jmod, closure_ref, index, value);
    }

    pub(crate) fn materialize_cont_word(&mut self, value: ir::Value) -> ir::Value {
        self.cx.materialize_cont(self.b, self.jmod, value)
    }
}

impl<M> CodegenFnBody<'_, '_, '_, M>
where
    M: cranelift_module::Module,
{
    pub(crate) fn value_as_any_ref(&mut self, value: CodegenValue) -> ir::Value {
        self.cx
            .value_as_any_ref(self.b, self.jmod, self.cache, value)
    }

    pub(crate) fn tagged_var(
        &mut self,
        var_env: &HashMap<u32, CodegenValue>,
        var: u32,
    ) -> ir::Value {
        self.cx
            .tagged_var(var_env, self.b, self.jmod, var, self.cache)
    }

    pub(crate) fn value_raw_int(&mut self, value: CodegenValue) -> ir::Value {
        self.cx.value_raw_int(self.b, self.jmod, value)
    }

    pub(crate) fn value_raw_float(&mut self, value: CodegenValue) -> ir::Value {
        self.cx.value_raw_float(self.b, self.jmod, value)
    }

    pub(crate) fn value_raw_atom(&mut self, value: CodegenValue) -> ir::Value {
        self.cx.value_raw_atom(self.b, self.jmod, self.cache, value)
    }

    pub(crate) fn ref_tag(&mut self, value_ref: ir::Value) -> ir::Value {
        self.cx.ref_tag(self.b, self.jmod, value_ref)
    }

    pub(crate) fn mark_published_ref_aliased(&mut self, value_ref: ir::Value) -> ir::Value {
        self.cx
            .mark_published_ref_aliased(self.b, self.jmod, value_ref)
    }

    pub(crate) fn any_ref_for_var(
        &mut self,
        var_env: &HashMap<u32, CodegenValue>,
        var: u32,
    ) -> ir::Value {
        self.cx
            .any_ref_for_var(var_env, self.b, self.jmod, var, self.cache)
    }

    pub(crate) fn list_tail_ref_word(&mut self, tail: ListTailBits) -> ir::Value {
        self.cx.list_tail_ref_word(self.b, self.cache, tail)
    }

    pub(crate) fn empty_list_ref(&mut self) -> ir::Value {
        self.cx.empty_list_ref(self.b, self.cache)
    }

    pub(crate) fn list_cons_with(&mut self, cons_id: FuncId, args: &[ir::Value]) -> ir::Value {
        self.cx.list_cons_with(self.b, self.jmod, cons_id, args)
    }

    pub(crate) fn list_head(&mut self, list_ref: ir::Value) -> ir::Value {
        self.cx.list_head(self.b, self.jmod, list_ref)
    }

    pub(crate) fn list_head_int(&mut self, list_ref: ir::Value) -> ir::Value {
        self.cx.list_head_int(self.b, self.jmod, list_ref)
    }

    pub(crate) fn list_head_float(&mut self, list_ref: ir::Value) -> ir::Value {
        self.cx.list_head_float(self.b, self.jmod, list_ref)
    }

    pub(crate) fn list_tail(&mut self, list_ref: ir::Value) -> ir::Value {
        self.cx.list_tail(self.b, self.jmod, list_ref)
    }

    pub(crate) fn owned_cons_reuse_source(
        &self,
        head: crate::fz_ir::Var,
    ) -> Option<crate::fz_ir::Var> {
        self.cache.owned_cons_reuse_sources.get(&head.0).copied()
    }

    pub(crate) fn list_reuse_or_cons_tail_ref(
        &mut self,
        source_ref: ir::Value,
        tail_ref: ir::Value,
    ) -> ir::Value {
        self.cx
            .list_reuse_or_cons_tail_ref(self.b, self.jmod, source_ref, tail_ref)
    }

    pub(crate) fn halt_implicit(&mut self, repr: ArgRepr, value: ir::Value) {
        self.cx.halt_implicit(self.b, self.jmod, repr, value);
    }

    pub(crate) fn alloc_frame(&mut self, schema_id: ir::Value, size: ir::Value) -> ir::Value {
        self.cx.alloc_frame(self.b, self.jmod, schema_id, size)
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
                        ArgRepr::RawInt => self.cx.box_int_for_any(self.b, self.jmod, value),
                        ArgRepr::RawF64 => self.cx.box_float_for_any(self.b, self.jmod, value),
                        ArgRepr::Condition => {
                            let atom = bool_to_fz(self.b, self.cache, value);
                            self.cx.box_atom_for_any(self.b, self.jmod, atom)
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
            out.push(match binding {
                CodegenValue::RawInt(value) => {
                    emit_raw_int_as_abi_value_ref(self.cx, self.b, self.jmod, value)
                }
                CodegenValue::RawF64(value) => {
                    emit_raw_float_as_abi_value_ref(self.cx, self.b, self.jmod, value)
                }
                CodegenValue::Condition(value) => {
                    let atom = bool_to_fz(self.b, self.cache, value);
                    emit_raw_atom_as_abi_value_ref(self.cx, self.b, self.jmod, atom)
                }
                CodegenValue::AnyRef(value) => value,
                CodegenValue::Known { payload, kind } => {
                    box_known_non_heap_as_any_ref(self.cx, self.b, self.jmod, payload, kind)
                }
            });
        } else {
            out.push(self.coerce_binding_to(binding, to));
        }
    }

    pub(crate) fn coerce_binding_to(&mut self, binding: CodegenValue, to: ArgRepr) -> ir::Value {
        coerce_binding_to(self.cx, self.b, self.jmod, binding, to)
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
