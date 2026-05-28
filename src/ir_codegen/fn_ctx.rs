//! Per-function semantic codegen context.
//!
//! Cranelift's `FunctionBuilder` owns the body currently being emitted.
//! Function-local imports, however, need both the module and the function
//! body. `CodegenFn` is the fz-owned boundary for "lower one fz function":
//! semantic lowering code should ask this context for operations, while
//! runtime helper calls remain an implementation detail behind those methods.

use super::*;
use cranelift_codegen::ir::{self, InstBuilder, types};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::FuncId;
use std::collections::HashMap;

#[derive(Default)]
pub(crate) struct FunctionImports {
    refs: HashMap<FuncId, ir::FuncRef>,
}

impl FunctionImports {
    pub(crate) fn func_ref<M: cranelift_module::Module>(
        &mut self,
        jmod: &mut M,
        func: &mut ir::Function,
        id: FuncId,
    ) -> ir::FuncRef {
        *self
            .refs
            .entry(id)
            .or_insert_with(|| jmod.declare_func_in_func(id, func))
    }
}

pub(crate) struct CodegenFn<'env> {
    runtime: &'env RuntimeRefs,
    imports: FunctionImports,
}

impl<'env> CodegenFn<'env> {
    pub(crate) fn new(env: &'env CodegenEnv<'_>) -> Self {
        Self {
            runtime: env.runtime,
            imports: FunctionImports::default(),
        }
    }

    /// Build a semantic context for generated runtime shim bodies, which
    /// have runtime refs but no fz `CodegenEnv`.
    pub(crate) fn for_runtime_shim(runtime: &'env RuntimeRefs) -> Self {
        Self {
            runtime,
            imports: FunctionImports::default(),
        }
    }

    pub(crate) fn func_ref<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        id: FuncId,
    ) -> ir::FuncRef {
        self.imports.func_ref(jmod, b.func, id)
    }

    pub(crate) fn call_func<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        id: FuncId,
        args: &[ir::Value],
    ) -> ir::Inst {
        let fref = self.func_ref(b, jmod, id);
        b.ins().call(fref, args)
    }

    pub(crate) fn call_func1<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        id: FuncId,
        args: &[ir::Value],
    ) -> ir::Value {
        let inst = self.call_func(b, jmod, id, args);
        b.inst_results(inst)[0]
    }

    pub(crate) fn ref_tag<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        value_ref: ir::Value,
    ) -> ir::Value {
        self.call_func1(b, jmod, self.runtime.type_of_id, &[value_ref])
    }

    pub(crate) fn truthy_ref<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        value_ref: ir::Value,
    ) -> ir::Value {
        self.call_func1(b, jmod, self.runtime.truthy_ref_id, &[value_ref])
    }

    pub(crate) fn mark_published_ref_aliased<M: cranelift_module::Module>(
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

    pub(crate) fn box_int_for_any<M: cranelift_module::Module>(
        &mut self,
        b: &mut FunctionBuilder<'_>,
        jmod: &mut M,
        raw: ir::Value,
    ) -> ir::Value {
        self.call_func1(b, jmod, self.runtime.box_int_for_any_id, &[raw])
    }

    pub(crate) fn box_float_for_any<M: cranelift_module::Module>(
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
    fn function_imports_reuse_func_ref_per_function() {
        let mut module = jit_module();
        let mut sig = module.make_signature();
        sig.returns.push(AbiParam::new(types::I64));
        let callee = module
            .declare_function("fz_import_test_callee", Linkage::Import, &sig)
            .expect("declare import");

        let mut ctx = module.make_context();
        ctx.func.signature = module.make_signature();
        let mut fbctx = FunctionBuilderContext::new();
        let b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);

        let mut imports = FunctionImports::default();
        let first = imports.func_ref(&mut module, b.func, callee);
        let second = imports.func_ref(&mut module, b.func, callee);

        assert_eq!(first, second);
        b.finalize();
    }

    fn count_matches(haystack: &str, needle: &str) -> usize {
        haystack.matches(needle).count()
    }

    #[test]
    fn ordinary_lowering_runtime_plumbing_stays_budgeted() {
        let files = [
            ("call.rs", include_str!("call.rs"), 8, 8, 0),
            ("closure.rs", include_str!("closure.rs"), 3, 6, 0),
            ("entry.rs", include_str!("entry.rs"), 1, 1, 0),
            ("function.rs", include_str!("function.rs"), 0, 0, 0),
            ("prim.rs", include_str!("prim.rs"), 47, 57, 0),
            ("repr.rs", include_str!("repr.rs"), 1, 1, 0),
            ("support.rs", include_str!("support.rs"), 1, 1, 0),
            ("terminator.rs", include_str!("terminator.rs"), 13, 7, 0),
            ("value.rs", include_str!("value.rs"), 1, 1, 0),
        ];

        for (name, source, max_declares, max_runtime_ids, max_runtime_contexts) in files {
            let declares = count_matches(source, "declare_func_in_func");
            assert!(
                declares <= max_declares,
                "{name} has {declares} direct function imports; budget is {max_declares}"
            );
            let runtime_ids = count_matches(source, "runtime.");
            assert!(
                runtime_ids <= max_runtime_ids,
                "{name} has {runtime_ids} runtime helper id references; budget is {max_runtime_ids}"
            );
            let runtime_contexts = count_matches(source, "CodegenFn::for_runtime_shim");
            assert!(
                runtime_contexts <= max_runtime_contexts,
                "{name} has {runtime_contexts} helper-local CodegenFn contexts; budget is {max_runtime_contexts}"
            );
        }
    }
}
