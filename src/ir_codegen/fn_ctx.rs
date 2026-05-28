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

pub(crate) struct CodegenFn<'builder, 'ctx, M: cranelift_module::Module> {
    pub(crate) b: &'ctx mut FunctionBuilder<'builder>,
    pub(crate) jmod: &'ctx mut M,
    runtime: &'ctx RuntimeRefs,
    cache: Option<&'ctx mut CodegenCache>,
    imports: FunctionImports,
}

impl<'builder, 'ctx, M: cranelift_module::Module> CodegenFn<'builder, 'ctx, M> {
    pub(crate) fn new(
        b: &'ctx mut FunctionBuilder<'builder>,
        jmod: &'ctx mut M,
        env: &'ctx CodegenEnv<'_>,
        cache: &'ctx mut CodegenCache,
    ) -> Self {
        Self {
            b,
            jmod,
            runtime: env.runtime,
            cache: Some(cache),
            imports: FunctionImports::default(),
        }
    }

    pub(crate) fn new_runtime(
        b: &'ctx mut FunctionBuilder<'builder>,
        jmod: &'ctx mut M,
        runtime: &'ctx RuntimeRefs,
    ) -> Self {
        Self {
            b,
            jmod,
            runtime,
            cache: None,
            imports: FunctionImports::default(),
        }
    }

    pub(crate) fn new_runtime_with_cache(
        b: &'ctx mut FunctionBuilder<'builder>,
        jmod: &'ctx mut M,
        runtime: &'ctx RuntimeRefs,
        cache: &'ctx mut CodegenCache,
    ) -> Self {
        Self {
            b,
            jmod,
            runtime,
            cache: Some(cache),
            imports: FunctionImports::default(),
        }
    }

    pub(crate) fn func_ref(&mut self, id: FuncId) -> ir::FuncRef {
        self.imports.func_ref(self.jmod, self.b.func, id)
    }

    pub(crate) fn call_func(&mut self, id: FuncId, args: &[ir::Value]) -> ir::Inst {
        let fref = self.func_ref(id);
        self.b.ins().call(fref, args)
    }

    pub(crate) fn call_func1(&mut self, id: FuncId, args: &[ir::Value]) -> ir::Value {
        let inst = self.call_func(id, args);
        self.b.inst_results(inst)[0]
    }

    pub(crate) fn ref_tag(&mut self, value_ref: ir::Value) -> ir::Value {
        self.call_func1(self.runtime.type_of_id, &[value_ref])
    }

    pub(crate) fn truthy_ref(&mut self, value_ref: ir::Value) -> ir::Value {
        self.call_func1(self.runtime.truthy_ref_id, &[value_ref])
    }

    pub(crate) fn box_int_for_any(&mut self, raw: ir::Value) -> ir::Value {
        self.call_func1(self.runtime.box_int_for_any_id, &[raw])
    }

    pub(crate) fn box_float_for_any(&mut self, raw: ir::Value) -> ir::Value {
        self.call_func1(self.runtime.box_float_for_any_id, &[raw])
    }

    pub(crate) fn box_atom_for_any(&mut self, raw: ir::Value) -> ir::Value {
        self.call_func1(self.runtime.box_atom_for_any_id, &[raw])
    }

    pub(crate) fn unbox_int(&mut self, value_ref: ir::Value) -> ir::Value {
        self.call_func1(self.runtime.unbox_int_id, &[value_ref])
    }

    pub(crate) fn unbox_float(&mut self, value_ref: ir::Value) -> ir::Value {
        self.call_func1(self.runtime.unbox_float_id, &[value_ref])
    }

    pub(crate) fn unbox_atom(&mut self, value_ref: ir::Value) -> ir::Value {
        self.call_func1(self.runtime.unbox_atom_id, &[value_ref])
    }

    pub(crate) fn empty_list_ref(&mut self) -> ir::Value {
        let cache = self
            .cache
            .as_deref_mut()
            .expect("empty list refs require a CodegenCache");
        emit_empty_list_value_ref_word(self.b, cache)
    }

    pub(crate) fn list_tail_ref_word(&mut self, tail: ListTailBits) -> ir::Value {
        match tail {
            ListTailBits::Empty => self.empty_list_ref(),
            ListTailBits::ValueRef(value) | ListTailBits::NonEmptyValueRef(value) => value,
        }
    }

    pub(crate) fn list_cons_with(&mut self, cons_id: FuncId, args: &[ir::Value]) -> ir::Value {
        self.call_func1(cons_id, args)
    }

    pub(crate) fn list_head(&mut self, list_ref: ir::Value) -> ir::Value {
        self.call_func1(self.runtime.list_head_fallback_id, &[list_ref])
    }

    pub(crate) fn list_head_int(&mut self, list_ref: ir::Value) -> ir::Value {
        self.call_func1(self.runtime.list_head_int_ref_id, &[list_ref])
    }

    pub(crate) fn list_head_float(&mut self, list_ref: ir::Value) -> ir::Value {
        self.call_func1(self.runtime.list_head_float_ref_id, &[list_ref])
    }

    pub(crate) fn list_tail(&mut self, list_ref: ir::Value) -> ir::Value {
        self.call_func1(self.runtime.list_tail_fallback_id, &[list_ref])
    }

    pub(crate) fn closure_capture_i64(
        &mut self,
        closure_ref: ir::Value,
        index: ir::Value,
    ) -> ir::Value {
        self.call_func1(
            self.runtime.closure_get_capture_i64_id,
            &[closure_ref, index],
        )
    }

    pub(crate) fn closure_capture_f64(
        &mut self,
        closure_ref: ir::Value,
        index: ir::Value,
    ) -> ir::Value {
        self.call_func1(
            self.runtime.closure_get_capture_f64_id,
            &[closure_ref, index],
        )
    }

    pub(crate) fn closure_capture_ref(
        &mut self,
        closure_ref: ir::Value,
        index: ir::Value,
    ) -> ir::Value {
        self.call_func1(
            self.runtime.closure_get_capture_ref_id,
            &[closure_ref, index],
        )
    }

    pub(crate) fn closure_code_ref(&mut self, closure_ref: ir::Value) -> ir::Value {
        self.call_func1(self.runtime.closure_code_ref_id, &[closure_ref])
    }

    pub(crate) fn closure_halt_kind_ref(&mut self, closure_ref: ir::Value) -> ir::Value {
        self.call_func1(self.runtime.closure_halt_kind_ref_id, &[closure_ref])
    }

    pub(crate) fn set_closure_capture_ref(
        &mut self,
        closure_ref: ir::Value,
        index: ir::Value,
        value: ir::Value,
    ) {
        self.call_func(
            self.runtime.closure_set_capture_ref_id,
            &[closure_ref, index, value],
        );
    }

    pub(crate) fn set_closure_capture_i64(
        &mut self,
        closure_ref: ir::Value,
        index: ir::Value,
        value: ir::Value,
    ) {
        self.call_func(
            self.runtime.closure_set_capture_i64_id,
            &[closure_ref, index, value],
        );
    }

    pub(crate) fn set_closure_capture_f64(
        &mut self,
        closure_ref: ir::Value,
        index: ir::Value,
        value: ir::Value,
    ) {
        self.call_func(
            self.runtime.closure_set_capture_f64_id,
            &[closure_ref, index, value],
        );
    }

    pub(crate) fn materialize_cont(&mut self, value: ir::Value) -> ir::Value {
        self.call_func1(self.runtime.materialize_cont_id, &[value])
    }

    pub(crate) fn struct_set_field_int(
        &mut self,
        struct_bits: ir::Value,
        offset: ir::Value,
        value: ir::Value,
    ) {
        self.call_func(
            self.runtime.struct_set_field_int_id,
            &[struct_bits, offset, value],
        );
    }

    pub(crate) fn struct_set_field_float(
        &mut self,
        struct_bits: ir::Value,
        offset: ir::Value,
        value: ir::Value,
    ) {
        self.call_func(
            self.runtime.struct_set_field_float_id,
            &[struct_bits, offset, value],
        );
    }

    pub(crate) fn struct_set_field_atom(
        &mut self,
        struct_bits: ir::Value,
        offset: ir::Value,
        value: ir::Value,
    ) {
        self.call_func(
            self.runtime.struct_set_field_atom_id,
            &[struct_bits, offset, value],
        );
    }

    pub(crate) fn struct_set_field_ref(
        &mut self,
        struct_bits: ir::Value,
        offset: ir::Value,
        value: ir::Value,
    ) {
        self.call_func(
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
            ("call.rs", include_str!("call.rs"), 8, 8),
            ("closure.rs", include_str!("closure.rs"), 3, 6),
            ("prim.rs", include_str!("prim.rs"), 47, 57),
            ("terminator.rs", include_str!("terminator.rs"), 13, 7),
            ("value.rs", include_str!("value.rs"), 1, 1),
        ];

        for (name, source, max_declares, max_runtime_ids) in files {
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
        }
    }
}
