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

pub(crate) struct CodegenFn<'builder, 'ctx, 'env, M: cranelift_module::Module> {
    pub(crate) b: &'ctx mut FunctionBuilder<'builder>,
    pub(crate) jmod: &'ctx mut M,
    pub(crate) env: &'ctx CodegenEnv<'env>,
    pub(crate) cache: &'ctx mut CodegenCache,
    imports: FunctionImports,
}

impl<'builder, 'ctx, 'env, M: cranelift_module::Module> CodegenFn<'builder, 'ctx, 'env, M> {
    pub(crate) fn new(
        b: &'ctx mut FunctionBuilder<'builder>,
        jmod: &'ctx mut M,
        env: &'ctx CodegenEnv<'env>,
        cache: &'ctx mut CodegenCache,
    ) -> Self {
        Self {
            b,
            jmod,
            env,
            cache,
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
        self.call_func1(self.env.runtime.type_of_id, &[value_ref])
    }

    pub(crate) fn empty_list_ref(&mut self) -> ir::Value {
        emit_empty_list_value_ref_word(self.b, self.cache)
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
}
