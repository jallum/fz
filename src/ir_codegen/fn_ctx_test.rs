use super::*;
use cranelift_codegen::ir::AbiParam;
use cranelift_codegen::settings;
use cranelift_frontend::FunctionBuilderContext;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module, default_libcall_names};
use cranelift_native::builder;

fn jit_module() -> JITModule {
    let flags = settings::Flags::new(settings::builder());
    let isa = builder().expect("host isa").finish(flags).expect("finish isa");
    JITModule::new(JITBuilder::with_isa(isa, default_libcall_names()))
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

    let mut cache = CodegenCache::default();
    let mut cg = CodegenFn::for_runtime_shim(&runtime, &mut b, &mut module, &mut cache);
    let first = cg.func_ref(callee);
    let second = cg.func_ref(callee);

    assert_eq!(first, second);
    drop(cg);
    b.finalize();
}
