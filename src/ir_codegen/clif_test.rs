use super::*;
use cranelift_codegen::Context;
use cranelift_codegen::ir::AbiParam;
use cranelift_codegen::verifier::verify_function;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module, default_libcall_names};
use fz_runtime::heap::SchemaRegistry;
use fz_runtime::ir_runtime::fz_yield_slow_path_begin;
use fz_runtime::pinned_abi::call1;
use fz_runtime::process::Process;
use std::cell::RefCell;
use std::rc::Rc;

#[test]
fn pinned_register_instructions_verify_for_jit_and_aot_isa() {
    for pic in [false, true] {
        let isa = host_isa_with(pic);
        assert!(isa.flags().enable_pinned_reg());

        let mut sig = Signature::new(isa.default_call_conv());
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));

        let mut ctx = Context::new();
        ctx.func.signature = sig;
        let mut fbctx = FunctionBuilderContext::new();
        {
            let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);
            let process = b.block_params(entry)[0];
            b.ins().set_pinned_reg(process);
            let observed = b.ins().get_pinned_reg(types::I64);
            b.ins().return_(&[observed]);
            b.finalize();
        }

        verify_function(&ctx.func, isa.as_ref()).expect("pinned-register CLIF should verify");
        let clif = ctx.func.display().to_string();
        assert!(clif.contains("set_pinned_reg"));
        assert!(clif.contains("get_pinned_reg"));
    }
}

#[test]
fn pinned_register_survives_runtime_helper_call() {
    let isa = host_isa();
    let mut builder = JITBuilder::with_isa(isa, default_libcall_names());
    builder.symbol("fz_yield_slow_path_begin", fz_yield_slow_path_begin as *const u8);
    let mut module = JITModule::new(builder);

    let yield_slow_path_begin_id = module
        .declare_function("fz_yield_slow_path_begin", Linkage::Import, &sig1(&[types::I64], &[]))
        .expect("declare yield slow path helper");
    let probe_id = module
        .declare_function(
            "fz_pinned_runtime_call_probe",
            Linkage::Local,
            &sig1(&[types::I64], &[types::I64]),
        )
        .expect("declare probe");

    let mut fbctx = FunctionBuilderContext::new();
    emit_fn_body(
        &mut module,
        &mut fbctx,
        sig1(&[types::I64], &[types::I64]),
        probe_id,
        |module, b| {
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);

            let slow_path = module.declare_func_in_func(yield_slow_path_begin_id, b.func);
            let process = b.ins().get_pinned_reg(types::I64);
            b.ins().call(slow_path, &[process]);

            let observed = b.ins().get_pinned_reg(types::I64);
            b.ins().return_(&[observed]);
        },
    )
    .expect("define probe");
    module.finalize_definitions().expect("finalize probe");
    let probe_addr = module.get_finalized_function(probe_id);

    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let mut process = Process::new(schemas);
    let expected = (&mut process as *mut Process) as u64;

    let observed = unsafe { call1(probe_addr, &mut process, 0) } as u64;
    assert_eq!(observed, expected);
}
