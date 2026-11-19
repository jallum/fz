use super::*;
use crate::compiler2::native_codegen::runtime_call::runtime_func_ref;
use cranelift_jit::JITModule;
use cranelift_module::default_libcall_names;
use cranelift_object::{ObjectBuilder, ObjectModule};
use fz_runtime::ir_runtime::fz_type_of;

fn executable_module() -> ObjectModule {
    let object = ObjectBuilder::new(host_isa_for(CodeHome::Executable), "clif_test", default_libcall_names())
        .expect("an object builder for the host");
    ObjectModule::new(object)
}

/// Whether a function of `module` calls `fz_type_of` through a near reference.
fn runtime_call_is_near<M: Module>(mut module: M) -> bool {
    let mut ctx = module.make_context();
    let mut fbctx = FunctionBuilderContext::new();
    let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
    let entry = b.create_block();
    b.switch_to_block(entry);
    let mut cache = CodegenCache::default();
    let sites = std::cell::RefCell::new(AllocSites::declare(&mut module).expect("declare the site counters"));
    let scope = SiteScope {
        sites: &sites,
        function: "test",
    };
    let mut body = CodegenFn::new(&mut b, &mut module, &mut cache, scope);
    let callee = runtime_func_ref!(body, fz_type_of(_));
    body.b.func.dfg.ext_funcs[callee].colocated
}

/// An executable is linked with the runtime archive, so the linker places
/// every helper within a direct branch's reach: the call is one `bl`.
#[test]
fn an_executable_calls_a_runtime_helper_by_a_direct_branch() {
    assert!(runtime_call_is_near(executable_module()));
}

/// JIT code lives in its own arena, which may lie beyond a direct branch's
/// reach of the runtime in the process image, so it calls through an address.
#[test]
fn code_in_this_process_calls_a_runtime_helper_through_its_address() {
    assert!(!runtime_call_is_near(JITModule::new(jit_builder())));
}
