use super::source::{define_function, define_module, expand_function_source, index_code, scope_code};
use super::{Job, World};
use crate::compiler2::{FactKey, ModuleId};
use crate::telemetry::{Capture, ConfiguredTelemetry};

#[test]
fn runtime_prelude_exact_imports_record_kernel_expectations_without_waiting() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let mut world = World::new(&tel);
    let prelude = world.runtime_prelude();
    let kernel = world.reference_module("Kernel".to_string());

    let index = index_code(&mut world, prelude).expect("runtime prelude should index");
    world.complete_job(Job::IndexCode(prelude), index);

    let scoped = scope_code(&mut world, prelude).expect("runtime prelude scoping should not fatal");
    assert!(
        scoped.waits.is_empty(),
        "runtime prelude exact imports should bind expectations without blocking on Kernel's full interface: {scoped:?}",
    );
    let kernel_interface = world
        .module_interface_if_present(kernel)
        .expect("exact prelude imports should note expectations on Kernel immediately");
    assert!(
        kernel_interface
            .expectations()
            .iter()
            .any(|expectation| expectation.name == "dbg" && expectation.arity == 1),
        "runtime prelude should record exact import expectations on Kernel before its interface settles: {:?}",
        kernel_interface.expectations(),
    );
    world.complete_job(Job::ScopeCode(prelude), scoped);

    let kernel_code = world
        .ensure_runtime_module(kernel)
        .expect("Kernel should be a known runtime module");
    let kernel_index = index_code(&mut world, kernel_code).expect("Kernel runtime source should index");
    world.complete_job(Job::IndexCode(kernel_code), kernel_index);
    let kernel_scope = scope_code(&mut world, kernel_code).expect("Kernel runtime source should scope");
    world.complete_job(Job::ScopeCode(kernel_code), kernel_scope);

    let kernel_define = define_module(&mut world, kernel).unwrap_or_else(|_| {
        let diagnostic = capture
            .last(&["fz", "diag", "error"])
            .expect("Kernel definition failure should emit a diagnostic");
        panic!("Kernel module definition should not fatal: diagnostic={diagnostic:?}");
    });
    world.complete_job(Job::DefineModule(kernel), kernel_define);
    assert!(
        capture.last(&["fz", "diag", "error"]).is_none(),
        "settling Kernel after the prelude records exact import expectations should not emit diagnostics",
    );
}

#[test]
fn re_scoping_the_runtime_prelude_does_not_churn_fn_macro_source() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let prelude = world.runtime_prelude();

    let index = index_code(&mut world, prelude).expect("runtime prelude should index");
    world.complete_job(Job::IndexCode(prelude), index);
    let scoped = scope_code(&mut world, prelude).expect("runtime prelude should scope");
    world.complete_job(Job::ScopeCode(prelude), scoped);

    let fn_macro = world.reference_function(ModuleId::GLOBAL, "fn", 1);
    let expand = expand_function_source(&mut world, fn_macro).expect("fn/1 source should expand");
    world.complete_job(Job::ExpandFunctionSource(fn_macro), expand);
    let define = define_function(&mut world, fn_macro).expect("fn/1 should define from expanded source");
    world.complete_job(Job::DefineFunction(fn_macro), define);

    let initial_revision = world
        .fact_revision(FactKey::FunctionSource(fn_macro))
        .expect("fn/1 source fact should exist after first scope");
    let replay = scope_code(&mut world, prelude).expect("re-scoping runtime prelude should not fatal");
    assert!(
        !replay.changed.contains(&FactKey::FunctionSource(fn_macro)),
        "stable re-scoping must not republish fn/1 source as changed: {replay:?}",
    );
    world.complete_job(Job::ScopeCode(prelude), replay);
    assert_eq!(
        world.fact_revision(FactKey::FunctionSource(fn_macro)),
        Some(initial_revision),
        "re-scoping the unchanged prelude must keep the fn/1 source revision stable",
    );
}
