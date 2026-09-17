use super::Job;
use super::source::{define_function, define_module, expand_function_source, index_code, scope_code};
use crate::compiler2::{FactKey, ModuleId, World};
use crate::telemetry::{Capture, ConfiguredTelemetry};

#[test]
fn runtime_prelude_exact_imports_record_kernel_expectations_without_waiting() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut world = World::new();
    let prelude = world.runtime_prelude();
    let kernel = world.reference_module(crate::modules::identity::ModuleName::parse_dotted("Kernel").unwrap());

    let index = index_code(&mut world, &tel, prelude).expect("runtime prelude should index");
    world.complete_job(Job::IndexCode(prelude), index);

    let scoped = scope_code(&mut world, &tel, None, prelude).expect("runtime prelude scoping should not fatal");
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
    let kernel_index = index_code(&mut world, &tel, kernel_code).expect("Kernel runtime source should index");
    world.complete_job(Job::IndexCode(kernel_code), kernel_index);
    let kernel_scope = scope_code(&mut world, &tel, None, kernel_code).expect("Kernel runtime source should scope");
    world.complete_job(Job::ScopeCode(kernel_code), kernel_scope);

    let kernel_define = define_module(&mut world, &tel, None, kernel).unwrap_or_else(|_| {
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
fn re_scoping_the_runtime_prelude_does_not_churn_def_macro_source() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let prelude = world.runtime_prelude();

    let index = index_code(&mut world, &tel, prelude).expect("runtime prelude should index");
    world.complete_job(Job::IndexCode(prelude), index);
    let scoped = scope_code(&mut world, &tel, None, prelude).expect("runtime prelude should scope");
    world.complete_job(Job::ScopeCode(prelude), scoped);

    let def_macro = world.reference_function(ModuleId::GLOBAL, "def", 1);
    let expand = expand_function_source(&mut world, &tel, None, def_macro).expect("def/1 source should expand");
    world.complete_job(Job::ExpandFunctionSource(def_macro), expand);
    let define = define_function(&mut world, &tel, def_macro).expect("def/1 should define from expanded source");
    world.complete_job(Job::DefineFunction(def_macro), define);

    let initial_revision = world
        .fact_revision(&FactKey::FunctionSource(def_macro))
        .expect("def/1 source fact should exist after first scope");
    let replay = scope_code(&mut world, &tel, None, prelude).expect("re-scoping runtime prelude should not fatal");
    assert!(
        !replay.changed.contains(&FactKey::FunctionSource(def_macro)),
        "stable re-scoping must not republish def/1 source as changed: {replay:?}",
    );
    world.complete_job(Job::ScopeCode(prelude), replay);
    assert_eq!(
        world.fact_revision(&FactKey::FunctionSource(def_macro)),
        Some(initial_revision),
        "re-scoping the unchanged prelude must keep the def/1 source revision stable",
    );
}

#[test]
fn blocked_scope_keeps_prelude_ground_on_reached_function_sources() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let code = world.submit_code(
        Some("blocked-ground.fz".into()),
        "def early(), do: 1\nimport MissingReviewModule\n".into(),
    );
    world.demand(Job::ScopeCode(code));
    let mut sessions = crate::compiler2::pull::ProductSessions::default();
    let _ = crate::compiler2::drive::ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive();

    let effects = scope_code(&mut world, &tel, Some(&sessions), code).expect("scope returns a wait");
    assert!(
        !effects.waits.is_empty(),
        "the unresolved import must leave the scope walk blocked"
    );

    let early = world.reference_function(ModuleId::GLOBAL, "early", 0);
    let derivation = effects
        .derivations
        .iter()
        .find(|derivation| derivation.outputs.contains(&FactKey::FunctionSource(early)))
        .expect("early source reached");
    let prelude = crate::compiler2::facts::FactUse::current(FactKey::CodeScoped(world.runtime_prelude()));
    assert!(
        derivation.reads.contains(&prelude),
        "a reached function source must retain the prelude ground that scoped it"
    );
    assert!(
        effects.reads.contains(&prelude),
        "the blocked scope job must retain the prelude ground that scoped it"
    );

    world.complete_job(Job::ScopeCode(code), effects);
    assert!(
        world.fact_is_settled(&FactKey::FunctionSource(early)),
        "the reached function source must settle while its prelude ground remains published"
    );
    let prelude_retraction = world.complete_job(
        Job::ScopeCode(world.runtime_prelude()),
        crate::compiler2::drive::JobEffects::default(),
    );
    assert!(
        !world.fact_is_settled(&FactKey::FunctionSource(early)),
        "retracting the prelude must unsettle the reached function source"
    );
    assert!(
        prelude_retraction.step.wakes.iter().any(|wake| {
            wake.job == Job::ScopeCode(code)
                && wake.cause.readiness() == prelude.readiness()
                && wake.cause.fact().fact() == Some(prelude.fact())
                && wake.shift
        }),
        "prelude retraction must wake the blocked scope job through its base read"
    );
}
