use crate::fz_ir::{FnId, Module};
use crate::telemetry::{ConfiguredTelemetry, Handler};
use crate::types::ConcreteTypes;
use std::cell::RefCell;
use std::panic::AssertUnwindSafe;
use std::rc::Rc;

/// Captures the exact lowered IR module emitted by the production frontend
/// before planning begins.
struct LoweredCapture(Rc<RefCell<Option<Module>>>);

impl Handler for LoweredCapture {
    fn handle(&self, ev: &crate::telemetry::Event<'_, '_, '_>) {
        if let ["fz", "frontend", "lowered"] = ev.name {
            if let Some(module) = ev
                .metadata
                .get("module")
                .and_then(|value| value.downcast_ref::<Module>())
            {
                *self.0.borrow_mut() = Some(module.clone());
            }
        }
    }
}

/// Run the production frontend and snapshot the lowered IR module from
/// telemetry. This is the exact frontend output the planner consumes.
pub(crate) fn lower_frontend_module(src: &str) -> Module {
    let captured = Rc::new(RefCell::new(None));
    let tel = ConfiguredTelemetry::new();
    tel.attach(&["fz"], Box::new(LoweredCapture(captured.clone())));

    let prev_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let _ = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let mut t = ConcreteTypes;
        let providers = crate::modules::pipeline::ProviderInputs::new(
            crate::modules::artifact_store::DEFAULT_ARTIFACT_ROOT.to_string(),
            Vec::new(),
        );
        let _ = crate::modules::pipeline::compile_source_with_providers(
            &mut t,
            src.to_string(),
            "test_fixture.fz".to_string(),
            &providers,
            &tel,
        );
    }));
    std::panic::set_hook(prev_hook);

    captured
        .borrow_mut()
        .take()
        .expect("frontend emitted no lowered module")
}

/// Compile a program through the production pipeline to the linked runtime IR:
/// protocol impls, runtime helpers, and execution-graph rewrites are local.
pub(crate) fn linked_runtime_module(src: &str) -> Module {
    use crate::modules::pipeline::{
        CompileMode, ProviderInputs, checked_module_for_mode, compile_source_with_providers,
        prepare_execution_graph,
    };

    let mut t = ConcreteTypes;
    let tel = crate::telemetry::NullTelemetry;
    let providers = ProviderInputs::new(
        crate::modules::artifact_store::DEFAULT_ARTIFACT_ROOT.to_string(),
        Vec::new(),
    );
    let frontend = compile_source_with_providers(
        &mut t,
        src.to_string(),
        "test_fixture.fz".to_string(),
        &providers,
        &tel,
    )
    .unwrap_or_else(|err| panic!("frontend: {err}"));
    let checked = checked_module_for_mode(&mut t, frontend, &tel, CompileMode::Normal)
        .unwrap_or_else(|err| panic!("checked: {err}"));
    let prepared = prepare_execution_graph(&mut t, checked, &providers, &tel, CompileMode::Normal)
        .unwrap_or_else(|err| panic!("execution graph: {err}"));
    prepared.module
}

/// Fixture tests enter through a top-level `main`.
pub(crate) fn entry_main_fn_id(module: &Module) -> FnId {
    module
        .fns
        .iter()
        .find(|f| f.name == "main")
        .expect("main fn")
        .id
}
