use crate::compiler2::{Compiler2, FactKey, Job};
use crate::modules::identity::ModuleName;
use crate::modules::runtime_library;
use crate::telemetry::{Capture, ConfiguredTelemetry};

/// The library's declarations are not checked on each compile; a program
/// would pay for hundreds of contracts it never uses. They are checked here
/// instead, once, so a typo in a library `@spec`, `@type` or extern fails
/// the gate rather than going unnoticed until something calls it.
#[test]
fn every_library_declaration_is_checked() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &["fz", "diag"]);
    let mut compiler = Compiler2::new(tel);
    let owners = runtime_library::module_sources()
        .map(|(name, _)| {
            let world = compiler.world_mut();
            let module = world.reference_module(ModuleName::parse_dotted(name).expect("library module name"));
            let owner = world
                .ensure_runtime_module(module)
                .expect("a library module has a source");
            compiler.demand(Job::CheckDeclarations(owner));
            (name, owner)
        })
        .collect::<Vec<_>>();
    compiler.drive();

    let reports = capture
        .events()
        .iter()
        .filter_map(|event| event.diagnostic.as_ref())
        .map(|diagnostic| diagnostic.message.clone())
        .collect::<Vec<_>>();
    assert_eq!(reports, Vec::<String>::new(), "every library declaration resolves");
    let unchecked = owners
        .iter()
        .filter(|(_, owner)| !compiler.world().has_fact(&FactKey::DeclarationsChecked(*owner)))
        .map(|(name, _)| *name)
        .collect::<Vec<_>>();
    assert_eq!(unchecked, Vec::<&str>::new(), "every library module is checked");
}
