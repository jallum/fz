//! Proof that `drive_harness`'s own mechanics work, for the corners no
//! fixture pilot happens to exercise: `.open_root`, `.demand`, the raw
//! `.drive()` outcome, `.dump_stage`, and every `Settled` lookup method.
//! `canon_test.rs` and `fixture_facts_test.rs` only need
//! `fixture`/`settle`/`dump_stage`/`world`/`compiler`/`backend_program`/
//! `fixture_path`; this file is where the rest of the harness gets a real
//! caller instead of sitting as unexercised API.

use super::drive_harness::{Drive, module_name};
use super::identity::TypeName;
use super::{DriveOutcome, Job, LoweredBody, ModuleId};

/// `.open_root` enters a function other than `main/0`, and `.demand` forces a
/// job the entered root's own reachability would never ask for. In
/// `00574_drive_harness_open_root_probe`, `helper/1` is the root, and
/// `Probe.unreached` is a module-scoped `@type` nothing `helper/1` mentions,
/// so the job graph derives it only because of the explicit demand.
#[test]
fn open_root_and_demand_reach_a_non_default_entry_and_an_unreferenced_fact() {
    let unreached = |module: ModuleId| TypeName {
        module,
        name: "unreached".to_string(),
        arity: 0,
    };

    let settled = Drive::fixture(574)
        .open_root(None, "helper", 1)
        .demand(move |world| Job::DeriveTypeDef(unreached(world.reference_module(module_name("Probe")))))
        .settle();

    assert_eq!(
        settled.function("helper", 1),
        settled.compiler().root_function(settled.root()),
        "open_root's entry must be the driven root's own function"
    );
    assert!(
        settled.world().type_def(&unreached(settled.module("Probe"))).is_some(),
        "an explicit demand must derive a type nothing in the entered root reaches"
    );
}

#[test]
fn drive_returns_the_outcome_alongside_settled() {
    let (settled, outcome) = Drive::fixture(572).drive();
    assert!(
        matches!(outcome, DriveOutcome::Resolved),
        "a well-formed program should resolve: {outcome:?}"
    );
    assert_eq!(
        settled.function("main", 0),
        settled.compiler().root_function(settled.root())
    );
}

/// Every capture `Drive` installs, and every `Settled` lookup over it, proved
/// against `00573_drive_harness_capture_probe`: a module (`.module`,
/// `.modules`), a lowered function (`.lowered_body`), calls and their return
/// types (`.callsites`, `.return_types`), `dbg` output (`.dbg`), per-job
/// effects (`.outputs`), and the settled backend/native product
/// (`.backend_program`/`.native_program`/`.backend_programs`/
/// `.native_programs`, reached through `.dump_stage` rather than `.settle()`
/// — the product-pull path never runs during the semantic drive alone).
#[test]
fn settle_and_dump_stage_populate_every_installed_capture() {
    let mut settled = Drive::fixture(573).settle();

    let helper = settled.function("helper", 1);
    let main = settled.function("main", 0);
    assert_ne!(
        helper, main,
        "distinct top-level functions must resolve to distinct ids"
    );

    let util = settled.module("Util");
    assert_eq!(settled.modules().qualified_name(util), "Util");

    let LoweredBody::Clauses { .. } = settled.lowered_body(helper) else {
        panic!("helper/1 should lower to clauses");
    };

    assert!(
        !settled.callsites().all().is_empty(),
        "calling helper/1 and Util.double/1 from main/0 must define callsites"
    );
    let return_ty = settled
        .return_types()
        .last_for_function(settled.root(), helper)
        .return_ty;
    assert!(
        !settled.world().types().display(&return_ty).is_empty(),
        "helper/1 must publish a renderable return type"
    );
    // `dbg()` is a runtime call: `.settle()` only runs the semantic fixpoint
    // layer, so the `DbgCapture` stays empty until the program is actually
    // executed, the same way `canon_test.rs`'s allocation-order tests drive
    // execution with `run_root_interp` after settling.
    let root = settled.root();
    settled
        .compiler_mut()
        .run_root_interp(root)
        .expect("main/0 should run to completion");
    assert!(
        settled.dbg().lines().len() >= 2,
        "both dbg() calls in main/0 must reach the installed DbgCapture: {:?}",
        settled.dbg().lines()
    );
    assert!(
        !settled
            .outputs()
            .effects(Job::DefineFunction(helper))
            .outputs
            .is_empty(),
        "defining helper/1 must publish at least one output fact"
    );
    assert!(
        !settled.functions().all().is_empty(),
        "the installed FunctionCapture must have recorded every defined function"
    );

    let fact = super::drive::FactKey::TypeDefined(TypeName {
        module: ModuleId::GLOBAL,
        name: "unused_probe".to_string(),
        arity: 0,
    });
    assert_eq!(settled.presence(fact.clone(), true), (fact, true));

    let settled = Drive::fixture(573).dump_stage(super::dump::DumpStage::Native);
    assert!(
        !settled.backend_program().executables().is_empty(),
        "the backend product must retain at least one executable"
    );
    assert!(
        !settled.backend_programs().records(settled.root()).is_empty(),
        "BackendProgramCapture must have recorded the settled backend product"
    );
    assert_eq!(
        settled.native_program().executable_entries.len(),
        settled.backend_program().executables().len(),
        "the native product should carry one entry per backend executable"
    );
    // NativeProgramCapture has no `records` lookup (unlike its backend
    // sibling); `.last` is what production code and this proof both use.
    assert_eq!(
        settled.native_programs().last(settled.root()).root_id,
        settled.root(),
        "NativeProgramCapture must have recorded the settled native product"
    );
}
