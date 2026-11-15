use super::{DefinitionCycle, WaitForGraph};
use crate::compiler2::drive::{DependencyKey, FactKey, Job, ProductAddress};
use crate::compiler2::identity::{FunctionId, ModuleId, RootId};
use crate::compiler2::pull::{ProductKey, ProductScope};
use crate::fast_hash::HashSet;
use fz_engine::{FactUse, UnresolvedWait};

fn module(raw: u32) -> ModuleId {
    ModuleId::for_test(raw)
}

fn function(raw: u32) -> FunctionId {
    FunctionId::from_coordinate(raw)
}

fn macro_program(root: u32) -> ProductAddress {
    let root = RootId::for_test(root);
    ProductAddress::of(ProductKey::RootBackendProduct(root), root)
}

fn wait(dependency: DependencyKey, jobs: &[Job]) -> UnresolvedWait<Job, DependencyKey> {
    UnresolvedWait {
        fact: FactUse::current(dependency),
        jobs: jobs.to_vec(),
    }
}

fn fact_wait(fact: FactKey, jobs: &[Job]) -> UnresolvedWait<Job, DependencyKey> {
    wait(DependencyKey::Fact(fact), jobs)
}

fn producer(fact: &FactKey) -> Option<Job> {
    match fact {
        FactKey::ModuleDefined(module) => Some(Job::DefineModule(*module)),
        FactKey::LoweredBody(function) => Some(Job::LowerFunction(*function)),
        _ => None,
    }
}

/// `M`'s definition waits on a macro's compiled program; that program's drive
/// deferred on the lowered body of `g`; lowering `g` waits on `M`'s definition.
/// `main` lowers only once `M` is defined, so it is stalled by the loop too.
#[test]
fn a_definition_that_waits_through_a_macro_program_on_itself_is_a_cycle() {
    let (m, g, main) = (module(7), function(1), function(2));
    let waits = [
        wait(DependencyKey::Product(macro_program(5)), &[Job::DefineModule(m)]),
        fact_wait(
            FactKey::ModuleDefined(m),
            &[Job::LowerFunction(g), Job::LowerFunction(main)],
        ),
    ];
    let deferred = |scope: &ProductScope| match scope {
        ProductScope::Root(_) => vec![FactKey::LoweredBody(g)],
        ProductScope::Program => Vec::new(),
    };
    assert_eq!(
        WaitForGraph::new(&waits, producer, deferred).definition_cycle(),
        Some(DefinitionCycle {
            module: m,
            entry: Job::LowerFunction(g),
            exit: DependencyKey::Product(macro_program(5)),
            stalled_by_it: HashSet::from_iter([Job::DefineModule(m), Job::LowerFunction(g), Job::LowerFunction(main)]),
        })
    );
}

/// `M`'s definition waits on a macro's program that waits on a module nothing
/// defines. `M` is stalled, and `main` waits on `M`, but nothing leads back to
/// `M`'s definition: the fault is the other module, not a loop.
#[test]
fn a_stalled_definition_that_waits_on_something_else_is_no_cycle() {
    let (m, nope, main) = (module(7), module(8), function(2));
    let waits = [
        wait(DependencyKey::Product(macro_program(5)), &[Job::DefineModule(m)]),
        fact_wait(FactKey::ModuleDefined(m), &[Job::LowerFunction(main)]),
    ];
    let deferred = |_: &ProductScope| vec![FactKey::ModuleDefined(nope)];
    assert_eq!(WaitForGraph::new(&waits, producer, deferred).definition_cycle(), None);
}
