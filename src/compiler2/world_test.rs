use super::{Namespace, World};
use crate::telemetry::ConfiguredTelemetry;

#[test]
#[should_panic(expected = "modules should be scoped before definition")]
fn compiler2_world_define_module_panics_for_unscoped_module() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let module = world.reference_module("Unscoped");

    let _ = world.define_module(module, Namespace::default(), Vec::new());
}

#[test]
#[should_panic(expected = "module exports should only be read from defined modules")]
fn compiler2_world_module_exports_panics_for_unscoped_module() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let module = world.reference_module("Unscoped");

    let _ = world.module_exports(module);
}

#[test]
#[should_panic(expected = "modules should be indexed before scoping")]
fn compiler2_world_scope_module_panics_for_unindexed_module() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let module = world.reference_module("Unindexed");

    let _ = world.scope_module(module, Namespace::default());
}
