use std::collections::HashMap;

use super::artifact::tests::fake_call_executable;
use super::artifact::{ArtifactTransportLookup, materialize_closure_call_edge};
use crate::compiler2::body::ControlDestination;
use crate::compiler2::identity::{ExecutableNeed, ModuleId, RootId};
use crate::compiler2::pull::TransportLayout;
use crate::compiler2::semantic::{
    ActivationAnalysis, CallSiteKey, CallSiteResolution, CallSiteSummary, CallTargetSummary, EntryReachability,
    SelectedCallee,
};
use crate::compiler2::transport::ShapeDescr;
use crate::compiler2::{ActivationKey, CallSiteId, ValueId, World};
use crate::telemetry::ConfiguredTelemetry;

/// A closure call is lowered one of two ways, and the callee's layout picks
/// which: a callable naming the target with its capture layouts becomes a
/// direct edge, and one public word becomes a boxed call through the apply
/// seam. A callee with neither -- and no evidence at all -- is a call that
/// never happens, and lowers as a dead one.
///
/// This is the state none of those three describe. The callee is a real
/// value -- a callable shape, not nothing -- so the call is not dead; but it
/// names no function, publishes no lane, and the one target it reaches
/// declares a capture. There is nothing to supply that capture from and no
/// word to call through, so neither convention can be built. No source
/// program produces that: the callsite summary and the transport layout
/// describe one value, and here they contradict each other. That is a
/// compiler defect, so the edge stops as an internal error rather than
/// picking one half of a convention or blaming the program.
#[test]
#[should_panic(expected = "does not carry, and the layout is not one public word either")]
fn materialize_closure_call_edge_refuses_a_callee_that_supplies_neither_captures_nor_a_word() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let caller = fake_call_executable(&mut world, 320, 321, &[]);
    let callsite = CallSiteId::from_u32(7);
    // One capture input beyond the source arity, so the target declares a
    // capture the caller would have to hand it.
    let target_function = world.reference_function(ModuleId::GLOBAL, "needs_capture", 0);
    let target = ActivationKey::from_inputs(RootId::for_test(320), target_function, &[int], world.types_mut());
    assert_eq!(world.activation_capture_count(&target), 1);
    world.define_callsite_summary(
        CallSiteKey {
            activation: caller.activation.clone(),
            callsite,
        },
        CallSiteResolution::Resolved(CallSiteSummary {
            targets: vec![CallTargetSummary {
                callee: SelectedCallee::Function(target_function),
                surface_inputs: vec![int],
                activation: Some(target),
                activation_inputs: None,
                extern_params: None,
                return_ty: Some(int),
            }],
            return_ty: Some(int),
        }),
    );
    let generic = world.intern_callable(crate::compiler2::transport::CallableDescr {
        function: None,
        arity: 0,
        capture_layouts: Box::default(),
    });
    let callee_layout = TransportLayout::structural(world.intern_shape(ShapeDescr::Callable(generic)));
    let result_value = ValueId::from_u32(2);
    let summaries = world
        .callsite_summary(&CallSiteKey {
            activation: caller.activation.clone(),
            callsite,
        })
        .cloned()
        .map(|summary| HashMap::from([(callsite, summary)]))
        .unwrap_or_default();

    let _ = materialize_closure_call_edge(
        &mut world,
        &tel,
        RootId::for_test(320),
        &ArtifactTransportLookup { positions: &[] },
        &caller,
        &ActivationAnalysis {
            input_rows: Vec::new(),
            entry_reachability: EntryReachability::new(Vec::new(), false),
            reachable_entries: Vec::new(),
            callsites: Vec::new(),
            value_types: HashMap::from([(result_value, int)]),
        },
        &summaries,
        callee_layout,
        ExecutableNeed::Value,
        callsite,
        result_value,
        &ControlDestination::Return,
        &[],
        &HashMap::new(),
    );
}
