use super::World;
use super::identity::{ActivationKey, RootId};
use super::semantic::{CallSiteSummary, CallTargetSummary, CallableDemand, RuntimeDemand, SelectedCallee, ShapeDemand};

/// A consumer states a tuple demand field by field, and two consumers of
/// one tuple rarely read the same fields. `TupleFields` is a prefix: a body
/// that reads only field 0 says one field, a body that reads field 1 says
/// two. Joining those is padding the shorter one with `ignore`, not
/// throwing both away -- a value nobody read cannot be evidence about a
/// value somebody did, and the callable obligation on field 0 has to
/// survive the arrival of a sibling.
#[test]
fn joining_tuple_field_demands_of_different_length_keeps_every_field() {
    let mut world = World::new();
    let int = world.types_mut().int();
    let callable = RuntimeDemand::callable(CallableDemand::resolved(vec![int], world.types_mut()));
    let first_field_only = RuntimeDemand::tuple_fields(vec![callable.clone()]);
    let second_field_only = RuntimeDemand::tuple_fields(vec![RuntimeDemand::ignore(), RuntimeDemand::whole()]);

    let joined = first_field_only.join(&second_field_only);

    let ShapeDemand::TupleFields(fields) = &joined.shape else {
        panic!("two field demands join to a field demand, not {:?}", joined.shape);
    };
    assert_eq!(fields.len(), 2, "the join spans every field either side named");
    assert_eq!(
        fields[0], callable,
        "the callable obligation on a field only one side read still stands"
    );
    assert_eq!(fields[1], RuntimeDemand::whole());
    assert_eq!(
        second_field_only.join(&first_field_only),
        joined,
        "the join does not depend on which consumer is seen first"
    );
}

/// A provider boundary is somebody else's code: it publishes a call surface,
/// not a compiler2 executable, so nothing downstream can emit a direct edge
/// to it or ground a return against its executable fact. The activation field
/// is not the test -- a summary carrying one anyway must still be refused,
/// because the callee kind is what decides who owns the body.
#[test]
fn a_provider_boundary_is_never_the_one_owned_target() {
    let mut world = World::new();
    let int = world.types_mut().int();
    let function = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "impl", 1);
    let activation = ActivationKey::from_inputs(RootId::for_test(0), function, &[int], world.types_mut());
    let target = |callee| CallTargetSummary {
        callee,
        surface_inputs: vec![int],
        activation: Some(activation.clone()),
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };
    let summary = |callee| CallSiteSummary {
        targets: vec![target(callee)],
        return_ty: None,
    };

    assert!(
        summary(SelectedCallee::ProviderBoundary(function))
            .single_owned_target()
            .is_none(),
        "a provider boundary owns no executable to call directly",
    );
    assert_eq!(
        summary(SelectedCallee::Function(function))
            .single_owned_target()
            .map(|(_, activation)| activation.clone()),
        Some(activation),
        "a compiler-owned callee with one activation is the target",
    );
}
