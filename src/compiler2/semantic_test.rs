use super::super::World;
use super::super::identity::{ActivationKey, RootId};
use super::super::semantic::{
    CallSiteSummary, CallTargetSummary, CallableDemand, RuntimeDemand, SelectedCallee, ShapeDemand,
};

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

#[cfg(test)]
mod tests {
    use std::collections::{BTreeSet, HashMap, HashSet};
    use std::rc::Rc;

    use super::super::*;
    use crate::compiler2::drive::JobEffects;
    use crate::compiler2::{ExecutableNeed, FactKey, Job, RootId, World};
    use crate::telemetry::ConfiguredTelemetry;
    use crate::types::{ClosureTarget, Sigma};

    fn test_key(world: &mut World, _tel: &ConfiguredTelemetry) -> ActivationKey {
        let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
        let any = world.types_mut().any();
        let function = world.root_function(root);
        ActivationKey::from_inputs(root, function, &[any, any], world.types_mut())
    }

    #[test]
    fn runtime_demand_contributions_replace_and_retract_one_exact_publisher() {
        let mut world = World::new();
        let tel = ConfiguredTelemetry::new();
        let activation = test_key(&mut world, &tel);
        let target = ExecutableKey {
            activation: activation.clone(),
            need: ExecutableNeed::Value,
        };
        let left = Job::DeriveRuntimeDemand(target.clone());
        let right = Job::DeriveRuntimeDemand(ExecutableKey {
            activation,
            need: ExecutableNeed::TupleFields(1),
        });
        let mut contributions = RuntimeDemandInputMap::new();

        let returning = TargetDemandContribution {
            return_demand: Some(RuntimeDemand::whole()),
            ..TargetDemandContribution::default()
        };
        let first = contributions.conclude_exact(
            world.types_mut(),
            left.clone(),
            HashSet::new(),
            HashMap::from([(target.clone(), returning.clone())]),
        );
        assert_eq!(first.changed_keys, HashSet::from([target.clone()]));

        let equal = contributions.conclude_exact(
            world.types_mut(),
            left.clone(),
            first.output_keys,
            HashMap::from([(target.clone(), returning.clone())]),
        );
        assert!(equal.changed_keys.is_empty(), "an equal exact answer must not move");

        let second = contributions.conclude_exact(
            world.types_mut(),
            right.clone(),
            HashSet::new(),
            HashMap::from([(target.clone(), returning.clone())]),
        );
        assert!(
            second.changed_keys.is_empty(),
            "an equal second publisher must not move the join"
        );

        let narrowed = TargetDemandContribution {
            input_demands: HashMap::from([(0, RuntimeDemand::whole())]),
            ..TargetDemandContribution::default()
        };
        let replacement = contributions.conclude_exact(
            world.types_mut(),
            left.clone(),
            equal.output_keys,
            HashMap::from([(target.clone(), narrowed.clone())]),
        );
        assert_eq!(replacement.changed_keys, HashSet::from([target.clone()]));
        assert_eq!(
            contributions.get(&target).unwrap().return_demand,
            returning.return_demand
        );
        assert_eq!(
            contributions.get(&target).unwrap().input_demands,
            narrowed.input_demands
        );

        let left_retraction =
            contributions.conclude_exact(world.types_mut(), left, replacement.output_keys, HashMap::new());
        assert_eq!(left_retraction.changed_keys, HashSet::from([target.clone()]));
        assert_eq!(contributions.get(&target), Some(&returning));

        let right_retraction =
            contributions.conclude_exact(world.types_mut(), right, second.output_keys, HashMap::new());
        assert_eq!(right_retraction.changed_keys, HashSet::from([target.clone()]));
        assert!(contributions.get(&target).is_none());
    }

    #[test]
    fn equal_runtime_demand_conclusions_do_not_revise_or_wake_exact_readers() {
        let mut world = World::new();
        let tel = ConfiguredTelemetry::new();
        let activation = test_key(&mut world, &tel);
        let target = ExecutableKey {
            activation: activation.clone(),
            need: ExecutableNeed::Value,
        };
        let writer = Job::DeriveRuntimeDemand(target.clone());
        let reader = Job::DeriveRuntimeDemand(ExecutableKey {
            activation,
            need: ExecutableNeed::TupleFields(1),
        });
        let input_fact = FactKey::RuntimeDemandInput(target.clone());
        let reads = vec![FactUse::current(input_fact.clone())];
        world.complete_job(
            reader.clone(),
            JobEffects {
                reads: reads.clone(),
                ..JobEffects::default()
            },
        );
        let target_contribution = TargetDemandContribution {
            return_demand: Some(RuntimeDemand::whole()),
            ..TargetDemandContribution::default()
        };
        let first = world.complete_job(
            writer.clone(),
            JobEffects {
                runtime_demand_input_contributions: vec![(target.clone(), target_contribution.clone())],
                ..JobEffects::default()
            },
        );
        assert!(
            first
                .changed
                .iter()
                .any(|change| change.key == crate::compiler2::drive::DependencyKey::Fact(input_fact.clone()))
        );
        assert!(first.wakes.iter().any(|wake| wake.job == reader));
        let input_revision = world.fact_revision(&input_fact);

        world.complete_job(
            reader,
            JobEffects {
                reads,
                ..JobEffects::default()
            },
        );
        let equal = world.complete_job(
            writer,
            JobEffects {
                runtime_demand_input_contributions: vec![(target, target_contribution)],
                ..JobEffects::default()
            },
        );
        assert!(
            equal.changed.is_empty(),
            "equal semantic answers must not move either fact"
        );
        assert!(
            equal.wakes.is_empty(),
            "equal semantic answers must not wake exact readers"
        );
        assert_eq!(world.fact_revision(&input_fact), input_revision);
    }

    #[test]
    fn runtime_demand_input_subfact_moves_only_with_the_stored_input_vector() {
        let mut world = World::new();
        let tel = ConfiguredTelemetry::new();
        let activation = test_key(&mut world, &tel);
        let executable = ExecutableKey {
            activation: activation.clone(),
            need: ExecutableNeed::Value,
        };
        let fact = FactKey::RuntimeDemand(executable.clone());
        let inputs_fact = FactKey::RuntimeDemandInputs(executable.clone());
        let writer = Job::DeriveRuntimeDemand(executable.clone());
        let full_reader = Job::DeriveRuntimeDemand(ExecutableKey {
            activation: activation.clone(),
            need: ExecutableNeed::TupleFields(1),
        });
        let input_reader = Job::DeriveRuntimeDemand(ExecutableKey {
            activation,
            need: ExecutableNeed::TupleFields(2),
        });
        world.complete_job(
            full_reader.clone(),
            JobEffects {
                reads: vec![FactUse::current(fact.clone())],
                ..JobEffects::default()
            },
        );
        world.complete_job(
            input_reader.clone(),
            JobEffects {
                reads: vec![FactUse::current(inputs_fact.clone())],
                ..JobEffects::default()
            },
        );

        let first_value = Rc::new(ExecutableRuntimeDemand::default());
        assert_eq!(
            world.define_runtime_demand(executable.clone(), first_value),
            (true, true)
        );
        let first = world.complete_job(
            writer.clone(),
            JobEffects {
                outputs: vec![fact.clone(), inputs_fact.clone()],
                changed: vec![fact.clone(), inputs_fact.clone()],
                ..JobEffects::default()
            },
        );
        assert!(first.wakes.iter().any(|wake| wake.job == full_reader));
        assert!(first.wakes.iter().any(|wake| wake.job == input_reader));
        let first_inputs_revision = world.fact_revision(&inputs_fact);

        world.complete_job(
            full_reader.clone(),
            JobEffects {
                reads: vec![FactUse::current(fact.clone())],
                ..JobEffects::default()
            },
        );
        world.complete_job(
            input_reader.clone(),
            JobEffects {
                reads: vec![FactUse::current(inputs_fact.clone())],
                ..JobEffects::default()
            },
        );
        let return_only = Rc::new(ExecutableRuntimeDemand {
            return_demand: RuntimeDemand::whole(),
            ..ExecutableRuntimeDemand::default()
        });
        assert_eq!(
            world.define_runtime_demand(executable.clone(), return_only),
            (true, false)
        );
        let return_change = world.complete_job(
            writer.clone(),
            JobEffects {
                outputs: vec![fact.clone(), inputs_fact.clone()],
                changed: vec![fact.clone()],
                ..JobEffects::default()
            },
        );
        assert!(return_change.wakes.iter().any(|wake| wake.job == full_reader));
        assert!(!return_change.wakes.iter().any(|wake| wake.job == input_reader));
        assert_eq!(world.fact_revision(&inputs_fact), first_inputs_revision);

        let input_change = Rc::new(ExecutableRuntimeDemand {
            return_demand: RuntimeDemand::whole(),
            input_demands: vec![RuntimeDemand::whole()],
            ..ExecutableRuntimeDemand::default()
        });
        assert_eq!(
            world.define_runtime_demand(executable.clone(), input_change),
            (true, true)
        );
        let input_change = world.complete_job(
            writer.clone(),
            JobEffects {
                outputs: vec![fact.clone(), inputs_fact.clone()],
                changed: vec![fact.clone(), inputs_fact.clone()],
                ..JobEffects::default()
            },
        );
        assert!(input_change.wakes.iter().any(|wake| wake.job == input_reader));

        let retained = Rc::clone(world.runtime_demand(&executable).unwrap());
        let stored_inputs = retained.input_demands.as_ptr();
        assert_eq!(
            world.runtime_demand_inputs(&executable).unwrap().as_ptr(),
            stored_inputs,
            "the input fact must project the one stored RuntimeDemand allocation",
        );
        let equal_value = Rc::new((*retained).clone());
        assert_eq!(
            world.define_runtime_demand(executable.clone(), equal_value),
            (false, false)
        );
        assert!(Rc::ptr_eq(world.runtime_demand(&executable).unwrap(), &retained));

        let retracted = world.complete_job(writer.clone(), JobEffects::default());
        assert!(
            retracted
                .changed
                .iter()
                .any(|change| change.key == crate::compiler2::drive::DependencyKey::Fact(fact.clone()))
        );
        assert!(
            retracted
                .changed
                .iter()
                .any(|change| change.key == crate::compiler2::drive::DependencyKey::Fact(inputs_fact.clone()))
        );
        assert!(world.runtime_demand(&executable).is_none());
        assert!(world.runtime_demand_inputs(&executable).is_none());

        world.complete_job(
            full_reader.clone(),
            JobEffects {
                reads: vec![FactUse::current(fact.clone())],
                ..JobEffects::default()
            },
        );
        world.complete_job(
            input_reader.clone(),
            JobEffects {
                reads: vec![FactUse::current(inputs_fact.clone())],
                ..JobEffects::default()
            },
        );
        assert_eq!(
            world.define_runtime_demand(executable.clone(), Rc::new((*retained).clone())),
            (false, false),
            "reappearance must reuse the equal stored semantic value",
        );
        let reappeared = world.complete_job(
            writer,
            JobEffects {
                outputs: vec![fact.clone(), inputs_fact.clone()],
                ..JobEffects::default()
            },
        );
        assert!(
            reappeared
                .changed
                .iter()
                .any(|change| change.key == crate::compiler2::drive::DependencyKey::Fact(fact.clone()))
        );
        assert!(
            reappeared
                .changed
                .iter()
                .any(|change| change.key == crate::compiler2::drive::DependencyKey::Fact(inputs_fact.clone()))
        );
        assert!(reappeared.wakes.iter().any(|wake| wake.job == full_reader));
        assert!(reappeared.wakes.iter().any(|wake| wake.job == input_reader));
        assert!(Rc::ptr_eq(world.runtime_demand(&executable).unwrap(), &retained));
        assert_eq!(
            world.runtime_demand_inputs(&executable).unwrap().as_ptr(),
            stored_inputs
        );
    }

    #[test]
    fn callsite_targets_ignore_type_payload_ascent() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let activation = test_key(&mut world, &tel);
        let callee = activation.function;
        let int = world.types_mut().int();
        let atom = world.types_mut().atom();
        let any = world.types_mut().any();

        let narrow = CallSiteSummary {
            targets: vec![CallTargetSummary {
                callee: SelectedCallee::Function(callee),
                surface_inputs: vec![int],
                activation: Some(activation.clone()),
                activation_inputs: Some(vec![int]),
                extern_params: None,
                return_ty: Some(int),
            }],
            return_ty: Some(int),
        };
        let wider = CallSiteSummary {
            targets: vec![CallTargetSummary {
                callee: SelectedCallee::Function(callee),
                surface_inputs: vec![any],
                activation: Some(activation),
                activation_inputs: Some(vec![any]),
                extern_params: None,
                return_ty: Some(atom),
            }],
            return_ty: Some(atom),
        };

        assert_eq!(
            CallSiteTargets::from_summary(&narrow),
            CallSiteTargets::from_summary(&wider),
            "membership edges are callee+activation identity only; surface and return type ascents must not move them",
        );
    }

    fn resolved_surface(tys: &[Ty], types: &mut Types) -> CallableDemand {
        CallableDemand::resolved(tys.to_vec(), types)
    }

    use super::super::super::types::TypeVarId;

    fn surface(tys: &[Ty], types: &mut Types) -> CallableSurface {
        CallableSurface::new(tys.to_vec(), types)
    }

    #[test]
    fn callsite_summary_join_keeps_return_evidence_when_later_snapshot_is_pending() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
        let caller = world.root_function(root);
        let callee = world.submit_root(None, "callee".to_string(), 1, ExecutableNeed::Value);
        let callee = world.root_function(callee);
        let int = world.types_mut().int();
        let caller_activation = ActivationKey::from_inputs(root, caller, &[], world.types_mut());
        let callee_activation = ActivationKey::from_inputs(root, callee, &[int], world.types_mut());
        let key = CallSiteKey {
            activation: caller_activation,
            callsite: CallSiteId::from_u32(0),
        };
        let ready = CallSiteSummary {
            targets: vec![CallTargetSummary {
                callee: SelectedCallee::Function(callee),
                surface_inputs: vec![int],
                activation: Some(callee_activation.clone()),
                activation_inputs: Some(vec![int]),
                extern_params: None,
                return_ty: Some(int),
            }],
            return_ty: Some(int),
        };
        let pending = CallSiteSummary {
            targets: vec![CallTargetSummary {
                callee: SelectedCallee::Function(callee),
                surface_inputs: vec![int],
                activation: Some(callee_activation),
                activation_inputs: Some(vec![int]),
                extern_params: None,
                return_ty: None,
            }],
            return_ty: None,
        };
        let mut map = CallSiteMap::new();

        assert!(map.define(world.types_mut(), key.clone(), CallSiteResolution::Resolved(ready)));
        assert!(
            !map.define(world.types_mut(), key.clone(), CallSiteResolution::Resolved(pending)),
            "a pending later snapshot must not erase concrete return evidence"
        );
        let stored = map.resolved(&key).expect("joined callsite summary");
        assert_eq!(stored.return_ty, Some(int));
        assert_eq!(stored.targets[0].return_ty, Some(int));

        assert!(
            !map.define(world.types_mut(), key.clone(), CallSiteResolution::Unresolved),
            "an unresolved re-emission is the lattice bottom: it moves nothing"
        );
        assert_eq!(
            map.resolved(&key).expect("the resolved answer stands").return_ty,
            Some(int),
        );
    }

    #[test]
    fn callsite_summary_snapshot_does_not_manufacture_or_retain_activation_keys_for_same_callee() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
        let caller = world.root_function(root);
        let callee_root = world.submit_root(None, "callee".to_string(), 1, ExecutableNeed::Value);
        let callee = world.root_function(callee_root);
        let int = world.types_mut().int();
        let float = world.types_mut().float();
        let caller_activation = ActivationKey::from_inputs(root, caller, &[], world.types_mut());
        let int_activation = ActivationKey::from_inputs(root, callee, &[int], world.types_mut());
        let float_activation = ActivationKey::from_inputs(root, callee, &[float], world.types_mut());
        let key = CallSiteKey {
            activation: caller_activation,
            callsite: CallSiteId::from_u32(0),
        };
        let summary_for = |activation: ActivationKey, input: Ty| CallSiteSummary {
            targets: vec![CallTargetSummary {
                callee: SelectedCallee::Function(callee),
                surface_inputs: vec![input],
                activation: Some(activation),
                activation_inputs: Some(vec![input]),
                extern_params: None,
                return_ty: Some(input),
            }],
            return_ty: Some(input),
        };
        let mut map = CallSiteMap::new();

        assert!(map.define(
            world.types_mut(),
            key.clone(),
            CallSiteResolution::Resolved(summary_for(int_activation.clone(), int))
        ));
        assert!(map.define(
            world.types_mut(),
            key.clone(),
            CallSiteResolution::Resolved(summary_for(float_activation.clone(), float))
        ));

        let stored = map.resolved(&key).expect("joined callsite summary");
        assert_eq!(stored.targets.len(), 1);
        assert!(
            !stored
                .targets
                .iter()
                .any(|target| target.activation.as_ref() == Some(&int_activation)),
            "target membership is a snapshot; stale activations must not linger"
        );
        assert!(
            stored
                .targets
                .iter()
                .any(|target| target.activation.as_ref() == Some(&float_activation))
        );
    }

    #[test]
    fn callsite_summary_keeps_distinct_activations_for_one_callee() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
        let caller = world.root_function(root);
        let callee_root = world.submit_root(None, "callee".to_string(), 1, ExecutableNeed::Value);
        let callee = world.root_function(callee_root);
        let int = world.types_mut().int();
        let float = world.types_mut().float();
        let caller_activation = ActivationKey::from_inputs(root, caller, &[], world.types_mut());
        let int_activation = ActivationKey::from_inputs(root, callee, &[int], world.types_mut());
        let float_activation = ActivationKey::from_inputs(root, callee, &[float], world.types_mut());
        let key = CallSiteKey {
            activation: caller_activation,
            callsite: CallSiteId::from_u32(0),
        };
        let summary = CallSiteSummary {
            targets: vec![
                CallTargetSummary {
                    callee: SelectedCallee::Function(callee),
                    surface_inputs: vec![int],
                    activation: Some(int_activation.clone()),
                    activation_inputs: Some(vec![int]),
                    extern_params: None,
                    return_ty: Some(int),
                },
                CallTargetSummary {
                    callee: SelectedCallee::Function(callee),
                    surface_inputs: vec![float],
                    activation: Some(float_activation.clone()),
                    activation_inputs: Some(vec![float]),
                    extern_params: None,
                    return_ty: Some(float),
                },
            ],
            return_ty: Some(world.types_mut().union(int, float)),
        };
        let mut map = CallSiteMap::new();

        assert!(map.define(world.types_mut(), key.clone(), CallSiteResolution::Resolved(summary)));

        let stored = map.resolved(&key).expect("stored callsite summary");
        assert_eq!(stored.targets.len(), 2);
        assert!(
            stored
                .targets
                .iter()
                .any(|target| target.activation.as_ref() == Some(&int_activation))
        );
        assert!(
            stored
                .targets
                .iter()
                .any(|target| target.activation.as_ref() == Some(&float_activation))
        );
    }

    #[test]
    fn callsite_summary_join_is_quiet_for_equivalent_return_and_surface_types() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
        let caller = world.root_function(root);
        let callee_root = world.submit_root(None, "callee".to_string(), 1, ExecutableNeed::Value);
        let callee = world.root_function(callee_root);
        let var = world.types_mut().type_var(TypeVarId(0));
        let empty = world.types_mut().empty_list();
        let non_empty = world.types_mut().non_empty_list(var);
        let joined = world.types_mut().union(empty, non_empty);
        let rejoined = world.types_mut().union(joined, empty);
        assert!(
            world.types().is_equivalent(&joined, &rejoined),
            "test setup needs equivalent but independently joined types",
        );
        let caller_activation = ActivationKey::from_inputs(root, caller, &[], world.types_mut());
        let callee_activation = ActivationKey::from_inputs(root, callee, &[joined], world.types_mut());
        let key = CallSiteKey {
            activation: caller_activation,
            callsite: CallSiteId::from_u32(0),
        };
        let summary = |ty| CallSiteSummary {
            targets: vec![CallTargetSummary {
                callee: SelectedCallee::Function(callee),
                surface_inputs: vec![ty],
                activation: Some(callee_activation.clone()),
                activation_inputs: Some(vec![ty]),
                extern_params: None,
                return_ty: Some(ty),
            }],
            return_ty: Some(ty),
        };
        let mut map = CallSiteMap::new();

        assert!(map.define(
            world.types_mut(),
            key.clone(),
            CallSiteResolution::Resolved(summary(joined))
        ));
        assert!(
            !map.define(world.types_mut(), key, CallSiteResolution::Resolved(summary(rejoined))),
            "equivalent joined callsite evidence should not churn the semantic fact"
        );
    }

    #[test]
    fn activation_input_vector_join_does_not_lower_existing_union_evidence() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let atom_a = world.types_mut().atom_lit("a");
        let atom_b = world.types_mut().atom_lit("b");
        let union = world.types_mut().union(atom_a, atom_b);
        let mut current = vec![union];

        current.join_assign(&vec![atom_a], world.types_mut());

        assert_eq!(
            current,
            vec![union],
            "activation-input evidence is cumulative; a later narrower observation must not lower the joined slot",
        );
    }

    #[test]
    fn rebased_activation_input_conclusion_preserves_prior_publisher_frontier() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let key = test_key(&mut world, &tel);
        let input = world.types_mut().atom_lit("seen");
        let publisher = Job::AnalyzeActivation(key.clone());
        let mut map = ActivationInputMap::new();

        let first = map.conclude(
            world.types_mut(),
            publisher.clone(),
            HashSet::new(),
            HashMap::from([(key.clone(), ActivationInputAlternatives::from_row(vec![input]))]),
            false,
        );
        assert_eq!(first.output_keys, HashSet::from([key.clone()]));
        assert_eq!(map.get(&key), Some(&ActivationInputAlternatives::from_row(vec![input])));

        let rebased = map.conclude_preserving_frontier(
            world.types_mut(),
            publisher,
            HashSet::from([key.clone()]),
            HashMap::new(),
        );

        assert_eq!(
            rebased.output_keys,
            HashSet::from([key.clone()]),
            "rebased activation-input evidence may pause but must not retract the publisher's prior edge"
        );
        assert!(
            rebased.changed_keys.is_empty(),
            "preserving an unchanged frontier should not mark the activation input dirty"
        );
        assert_eq!(map.get(&key), Some(&ActivationInputAlternatives::from_row(vec![input])));
    }

    #[test]
    fn contribution_key_waves_allocate_identically_across_reverse_insertion() {
        let run = |reverse: bool| {
            let mut world = World::new();
            let root = RootId::for_test(92);
            let function = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "contribution_order", 1);
            let int = world.types_mut().int();
            let float = world.types_mut().float();
            let atom_a = world.types_mut().atom_lit("a");
            let atom_b = world.types_mut().atom_lit("b");
            let list = world.types_mut().list(int);
            let non_empty = world.types_mut().non_empty_list(int);
            let list_key = ActivationKey::from_inputs(root, function, &[list], world.types_mut());
            let non_empty_key = ActivationKey::from_inputs(root, function, &[non_empty], world.types_mut());
            let mut map = ActivationInputMap::new();
            let publisher_a = Job::SeedRoot(root);
            let publisher_b = Job::AnalyzeActivation(list_key.clone());
            let first = HashMap::from([
                (list_key.clone(), ActivationInputAlternatives::from_row(vec![int])),
                (
                    non_empty_key.clone(),
                    ActivationInputAlternatives::from_row(vec![float]),
                ),
            ]);
            map.conclude(world.types_mut(), publisher_a, HashSet::new(), first, false);
            let second = if reverse {
                [
                    (
                        non_empty_key.clone(),
                        ActivationInputAlternatives::from_row(vec![atom_b]),
                    ),
                    (list_key.clone(), ActivationInputAlternatives::from_row(vec![atom_a])),
                ]
                .into_iter()
                .collect()
            } else {
                HashMap::from([
                    (list_key.clone(), ActivationInputAlternatives::from_row(vec![atom_a])),
                    (
                        non_empty_key.clone(),
                        ActivationInputAlternatives::from_row(vec![atom_b]),
                    ),
                ])
            };
            map.conclude(
                world.types_mut(),
                publisher_b,
                HashSet::from([list_key.clone(), non_empty_key.clone()]),
                second,
                false,
            );
            (
                map.get(&list_key).expect("list contribution").rows()[0].columns()[0],
                map.get(&non_empty_key).expect("non-empty contribution").rows()[0].columns()[0],
                world.types().identity_inventory(),
            )
        };

        assert_eq!(run(false), run(true));
    }

    #[test]
    fn ground_dispatch_surfaces_resolves_a_publication_template_to_its_ground_dispatch() {
        // The Enum.with_index shape: a first-class publication template `(a0, a1)`
        // whose only real runtime dispatch is the ground sibling `(atom, int)`
        // collected among the direct surfaces, alongside phantom templates the
        // mapper picked up flowing through generic recursive code.
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let int = world.types_mut().int();
        let atom = world.types_mut().atom();
        let a0 = world.types_mut().type_var(TypeVarId(0));
        let a1 = world.types_mut().type_var(TypeVarId(1));

        let first_class = BTreeSet::from([surface(&[a0, a1], world.types_mut())]);
        let direct = BTreeSet::from([
            surface(&[atom, int], world.types_mut()),
            surface(&[a0, a0], world.types_mut()),
            surface(&[a0, a1], world.types_mut()),
        ]);
        let expected = BTreeSet::from([surface(&[atom, int], world.types_mut())]);

        assert_eq!(
            ground_dispatch_surfaces(world.types(), &first_class, &direct),
            expected,
            "a polymorphic publication template resolves to its single ground dispatch shape; the phantom templates publish no boundary",
        );
    }

    #[test]
    fn ground_dispatch_surfaces_drops_a_recurring_var_phantom_beside_a_ground_shape() {
        // A self-grounding demand set: `(atom, int)` is the real dispatch and
        // `(a0, a0)` is a phantom no distinct-argument ground pair instantiates.
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let int = world.types_mut().int();
        let atom = world.types_mut().atom();
        let a0 = world.types_mut().type_var(TypeVarId(0));

        let resolved = BTreeSet::from([
            surface(&[atom, int], world.types_mut()),
            surface(&[a0, a0], world.types_mut()),
        ]);
        let expected = BTreeSet::from([surface(&[atom, int], world.types_mut())]);

        assert_eq!(
            ground_dispatch_surfaces(world.types(), &resolved, &resolved),
            expected,
            "a ground dispatch shape exists, so the recurring-var phantom is dropped rather than published as its own boundary",
        );
    }

    #[test]
    fn ground_dispatch_surfaces_keeps_a_genuinely_polymorphic_escape() {
        // No ground sibling anywhere: a callable passed through but never invoked
        // at a concrete shape keeps its template — it is the only surface it is
        // ever published at.
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let a0 = world.types_mut().type_var(TypeVarId(0));
        let a1 = world.types_mut().type_var(TypeVarId(1));

        let template = BTreeSet::from([surface(&[a0, a1], world.types_mut())]);

        assert_eq!(
            ground_dispatch_surfaces(world.types(), &template, &template),
            template,
            "an escape with no ground instantiation keeps its template verbatim",
        );
    }

    #[test]
    fn runtime_demand_ignore_plus_resolved_callable_preserves_the_surface() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let int = world.types_mut().int();

        let joined =
            RuntimeDemand::ignore().join(&RuntimeDemand::callable(resolved_surface(&[int], world.types_mut())));

        assert_eq!(
            joined,
            RuntimeDemand::callable(CallableDemand::resolved(vec![int], world.types_mut())),
            "bottom must contribute nothing to callable demand",
        );
    }

    #[test]
    fn runtime_demand_resolved_callable_plus_escape_stays_callable_and_marks_first_class() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let int = world.types_mut().int();

        let joined = RuntimeDemand::callable(resolved_surface(&[int], world.types_mut()))
            .join(&RuntimeDemand::callable(CallableDemand::escaped()));

        assert_eq!(
            joined,
            RuntimeDemand::callable(CallableDemand {
                resolved: BTreeSet::from([CallableSurface::new(vec![int], world.types_mut())]),
                targets: BTreeSet::new(),
                opaque: false,
                escape: true,
            }),
            "escape is a first-class callable demand, not a reason to erase known surfaces",
        );
    }

    #[test]
    fn runtime_demand_tuple_fields_plus_whole_value_collapses_to_value() {
        let joined = RuntimeDemand::tuple_fields(vec![RuntimeDemand::whole(), RuntimeDemand::ignore()])
            .join(&RuntimeDemand::whole());

        assert_eq!(joined, RuntimeDemand::whole());
    }

    #[test]
    fn runtime_demand_callable_escape_preserves_known_resolved_surfaces() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let int = world.types_mut().int();
        let atom = world.types_mut().atom();

        let left = RuntimeDemand::callable(resolved_surface(&[int], world.types_mut()));
        let right = RuntimeDemand::callable(CallableDemand {
            resolved: BTreeSet::from([CallableSurface::new(vec![atom], world.types_mut())]),
            targets: BTreeSet::new(),
            opaque: false,
            escape: true,
        });
        let joined = left.join(&right);

        let expected_resolved = BTreeSet::from([
            CallableSurface::new(vec![atom], world.types_mut()),
            CallableSurface::new(vec![int], world.types_mut()),
        ]);
        assert_eq!(
            joined,
            RuntimeDemand::callable(CallableDemand {
                resolved: expected_resolved,
                targets: BTreeSet::new(),
                opaque: false,
                escape: true,
            }),
            "whole-value callable demand must keep any exact surfaces we already proved",
        );
    }

    #[test]
    fn activation_return_joins_within_an_epoch_and_narrows_only_on_rebase() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let mut activations = ActivationMap::new();
        let key = test_key(&mut world, &tel);
        let any = world.types_mut().any();
        let int = world.types_mut().int();

        assert!(
            activations
                .define_return(world.types_mut(), &key, Some(any), false)
                .changed
        );
        // Within an epoch evidence only ascends: int joins into any and
        // disappears — descent is unrepresentable without a ground shift.
        assert!(
            !activations
                .define_return(world.types_mut(), &key, Some(int), false)
                .changed
        );
        assert_eq!(activations.get(&key).and_then(|slot| slot.return_ty()), Some(&any));

        // The ground shifted (rebase): the fresh derivation replaces.
        assert!(
            activations
                .define_return(world.types_mut(), &key, Some(int), true)
                .changed
        );
        assert_eq!(activations.get(&key).and_then(|slot| slot.return_ty()), Some(&int));
    }

    #[test]
    fn activation_return_bottom_is_the_join_identity() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let mut activations = ActivationMap::new();
        let key = test_key(&mut world, &tel);
        let int = world.types_mut().int();

        // No evidence adds nothing — before and after real evidence lands.
        assert!(!activations.define_return(world.types_mut(), &key, None, false).changed);
        assert!(
            activations
                .define_return(world.types_mut(), &key, Some(int), false)
                .changed
        );
        assert!(!activations.define_return(world.types_mut(), &key, None, false).changed);
        assert_eq!(activations.get(&key).and_then(|slot| slot.return_ty()), Some(&int));
    }

    #[test]
    fn activation_return_join_ascends_by_union_and_republication_is_quiet() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let mut activations = ActivationMap::new();
        let key = test_key(&mut world, &tel);
        let int = world.types_mut().int();
        let atom = world.types_mut().atom();
        let both = world.types_mut().union(int, atom);

        assert!(
            activations
                .define_return(world.types_mut(), &key, Some(int), false)
                .changed
        );
        // Equal republication is quiet — the load-bearing scheduler
        // invariant: changed=false wakes nobody.
        assert!(
            !activations
                .define_return(world.types_mut(), &key, Some(int), false)
                .changed
        );
        assert!(
            activations
                .define_return(world.types_mut(), &key, Some(atom), false)
                .changed
        );
        assert_eq!(activations.get(&key).and_then(|slot| slot.return_ty()), Some(&both));
    }

    #[test]
    fn activation_return_join_preserves_closure_identity() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let mut activations = ActivationMap::new();
        let key = test_key(&mut world, &tel);
        let int = world.types_mut().int();
        let target = world.reference_function(super::super::super::identity::ModuleId::GLOBAL, "f", 1);
        let closure = world.closure_ty(target, vec![int]);

        assert!(
            activations
                .define_return(world.types_mut(), &key, Some(closure), false)
                .changed
        );
        assert!(
            activations
                .define_return(world.types_mut(), &key, Some(int), false)
                .changed
        );
        let joined = *activations
            .get(&key)
            .and_then(|slot| slot.return_ty())
            .expect("joined return");
        assert!(
            world.types_mut().callable_value_clauses(&joined).is_some(),
            "the union join must keep the closure identity resolvable",
        );
    }

    #[test]
    fn activation_return_widening_reports_only_real_coarsening() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let mut activations = ActivationMap::new();
        let key = test_key(&mut world, &tel);

        // Atom-by-atom growth ascends strictly but never builds a list
        // spine, so past the budget `convergence_class` is the identity:
        // crossing the threshold coarsens nothing and must not be reported
        // as widening.
        for index in 0..(2 * RETURN_WIDENING_BUDGET) {
            let atom = world.types_mut().atom_lit(&format!("a{index}"));
            let outcome = activations.define_return(world.types_mut(), &key, Some(atom), false);
            assert!(outcome.changed, "each fresh atom is a strict ascent");
            assert!(
                !outcome.widened,
                "round {index}: nothing was coarsened, so nothing may report as widened",
            );
        }

        // The ascent past twice the budget tops out at `any` — a real
        // coarsening, reported exactly once; at the top further evidence
        // joins quietly.
        let atom = world.types_mut().atom_lit("top");
        let outcome = activations.define_return(world.types_mut(), &key, Some(atom), false);
        assert!(outcome.changed && outcome.widened, "topping out at any IS a coarsening");
        let atom = world.types_mut().atom_lit("after");
        let outcome = activations.define_return(world.types_mut(), &key, Some(atom), false);
        assert!(
            !outcome.changed && !outcome.widened,
            "evidence joins quietly at the top"
        );
    }

    #[test]
    fn activation_return_widens_past_the_delay_and_terminates() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let mut activations = ActivationMap::new();
        let key = test_key(&mut world, &tel);

        // The canonical divergent ascent: ever-deeper list nests.
        let mut ty = world.types_mut().int();
        let mut widened_at = None;
        for round in 0..(2 * RETURN_WIDENING_BUDGET + 8) {
            ty = world.types_mut().list(ty);
            let outcome = activations.define_return(world.types_mut(), &key, Some(ty), false);
            if outcome.widened && widened_at.is_none() {
                widened_at = Some(round);
            }
            if !outcome.changed {
                // The ladder ended: a strictly-deepening ascent reached a
                // fixed point through the widening operator.
                assert!(widened_at.is_some(), "termination must come from widening");
                return;
            }
        }
        panic!("the widening operator must terminate a strictly-deepening ascent");
    }

    /// The ground instance of a closure literal at one signature: the same
    /// `fn_id` and captures, with the surface vars `closure_lit` mints for its
    /// parameters and return replaced by concrete types.
    fn ground_instance(world: &mut World, lambda: Ty, args: &[Ty], ret: Ty) -> Ty {
        let shape = world.types_mut().arrow(args, ret);
        let mut sigma = Sigma::new();
        world
            .types_mut()
            .collect_instantiation_subst(&lambda, &shape, &mut sigma);
        world.types_mut().instantiate(&lambda, &sigma)
    }

    /// Push rows into one antichain the way a publisher does, and read back the
    /// column vectors that survived.
    fn settled_rows(world: &mut World, rows: &[Vec<Ty>]) -> Vec<Vec<Ty>> {
        let mut alternatives = ActivationInputAlternatives::from_row(rows[0].clone());
        for row in &rows[1..] {
            alternatives.push_row(world.types_mut(), row.clone());
        }
        alternatives.rows().iter().map(|row| row.columns().to_vec()).collect()
    }

    /// fz-kdt.106: an ascent LADDER is one caller's history, not four
    /// alternatives.
    ///
    /// Every superseded conclusion of one callsite joins its row into the
    /// antichain and never leaves (`conclude_preserving_frontier`), so a
    /// column that widens over an epoch deposits one row per rung. The rungs
    /// are totally ordered -- each covers the one below -- so only the
    /// maximum carries evidence; the rest are the schedule's record of how it
    /// got there, and eight of them cross `ACTIVATION_INPUT_ROW_BUDGET` and
    /// collapse the whole set columnwise.
    #[test]
    fn activation_input_rows_keep_only_the_maximum_of_an_ascending_ladder() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let int = world.types_mut().int();
        let a = world.types_mut().atom_lit("a");
        let b = world.types_mut().atom_lit("b");
        let c = world.types_mut().atom_lit("c");
        let ab = world.types_mut().union(a, b);
        let abc = world.types_mut().union(ab, c);

        let rows = settled_rows(&mut world, &[vec![int, a], vec![int, ab], vec![int, abc]]);

        assert_eq!(
            rows,
            vec![vec![int, abc]],
            "an ascending ladder covers itself: only its maximum is an alternative",
        );
    }

    /// fz-kdt.106: absorption may not swallow a template row.
    ///
    /// A value-template row and its ground sibling are two DIFFERENT
    /// activations of one body -- the template mints the erased shared
    /// specialization, the ground row its representable instance -- and
    /// `is_subtype` treats a free var as absorbing, so bare subtyping would
    /// let the template eat its own instances and misroute the element
    /// families that depended on them (the `Enum.with_index` shape;
    /// `compiler2_jit_preserves_correlated_with_index_mapper_rows` is the
    /// artifact-level gate). Equal free-var SETS per column is what refuses
    /// it.
    #[test]
    fn activation_input_rows_keep_a_template_row_beside_its_ground_sibling() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let int = world.types_mut().int();
        let nil = world.types_mut().nil();
        let int_or_nil = world.types_mut().union(int, nil);
        let template = world.types_mut().closure_lit(ClosureTarget(7), Vec::new(), 1);
        let ground = ground_instance(&mut world, template, &[int], int);

        assert!(
            world.types().is_subtype(&template, &ground) && world.types().is_subtype(&ground, &template),
            "the hazard this test guards must actually exist: func_clause_empty judges a \
             var-carrying template arrow and its ground instance over one lambda equivalent",
        );

        assert_ne!(
            world.types().free_var_ids(&template),
            world.types().free_var_ids(&ground),
            "the template's surface vars are what tells the two apart",
        );

        let rows = settled_rows(&mut world, &[vec![int, template], vec![int_or_nil, ground]]);

        assert_eq!(
            rows.len(),
            2,
            "a template row and its ground sibling are two activations, not one: {rows:?}",
        );
    }

    /// fz-kdt.106: `is_subtype` cannot decide a closure-literal column, so
    /// dominance may not be "simplified" back to it.
    ///
    /// `types::emptiness::func_clause_empty` decides `P \ N` for a negative
    /// arrow carrying a `ClosureLit` from `fn_id` and `captures` ALONE -- it
    /// never reads `args` or `ret` -- so two arrows over ONE lambda are judged
    /// mutually subtypes however far apart their signatures are. Absorbing on
    /// that judgement drops a row whose reducer really is a different
    /// specialization. `Types::row_column_dominates` therefore requires the
    /// dominated column's closure-literal arrow shapes to appear verbatim in
    /// the dominator's, which is the part subtyping refuses to look at.
    #[test]
    fn activation_input_rows_keep_arrows_that_differ_only_where_subtyping_is_blind() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let int = world.types_mut().int();
        let nil = world.types_mut().nil();
        let int_or_nil = world.types_mut().union(int, nil);
        let lambda = world.types_mut().closure_lit(ClosureTarget(7), Vec::new(), 1);
        let narrow = ground_instance(&mut world, lambda, &[int], int);
        let wide = ground_instance(&mut world, lambda, &[int_or_nil], int);

        assert_ne!(narrow, wide, "the two reducer arrows must be distinct types");
        assert!(
            world.types().is_subtype(&narrow, &wide) && world.types().is_subtype(&wide, &narrow),
            "the hazard this test guards must actually exist: func_clause_empty judges two \
             signatures over one lambda equivalent",
        );

        assert_eq!(
            world.types().free_var_ids(&narrow),
            world.types().free_var_ids(&wide),
            "both arrows are ground, so free-var parity cannot be what keeps them apart -- the \
             literal SHAPE has to",
        );

        let rows = settled_rows(&mut world, &[vec![int, narrow], vec![int_or_nil, wide]]);

        assert_eq!(
            rows.len(),
            2,
            "two specializations of one lambda are two rows: subtyping is blind to the only \
             thing that tells them apart: {rows:?}",
        );
    }

    /// fz-kdt.106: the blind spot is STRUCTURAL, so the evidence has to be
    /// collected structurally.
    ///
    /// `func_clause_empty` reaches a lambda wrapped in a tuple exactly as it
    /// reaches a bare one, so `{:tag, fn}` columns over one lambda that differ
    /// only in the nested arrow's signature are mutually subtypes too. A
    /// `lit_arrow_shapes` that walked only the column's own funcs axis would
    /// report no shapes on either side, containment would hold vacuously both
    /// ways, and the pair would absorb -- the depth-0 sibling above, one tuple
    /// deep. Nothing in the corpus builds this row today; the walk is
    /// structural so that nothing has to.
    #[test]
    fn activation_input_rows_keep_nested_arrows_that_differ_only_where_subtyping_is_blind() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let int = world.types_mut().int();
        let nil = world.types_mut().nil();
        let int_or_nil = world.types_mut().union(int, nil);
        let tag = world.types_mut().atom_lit("tag");
        let lambda = world.types_mut().closure_lit(ClosureTarget(7), Vec::new(), 1);
        let narrow = ground_instance(&mut world, lambda, &[int], int);
        let wide = ground_instance(&mut world, lambda, &[int_or_nil], int);
        let narrow = world.types_mut().tuple(&[tag, narrow]);
        let wide = world.types_mut().tuple(&[tag, wide]);

        assert_ne!(narrow, wide, "the two wrapped reducer arrows must be distinct types");
        assert!(
            world.types().is_subtype(&narrow, &wide) && world.types().is_subtype(&wide, &narrow),
            "the hazard this test guards must actually exist: subtyping is blind to the nested \
             signature exactly as it is blind to a bare one",
        );
        assert_eq!(
            world.types().free_var_ids(&narrow),
            world.types().free_var_ids(&wide),
            "both wrapped arrows are ground, so free-var parity cannot be what keeps them apart",
        );
        assert!(
            !world.types().lit_arrow_shapes(&narrow).is_empty(),
            "the shapes have to be found THROUGH the tuple, or containment holds vacuously",
        );

        let rows = settled_rows(&mut world, &[vec![int, narrow], vec![int_or_nil, wide]]);

        assert_eq!(
            rows.len(),
            2,
            "a nested specialization is still a specialization: {rows:?}",
        );
    }
}

#[cfg(test)]
mod callsite_resolution_tests {
    use super::super::*;
    use crate::compiler2::identity::{FunctionId, RootId};

    fn key(callsite: u32, types: &mut Types) -> CallSiteKey {
        CallSiteKey {
            activation: ActivationKey::from_inputs(RootId::for_test(0), FunctionId::from_coordinate(1), &[], types),
            callsite: crate::compiler2::body::CallSiteId::from_u32(callsite),
        }
    }

    fn boundary_edge() -> CallSiteTargets {
        CallSiteTargets {
            targets: vec![CallTargetEdge {
                callee: SelectedCallee::ProviderBoundary(FunctionId::from_coordinate(7)),
                activation: None,
            }],
        }
    }

    /// fz-kdt.69.2: a reached callsite can give three answers, and they are
    /// three distinct values. A provider boundary is a RESOLVED edge that
    /// names no compiler2 activation; an unresolved callsite names no target
    /// at all; a callsite the walk never reached has no slot. Absence used to
    /// carry the last two together, so this state had no representation.
    #[test]
    fn an_unresolved_edge_is_neither_a_provider_boundary_nor_an_absent_one() {
        let mut types = Types::new();
        let boundary = CallSiteResolution::Resolved(boundary_edge());
        let unresolved: CallSiteResolution<CallSiteTargets> = CallSiteResolution::Unresolved;

        assert_ne!(boundary, unresolved);
        assert!(unresolved.is_unresolved());
        assert!(unresolved.resolved().is_none());
        assert!(
            boundary
                .resolved()
                .is_some_and(|targets| targets.targets[0].activation.is_none()),
            "a provider boundary is a named edge whose activation is None"
        );

        let mut map = CallSiteTargetsMap::new();
        let reached = key(0, &mut types);
        assert!(map.define(reached.clone(), CallSiteResolution::Unresolved));
        assert_eq!(map.get(&reached), Some(&CallSiteResolution::Unresolved));
        assert_eq!(
            map.get(&key(1, &mut types)),
            None,
            "a callsite the walk never reached has no slot at all"
        );
        assert_eq!(map.resolved(&reached), None, "an unresolved edge names no targets");
    }

    /// `Unresolved` is the lattice BOTTOM: re-emitting it moves nothing, and
    /// it never erases the resolved answer a previous round reached. That is
    /// what lets `preserved_analysis_claims` stop carrying these two kinds.
    #[test]
    fn an_unresolved_re_emission_is_quiet_and_resolving_one_is_a_content_change() {
        let mut types = Types::new();
        let mut map = CallSiteTargetsMap::new();
        let key = key(0, &mut types);

        assert!(
            map.define(key.clone(), CallSiteResolution::Unresolved),
            "the first appearance of a reached callsite is a content change"
        );
        assert!(
            !map.define(key.clone(), CallSiteResolution::Unresolved),
            "re-emitting the same unresolved answer must not bump the revision"
        );
        assert!(
            map.define(key.clone(), CallSiteResolution::Resolved(boundary_edge())),
            "unresolved -> resolved IS a content change, and must wake the readers"
        );
        assert!(
            !map.define(key.clone(), CallSiteResolution::Unresolved),
            "a later round that resolved nothing must not descend"
        );
        assert_eq!(
            map.resolved(&key),
            Some(&boundary_edge()),
            "the resolved answer stands at its own revision"
        );
    }
}
