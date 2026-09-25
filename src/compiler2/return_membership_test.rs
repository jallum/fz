//! Which activations solve their returns together, watched while the answer
//! is still forming.
//!
//! The settled answer is the easy one. The interesting moment is earlier: a
//! call site the walk has reached but not yet named a target for could still
//! reach anything at all, so a membership drawn across one is only part of
//! an answer. These tests watch one program's whole drive and ask the
//! question after every job, not just at the end.

use std::cell::RefCell;
use std::rc::Rc;

use super::*;
use crate::compiler2::canon::function_label;
use crate::compiler2::dump::DumpStage;
use crate::compiler2::identity::ModuleId;
use crate::compiler2::semantic::CallSiteResolution;
use crate::compiler2::{
    CodeSubmission, Compiler2, DependencyKey, ExecutableNeed, FunctionId, Job, JobCompletion, RootSubmission,
};
use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

/// Every call site this activation's walk reached and has not named a
/// target for. These are its unknown edges: the walk stood there, and what
/// the call reaches is still to be said.
fn unnamed_call_sites(world: &World, activation: &ActivationKey) -> Vec<CallSiteKey> {
    super::static_callsites(world, activation)
        .into_iter()
        .map(|callsite| CallSiteKey {
            activation: activation.clone(),
            callsite,
        })
        .filter(|key| {
            world
                .callsite_target_resolution(key)
                .is_some_and(CallSiteResolution::is_unresolved)
        })
        .collect()
}

/// The one activation this program settled for `function`.
fn sole_activation(world: &World, function: FunctionId, label: &str) -> ActivationKey {
    let mut matches: Vec<ActivationKey> = world
        .activation_keys()
        .into_iter()
        .filter(|key| key.function == function)
        .collect();
    assert_eq!(
        matches.len(),
        1,
        "{label} should settle one activation, found {matches:?}"
    );
    matches.pop().expect("one match")
}

/// The members of `seed`'s component, by function label, in semantic order.
fn member_labels(world: &World, seed: &ActivationKey) -> Option<Vec<String>> {
    let component = world.return_membership(seed).into_component()?;
    Some(
        component
            .members
            .iter()
            .map(|member| function_label(world, member.function))
            .collect(),
    )
}

/// A membership is an answer about edges, so it cannot be given while an
/// edge is unknown.
///
/// `dup/1` hands its own recursive result to `wrap/1`, so the two solve one
/// system. On `dup/1`'s first walks the call that says so has been reached
/// and has named no target yet: whatever it turns out to reach may join the
/// set, so the set is not yet a component and nobody owns it. Once the call
/// names `wrap/1`, the same seed has its component -- both members, owned by
/// the one canonical owner.
#[test]
fn a_membership_is_not_answered_across_a_call_site_that_has_named_no_target() {
    let tel = ConfiguredTelemetry::new();
    // A component answered while one of its members still had an unknown
    // edge: the answer could not have been whole.
    let partial: Rc<RefCell<Vec<String>>> = Rc::new(RefCell::new(Vec::new()));
    // Every activation ever seen with an unknown edge of its own, so the
    // test can prove the window it is about really occurred.
    let unknown_edged: Rc<RefCell<Vec<ActivationKey>>> = Rc::new(RefCell::new(Vec::new()));
    let partial_sink = Rc::clone(&partial);
    let unknown_sink = Rc::clone(&unknown_edged);
    tel.attach_raw_event2::<World, JobCompletion, _>(
        &["fz", "compiler2", "work_graph", "applied"],
        move |_, _, _, world, _| {
            for key in world.activation_keys() {
                if !unnamed_call_sites(world, &key).is_empty() && !unknown_sink.borrow().contains(&key) {
                    unknown_sink.borrow_mut().push(key.clone());
                }
                let Some(component) = world.return_membership(&key).into_component() else {
                    continue;
                };
                for member in &component.members {
                    for site in unnamed_call_sites(world, member) {
                        partial_sink.borrow_mut().push(format!(
                            "{} was answered a component owned by {} while {}'s call site {:?} had named no target",
                            function_label(world, key.function),
                            function_label(world, component.owner.function),
                            function_label(world, member.function),
                            site.callsite,
                        ));
                    }
                }
            }
        },
    );

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("wrapped_recursive_return.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/wrapped_recursive_return.fz").to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .drive_root_to_dump_stage(root, DumpStage::Backend)
        .unwrap_or_else(|error| panic!("wrapped_recursive_return should reach a backend program: {error}"));

    let world = compiler.world_mut();
    let dup_function = world.reference_function(ModuleId::GLOBAL, "dup", 1);
    let wrap_function = world.reference_function(ModuleId::GLOBAL, "wrap", 1);
    let dup = sole_activation(world, dup_function, "dup/1");
    let wrap = sole_activation(world, wrap_function, "wrap/1");

    assert!(
        unknown_edged.borrow().contains(&dup),
        "the window this test is about must occur: dup/1's recursive call is reached before it names a target, \
         seen instead at {:?}",
        unknown_edged.borrow(),
    );
    assert!(
        partial.borrow().is_empty(),
        "no component may be answered while a member's edge is unknown:\n{}",
        partial.borrow().join("\n"),
    );
    assert_eq!(
        member_labels(world, &dup),
        Some(vec!["wrap/1".to_string(), "dup/1".to_string()]),
        "once every call site has named its targets, the same seed has its whole component",
    );
    assert_eq!(
        world
            .return_membership(&dup)
            .into_component()
            .map(|component| component.owner),
        Some(wrap),
        "and one canonical owner publishes both members' returns",
    );
}

/// The whole point of walking outward from a seed instead of scanning every
/// activation the world holds is that the walk's cost tracks the
/// COMPONENT and its immediate callers, not the world. `wrap/1` and `dup/1`
/// are the only two activations `wrapped_recursive_return.fz` ever solves a
/// return for together, and `main/0` is the one caller `dup/1` has --
/// `Callers(dup/1)` lists main's call site, and the walk examines it every
/// time it walks `dup/1`'s in-edges, even though `main/0` never joins the
/// component: `main/0` is not itself on any return cycle, so its own
/// `ReturnUnknowns` calls the site settled, and the candidate is ruled back
/// out. That examination is still part of what the walk cost, so `visited`
/// counts it, and no `return_membership.discovered` dispatch over the whole
/// drive should ever report having touched more than these three
/// activations to answer either one's membership.
#[test]
fn discovery_visits_only_the_component_it_answers_for() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &["fz", "compiler2", "return_membership", "discovered"]);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("wrapped_recursive_return.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/wrapped_recursive_return.fz").to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .drive_root_to_dump_stage(root, DumpStage::Backend)
        .unwrap_or_else(|error| panic!("wrapped_recursive_return should reach a backend program: {error}"));

    let visited: Vec<u64> = capture
        .events()
        .iter()
        .filter_map(|event| match event.measurements.get("visited") {
            Some(Value::U64(visited)) => Some(*visited),
            _ => None,
        })
        .collect();
    assert!(
        !visited.is_empty(),
        "the drive should have discovered dup/1's and wrap/1's membership at least once",
    );
    assert_eq!(
        visited.iter().copied().max(),
        Some(3),
        "every discovery over this program should touch at most its two-member component \
         plus dup/1's one caller, not {visited:?}",
    );
}

/// The registration blind spot: `decode/1`'s own activation does not exist
/// the first time `skip_ws/1`'s component walks, so a membership answer
/// drawn from every activation the world currently holds cannot see the call
/// site that later makes `decode/1` a member. `projected_recursive_result.fz`
/// is built so that is exactly what happens. This watches every
/// `work_graph.applied` completion's own published facts -- the same signal
/// `pub.py`'s census reads, not a second walk of its own -- and requires
/// `decode/1`'s `ReturnType` to be published only by the component's
/// `SolveReturnComponent`, never by `decode/1`'s own `AnalyzeActivation`. A
/// whole-world scan would let `AnalyzeActivation` self-publish it instead,
/// which a later solve then has to clear and republish.
#[test]
fn decode_never_self_publishes_the_return_the_solve_owns() {
    let tel = ConfiguredTelemetry::new();
    let self_published: Rc<RefCell<u64>> = Rc::new(RefCell::new(0));
    let solved: Rc<RefCell<u64>> = Rc::new(RefCell::new(0));
    let self_sink = Rc::clone(&self_published);
    let solved_sink = Rc::clone(&solved);
    let decode_function: Rc<RefCell<Option<FunctionId>>> = Rc::new(RefCell::new(None));
    let decode_sink = Rc::clone(&decode_function);
    tel.attach_raw_event2::<World, JobCompletion, _>(
        &["fz", "compiler2", "work_graph", "applied"],
        move |_, _, _, _world, completion| {
            let Some(decode) = *decode_sink.borrow() else {
                return;
            };
            for change in &completion.step.changed {
                let DependencyKey::Fact(FactKey::ReturnType(activation)) = &change.key else {
                    continue;
                };
                if activation.function != decode || change.new_revision.is_none() {
                    continue;
                }
                match &completion.job {
                    Job::AnalyzeActivation(_) => *self_sink.borrow_mut() += 1,
                    Job::SolveReturnComponent(_) => *solved_sink.borrow_mut() += 1,
                    other => panic!("decode/1's ReturnType was published by an unexpected job {other:?}"),
                }
            }
        },
    );

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("projected_recursive_result.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/projected_recursive_result.fz").to_string(),
    });
    *decode_function.borrow_mut() = Some(compiler.world_mut().reference_function(ModuleId::GLOBAL, "decode", 1));
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .drive_root_to_dump_stage(root, DumpStage::Backend)
        .unwrap_or_else(|error| panic!("projected_recursive_result should reach a backend program: {error}"));

    assert_eq!(
        *self_published.borrow(),
        0,
        "decode/1's own AnalyzeActivation must never publish its ReturnType",
    );
    assert!(
        *solved.borrow() > 0,
        "decode/1's ReturnType should be published by the component's SolveReturnComponent instead",
    );
}
