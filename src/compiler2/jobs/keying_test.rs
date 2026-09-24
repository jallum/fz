//! Definition-owned source equations and input demand, read through their
//! published facts before activation keying consumes them.
//!
//! The demand fact is what activation keying asks before it decides whether a
//! slot's arriving type is meaning or freight, so the statements here are
//! about the demand one body publishes, not about the keys any later job
//! derives from it.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;

use crate::compiler2::body::{CallSiteId, ControlDestination, ControlEntryId, ValueId};
use crate::compiler2::dump::DumpStage;
use crate::compiler2::facts::FactUse;
use crate::compiler2::return_skeleton::{FunctionSkeleton, Invocation, InvocationCallee, Returns, Skeleton};
use crate::compiler2::{
    CodeSubmission, Compiler2, ExecutableNeed, FactKey, FunctionId, InputDemand, ModuleId, RootSubmission, World,
};
use crate::dispatch_matrix::demand::DispatchDemand;
use crate::telemetry::ConfiguredTelemetry;

/// Drives one program the way every door does and returns the `InputDemand`
/// each function ended up with, by label.
///
/// The fact is observed through its own telemetry (`input_demand/derived`)
/// rather than reached for in the world, so a re-derivation is visible as the
/// later value and the test reads exactly what a consumer of the fact reads.
fn input_demands(name: &str, source: &str) -> BTreeMap<String, InputDemand> {
    let tel = ConfiguredTelemetry::new();
    let derived: Rc<RefCell<Vec<(FunctionId, InputDemand)>>> = Rc::new(RefCell::new(Vec::new()));
    let sink = Rc::clone(&derived);
    tel.attach_raw_event2::<FunctionId, InputDemand, _>(
        &["fz", "compiler2", "input_demand", "derived"],
        move |_, _, _, function, demand| {
            sink.borrow_mut().push((*function, demand.clone()));
        },
    );

    let mut compiler = Compiler2::new(tel);
    compiler.set_drive_timeout(std::time::Duration::from_secs(30));
    compiler.submit_code(CodeSubmission {
        name: Some(name.to_string()),
        text: source.to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .drive_root_to_dump_stage(root, DumpStage::Backend)
        .unwrap_or_else(|error| panic!("{name} should reach a backend program: {error}"));

    let world = compiler.world();
    derived
        .borrow()
        .iter()
        .map(|(function, demand)| {
            (
                crate::compiler2::canon::function_label(world, *function),
                demand.clone(),
            )
        })
        .collect()
}

fn demand_of(demands: &BTreeMap<String, InputDemand>, label: &str) -> InputDemand {
    demands
        .get(label)
        .unwrap_or_else(|| {
            panic!(
                "{label} should have published an input demand, saw {:?}",
                demands.keys()
            )
        })
        .clone()
}

/// A source equation has the function's stable identity before it has a
/// definition. Definition arrival and replacement supply its relationship;
/// neither discovery needs an activation of that function or a caller's
/// concrete types. Expanding `def` itself still runs its compile-time code.
#[test]
fn a_referenced_source_equation_waits_for_definition_and_tracks_replacement() {
    use crate::compiler2::drive::{ExecutionContext, Job};
    use crate::compiler2::pull::ProductSessions;
    use crate::compiler2::scheduler::DriveOutcome;

    let tel = ConfiguredTelemetry::new();
    let runs = Rc::new(RefCell::new(Vec::<Job>::new()));
    let sink = Rc::clone(&runs);
    tel.attach_raw_event2::<World, crate::compiler2::JobCompletion, _>(
        &["fz", "compiler2", "work_graph", "applied"],
        move |_, _, _, _, completion| sink.borrow_mut().push(completion.job.clone()),
    );
    let mut world = World::new();
    let mut sessions = ProductSessions::default();
    let first = world.reference_function(ModuleId::GLOBAL, "first", 2);
    world.demand(Job::DeriveReturnSkeleton(first));
    let DriveOutcome::Unresolved { waits } =
        ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive()
    else {
        panic!("an equation referenced before its definition must remain pending");
    };
    assert!(
        world.return_skeleton(first).is_none(),
        "a referenced but undefined equation is pending, not an opaque or bottom equation"
    );
    assert!(!world.has_fact(&FactKey::ReturnSkeleton(first)));
    assert!(
        waits.iter().any(|wait| {
            wait.jobs.contains(&Job::DeriveReturnSkeleton(first))
                && wait.fact == crate::compiler2::drive::fact_dependency(FactUse::current(FactKey::LoweredBody(first)))
        }),
        "the pending equation must subscribe to the definition's lowered body"
    );

    for (returned, slot) in [("x", 0), ("y", 1)] {
        let source = world.submit_code(
            Some("source-equation-lifecycle.fz".into()),
            format!("def first(x, y), do: {returned}\n"),
        );
        world.demand(Job::ScopeCode(source));
        assert!(matches!(
            ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive(),
            DriveOutcome::Resolved
        ));
        assert_eq!(world.reference_function(ModuleId::GLOBAL, "first", 2), first);
        let skeleton = world
            .return_skeleton(first)
            .expect("definition arrival must publish its equation");
        assert_eq!(skeleton.input_len, 2);
        let Returns::Entries(entries) = &skeleton.returns else {
            panic!("a defined projection must publish a source relationship");
        };
        assert_eq!(entries.len(), 1);
        assert_eq!(
            entries.values().next(),
            Some(&Skeleton::Input(slot)),
            "definition replacement must rederive the relationship at the same equation reference"
        );
    }
    assert!(
        runs.borrow()
            .iter()
            .all(|job| !matches!(job, Job::AnalyzeActivation(key) if key.function == first)),
        "source equation discovery and replacement must not analyze first/2"
    );
}

#[test]
fn replacing_a_source_operation_changes_the_equation_at_the_same_result_position() {
    use crate::compiler2::drive::{ExecutionContext, Job};
    use crate::compiler2::pull::ProductSessions;
    use crate::compiler2::scheduler::DriveOutcome;

    let tel = ConfiguredTelemetry::new();
    let runs = Rc::new(RefCell::new(Vec::<Job>::new()));
    let sink = Rc::clone(&runs);
    tel.attach_raw_event2::<World, crate::compiler2::JobCompletion, _>(
        &["fz", "compiler2", "work_graph", "applied"],
        move |_, _, _, _, completion| sink.borrow_mut().push(completion.job.clone()),
    );
    let mut world = World::new();
    let mut sessions = ProductSessions::default();
    let invert = world.reference_function(ModuleId::GLOBAL, "invert", 2);
    world.demand(Job::DeriveReturnSkeleton(invert));
    let mut previous = None::<Rc<FunctionSkeleton>>;
    let mut previous_revision = None;
    for (operand, slot) in [("x", 0), ("y", 1)] {
        let source = world.submit_code(
            Some("source-operation-replacement.fz".into()),
            format!("def invert(x, y), do: not {operand}\n"),
        );
        world.demand(Job::ScopeCode(source));
        assert!(matches!(
            ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive(),
            DriveOutcome::Resolved
        ));
        assert_eq!(world.reference_function(ModuleId::GLOBAL, "invert", 2), invert);
        let next = world
            .return_skeleton(invert)
            .expect("the source equation must be published");
        let body = next
            .body
            .as_ref()
            .expect("a defined equation must retain its source operations");
        assert!(Rc::ptr_eq(body, &world.lowered_body(invert)));
        let crate::compiler2::body::LoweredBody::Clauses { clauses, .. } = &**body else {
            panic!("invert/2 must have a source body");
        };
        let Returns::Entries(returns) = &next.returns else {
            panic!("invert/2 must return from its source entry");
        };
        assert_eq!(returns.len(), 1);
        let Skeleton::Ground(result) = returns.values().next().unwrap() else {
            panic!("the result must refer to its source operation");
        };
        let site = body
            .value_definition_site(*result)
            .expect("the operation must define its result");
        let crate::compiler2::body::LoweredStep::UnaryOp { op, input, .. } = body.step_at(site) else {
            panic!("the result must retain the not operation");
        };
        assert_eq!(*op, crate::ast::UnOp::Not);
        assert_eq!(*input, clauses[0].params[slot]);
        let revision = world.fact_revision(&FactKey::ReturnSkeleton(invert));
        if let Some(previous) = previous {
            assert_eq!(previous.returns, next.returns, "the result position did not move");
            assert_eq!(
                previous.invocations, next.invocations,
                "neither definition invokes a function"
            );
            assert_ne!(
                previous_revision, revision,
                "equation subscribers must see the changed operation"
            );
            let previous_body = previous.body.as_ref().unwrap();
            assert_eq!(previous_body.value_definition_site(*result), Some(site));
            let crate::compiler2::body::LoweredStep::UnaryOp { input: prior_input, .. } = previous_body.step_at(site)
            else {
                panic!("the prior equation must retain its own operation");
            };
            assert_eq!(
                *prior_input, clauses[0].params[0],
                "replacement must not mutate the prior equation"
            );
            assert_ne!(
                &previous, next,
                "changing an operation's operand must change the source equation even at the same result position"
            );
        }
        previous = Some(Rc::clone(next));
        previous_revision = revision;
    }
    assert!(
        runs.borrow()
            .iter()
            .all(|job| !matches!(job, Job::AnalyzeActivation(key) if key.function == invert)),
        "an operation's definition must be available before analyzing invert/2"
    );
}

#[test]
fn replacing_a_source_condition_changes_the_equation_without_changing_its_returns() {
    use crate::compiler2::body::{LoweredBody, LoweredTail};
    use crate::compiler2::drive::{ExecutionContext, Job};
    use crate::compiler2::pull::ProductSessions;
    use crate::compiler2::scheduler::DriveOutcome;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let mut sessions = ProductSessions::default();
    let choose = world.reference_function(ModuleId::GLOBAL, "choose", 4);
    world.demand(Job::DeriveReturnSkeleton(choose));
    let mut previous = None::<Rc<FunctionSkeleton>>;
    for (condition, slot) in [("x", 0), ("y", 1)] {
        let source = world.submit_code(
            Some("source-condition-replacement.fz".into()),
            format!("def choose(x, y, a, b), do: if {condition}, do: a, else: b\n"),
        );
        world.demand(Job::ScopeCode(source));
        assert!(matches!(
            ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive(),
            DriveOutcome::Resolved
        ));
        let next = world
            .return_skeleton(choose)
            .expect("the source equation must be published");
        let body = next
            .body
            .as_ref()
            .expect("the equation must retain return prerequisites");
        assert!(Rc::ptr_eq(body, &world.lowered_body(choose)));
        let LoweredBody::Clauses { clauses, entries, .. } = &**body else {
            panic!("choose/4 must have a source body");
        };
        let LoweredTail::If {
            cond,
            then_entry,
            else_entry,
        } = entries[clauses[0].entry.as_u32() as usize].tail
        else {
            panic!("the return alternatives must retain their source condition");
        };
        assert_eq!(cond, clauses[0].params[slot]);
        let Returns::Entries(returns) = &next.returns else {
            panic!("choose/4 must retain its returning entries");
        };
        assert_eq!(returns.get(&then_entry), Some(&Skeleton::Input(2)));
        assert_eq!(returns.get(&else_entry), Some(&Skeleton::Input(3)));
        if let Some(previous) = previous {
            assert_eq!(previous.returns, next.returns);
            assert_eq!(previous.invocations, next.invocations);
            assert_ne!(
                &previous, next,
                "which input controls the returning entry is part of the equation"
            );
        }
        previous = Some(Rc::clone(next));
    }
}

#[test]
fn an_absent_transitive_return_reads_its_definition_for_rediscovery() {
    use crate::compiler2::drive::{ExecutionContext, Job, JobEffects};
    use crate::compiler2::pull::ProductSessions;
    use crate::compiler2::scheduler::DriveOutcome;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let mut sessions = ProductSessions::default();
    let source = world.submit_code(Some("late_return_body.fz".into()), "def later(_value), do: 0\n".into());
    world.demand(Job::ScopeCode(source));
    assert!(matches!(
        ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive(),
        DriveOutcome::Resolved
    ));
    let caller = world.reference_function(ModuleId::GLOBAL, "caller", 1);
    let later = world.reference_function(ModuleId::GLOBAL, "later", 1);
    assert!(world.function_defined_revision(later).is_none());
    let callsite = CallSiteId::from_u32(0);
    let entry = ControlEntryId::from_u32(0);
    assert!(world.define_return_skeleton(
        caller,
        Rc::new(FunctionSkeleton {
            body: None,
            returns: Returns::Entries(BTreeMap::from([(
                entry,
                Skeleton::Result {
                    callsite,
                    value: ValueId::from_u32(0),
                },
            )])),
            invocations: BTreeMap::from([(
                callsite,
                Invocation {
                    entry,
                    callee: InvocationCallee::Named(later),
                    arguments: vec![Skeleton::Input(0)],
                    result: ValueId::from_u32(0),
                    destination: ControlDestination::Return,
                },
            )]),
            input_len: 1,
        }),
    ));
    // Supply only the caller's static description so definition discovery can
    // be staged independently of lowering a source-level direct call.
    world.complete_job(
        Job::DeriveReturnSkeleton(caller),
        JobEffects {
            outputs: vec![FactKey::ReturnSkeleton(caller)],
            changed: vec![FactKey::ReturnSkeleton(caller)],
            ..JobEffects::default()
        },
    );
    world.demand(Job::DeriveReturnUnknowns(caller));
    assert!(matches!(
        ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive(),
        DriveOutcome::Resolved
    ));
    assert!(world.return_unknowns(caller).unwrap().returns_input(0));
    assert!(world.return_skeleton(later).is_none());
    let reads = world.job_reads(&Job::DeriveReturnUnknowns(caller));
    assert!(reads.contains(&FactUse::current(FactKey::ReturnSkeleton(later))));
    assert!(reads.contains(&FactUse::current(FactKey::FunctionDefined(later))));

    world.demand(Job::DefineFunction(later));
    assert!(matches!(
        ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).drive(),
        DriveOutcome::Resolved
    ));
    assert!(
        world.return_skeleton(later).is_some(),
        "definition arrival must demand the real return skeleton"
    );
    assert!(
        !world.return_unknowns(caller).unwrap().returns_input(0),
        "the definition's arrival must refine possible flow to the constant body's proven non-dependence"
    );
}

/// A closure call cannot be answered statically, so every value it touches is
/// a question this body asks: which callable arrived decides which body runs,
/// and that body decides what it makes of the arguments handed to it. Both the
/// called slot and the argument slot therefore carry `Whole` demand, raised
/// where the call is, before any forwarding is joined in.
#[test]
fn a_closure_call_asks_a_whole_question_of_the_callable_and_of_what_it_is_handed() {
    let demands = input_demands(
        "closure call demand",
        "def call2(x, f), do: f.(x)\n\
         def main() do\n  dbg(call2(1, fn (a) -> a + 1 end))\nend\n",
    );

    let call2 = demand_of(&demands, "call2/2");
    assert_eq!(
        call2.forwarded_dispatch,
        vec![DispatchDemand::Whole, DispatchDemand::Whole],
        "calling slot 1 and handing it slot 0 is a question about both slots",
    );
}

/// A body that only TRANSPORTS a value asks nothing of it itself; what it
/// depends on is what the callee it hands the value to asks. The published
/// demand is that callee's, inherited through the forwarding fixpoint with no
/// second walk -- which is why a forwarder's callable slot is asked about here
/// and its brand survives to the callee that calls it.
#[test]
fn a_forwarder_inherits_what_its_callee_asks() {
    let demands = input_demands(
        "forwarded closure call demand",
        "def call2(x, f), do: f.(x)\n\
         def fwd(f, x), do: call2(x, f)\n\
         def main() do\n  dbg(fwd(fn (a) -> a + 1 end, 1))\nend\n",
    );

    let fwd = demand_of(&demands, "fwd/2");
    assert_eq!(
        fwd.forwarded_dispatch,
        vec![DispatchDemand::Whole, DispatchDemand::Whole],
        "both inputs reach call2/2, which calls one and hands it the other",
    );
}

#[test]
fn inline_dispatch_observes_its_input_and_its_forwarders() {
    let demands = input_demands(
        "inline dispatch demand",
        "def choose(x) do\n case x do\n :a -> 1\n _ -> 2\n end\nend\n\
         def forward(x), do: choose(x)\ndef main(), do: forward(:a)\n",
    );
    for name in ["choose/1", "forward/1"] {
        assert_eq!(
            demand_of(&demands, name).forwarded_dispatch,
            vec![DispatchDemand::Whole]
        );
    }
}

#[test]
fn inline_dispatch_pulls_a_projected_observation_back_to_its_input() {
    let demands = input_demands(
        "projected inline dispatch demand",
        "def choose(pair) do\n {x, _} = pair\n case x do\n :a -> 1\n _ -> 2\n end\nend\n\
         def main(), do: choose({:a, :freight})\n",
    );
    assert_eq!(
        demand_of(&demands, "choose/1").forwarded_dispatch,
        vec![DispatchDemand::TupleFields]
    );
}

#[test]
fn an_inline_condition_observes_the_operands_of_its_computation() {
    let demands = input_demands(
        "computed condition demand",
        "def choose(x, freight), do: if x == :a, do: freight, else: :no\n\
         def main(), do: choose(:a, :ok)\n",
    );
    assert_eq!(
        demand_of(&demands, "choose/2").forwarded_dispatch,
        vec![DispatchDemand::Whole, DispatchDemand::Ignore]
    );
}

#[test]
fn a_closure_call_observes_a_projected_argument() {
    let demands = input_demands(
        "projected closure argument demand",
        "def apply(pair, f) do\n {x, _} = pair\n f.(x)\nend\n\
         def main(), do: apply({1, :freight}, fn (x) -> x + 1 end)\n",
    );
    assert_eq!(
        demand_of(&demands, "apply/2").forwarded_dispatch,
        vec![DispatchDemand::TupleFields, DispatchDemand::Whole]
    );
}

#[test]
fn an_observed_call_result_pulls_demand_back_to_its_arguments() {
    let demands = input_demands(
        "observed call result demand",
        "def identity(x), do: x\n\
         def choose(x) do\n case identity(x) do\n :a -> 1\n _ -> 2\n end\nend\n\
         def main(), do: choose(:a)\n",
    );
    assert_eq!(
        demand_of(&demands, "choose/1").forwarded_dispatch,
        vec![DispatchDemand::Whole]
    );
}

#[test]
fn a_recursive_list_tail_preserves_list_shape_demand() {
    let demands = input_demands(
        "recursive list tail demand",
        "def walk([]), do: :ok\ndef walk([_ | tail]), do: walk(tail)\n\
         def main(), do: walk([1, 2, 3])\n",
    );
    assert_eq!(
        demand_of(&demands, "walk/1").forwarded_dispatch,
        vec![DispatchDemand::ListShape]
    );
}

#[test]
fn replacing_an_inline_question_rederives_its_forwarders_demand() {
    let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
    compiler.set_drive_timeout(std::time::Duration::from_secs(30));
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let forward = compiler.world_mut().reference_function(ModuleId::GLOBAL, "forward", 1);
    for (body, expected) in [
        ("1", DispatchDemand::Ignore),
        ("case x do\n :a -> 1\n _ -> 2\nend", DispatchDemand::Whole),
        ("1", DispatchDemand::Ignore),
    ] {
        compiler.submit_code(CodeSubmission {
            name: Some("inline-demand-replacement.fz".into()),
            text: format!("def choose(x), do: {body}\ndef forward(x), do: choose(x)\ndef main(), do: forward(:a)\n"),
        });
        compiler.drive_root_to_dump_stage(root, DumpStage::Backend).unwrap();
        assert_eq!(
            compiler.world().input_demand(forward).unwrap().forwarded_dispatch,
            vec![expected],
            "adding or removing a source observation must replace the forwarder's demand"
        );
    }
}

#[test]
fn an_observed_join_keeps_each_call_results_input_dependencies() {
    let demands = input_demands(
        "observed joined call result demand",
        "def identity(x), do: x\n\
         def choose(flag, x) do\n y = if flag, do: identity(x), else: :fixed\n\
         case y do\n :a -> 1\n _ -> 2\n end\nend\n\
         def main(), do: choose(true, :a)\n",
    );
    assert_eq!(
        demand_of(&demands, "choose/2").forwarded_dispatch,
        vec![DispatchDemand::Whole, DispatchDemand::Whole]
    );
}

#[test]
fn an_inline_case_on_a_list_tail_preserves_shape_demand() {
    let demands = input_demands(
        "inline list tail shape demand",
        "def last?([_ | tail]) do\n case tail do\n [] -> true\n _ -> false\n end\nend\n\
         def main(), do: last?([1, 2])\n",
    );
    assert_eq!(
        demand_of(&demands, "last?/1").forwarded_dispatch,
        vec![DispatchDemand::ListShape]
    );
}
