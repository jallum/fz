//! Ticket .10 acceptance at the ordinary source/compiler/backend boundary.
//!
//! Recovered by intent from off-the-rails drive_test's same-interface apply,
//! incompatible result, twice, following tuple, and complete reducer tests.
//! No abandoned StepEquation/continuation-arena API is required here. Owner
//! publication is only one measurement: actual-work telemetry is a separate gate.

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::rc::Rc;

use super::artifact::BackendExecutable;
use super::drive_test::CallsiteCapture;
use super::pull::{ProductKey, ProductSettlement, ProductValue};
use super::{
    AbiValueRepr, ActivationKey, BackendProgram, CallSiteKey, CallSiteSummary, CodeSubmission, Compiler2,
    ExecutableNeed, FunctionId, LoweredStep, RootSubmission, StepSite, World,
};
use crate::exec::runtime::DbgCapture;
use crate::telemetry::ConfiguredTelemetry;

struct Witness {
    compiler: Compiler2<ConfiguredTelemetry>,
    program: Rc<BackendProgram>,
    analyzed: HashSet<ActivationKey>,
    calls: HashMap<CallSiteKey, CallSiteSummary>,
    tuple_attempts: Vec<(FunctionId, StepSite)>,
}

fn witness(name: &str) -> Witness {
    let folder = concat!(env!("CARGO_MANIFEST_DIR"), "/fixtures2/behavior/interface10_");
    let source = std::fs::read_to_string(format!("{folder}{name}.fz")).expect("source witness");
    let expected = std::fs::read_to_string(format!("{folder}{name}.expected.txt")).expect("expected output");
    let telemetry = ConfiguredTelemetry::new();
    let tuple_attempts = Rc::new(RefCell::new(Vec::new()));
    let sink = Rc::clone(&tuple_attempts);
    telemetry.attach_raw_event3::<ActivationKey, StepSite, LoweredStep, _>(
        &["fz", "compiler2", "inference_work", "step_transfer_attempt"],
        move |_, _, _, owner, site, step| {
            if matches!(step, LoweredStep::Tuple { .. }) {
                sink.borrow_mut().push((owner.function, *site));
            }
        },
    );
    let analyses = Rc::new(RefCell::new(HashSet::new()));
    let sink = Rc::clone(&analyses);
    telemetry.attach_raw_event2::<World, ActivationKey, _>(
        &["fz", "compiler2", "activation_analysis", "defined"],
        move |_, _, _, _, key| {
            sink.borrow_mut().insert(key.clone());
        },
    );
    let backend = Rc::new(RefCell::new(None));
    let sink = Rc::clone(&backend);
    telemetry.attach_raw_event3::<ProductKey, ProductValue, ProductSettlement, _>(
        &["fz", "compiler2", "pull", "product", "settled"],
        move |_, _, _, key, value, _| {
            if let (ProductKey::RootBackendProduct(_), ProductValue::RootBackendProduct(program)) = (key, value) {
                *sink.borrow_mut() = Some(Rc::clone(program));
            }
        },
    );
    let callsites = CallsiteCapture::new();
    callsites.install(&telemetry);
    let dbg = DbgCapture::new();
    let mut compiler = Compiler2::new(telemetry);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some(format!("interface10/{name}.fz")),
        text: source,
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .run_root_interp(root)
        .unwrap_or_else(|error| panic!("{name}: normal compiler/interpreter: {error}"));
    assert_eq!(
        dbg.lines(),
        expected.lines().collect::<Vec<_>>(),
        "{name}: every actual callback/environment must execute"
    );
    let program = backend
        .borrow()
        .clone()
        .expect("normal execution published a backend product");
    let analyzed = analyses
        .borrow()
        .iter()
        .filter(|key| key.root == root)
        .cloned()
        .collect();
    let calls = callsites
        .all()
        .into_iter()
        .filter(|record| record.key.activation.root == root)
        .map(|record| (record.key, record.summary))
        .collect();
    let tuple_attempts = tuple_attempts.borrow().clone();
    Witness {
        compiler,
        program,
        analyzed,
        calls,
        tuple_attempts,
    }
}

impl Witness {
    fn label(&self, function: FunctionId) -> String {
        super::canon::function_label(self.compiler.world(), function)
    }

    fn bodies(&self, label: &str) -> Vec<&BackendExecutable> {
        self.program
            .executables()
            .iter()
            .filter(|body| self.label(body.key.activation.function) == label)
            .map(AsRef::as_ref)
            .collect()
    }

    fn counts(&self, label: &str) -> (usize, usize) {
        (
            self.analyzed
                .iter()
                .filter(|key| self.label(key.function) == label)
                .count(),
            self.bodies(label).len(),
        )
    }

    fn assert_shared(&self, labels: &[&str]) {
        let counts = labels
            .iter()
            .map(|label| ((*label).to_owned(), self.counts(label)))
            .collect::<BTreeMap<_, _>>();
        assert!(
            counts.values().all(|counts| *counts == (1, 1)),
            "one ever-analyzed owner and emitted body per compatible interface, not late deduplication: {counts:?}"
        );
    }

    fn assert_int_callbacks(&self, lexical_owner: &str, expected_functions: usize, arity: usize) {
        let callbacks = self.program.executables().iter().filter(|body| {
            matches!(&self.compiler.world().function_ref(body.key.activation.function).origin,
                fz_runtime::function_denotation::FunctionOrigin::Generated { owner, .. } if owner.is_named(lexical_owner))
        }).collect::<Vec<_>>();
        assert_eq!(
            callbacks
                .iter()
                .map(|body| body.key.activation.function)
                .collect::<HashSet<_>>()
                .len(),
            expected_functions,
            "both real callback implementations must survive"
        );
        for callback in callbacks {
            let captures = self.compiler.world().activation_capture_count(&callback.key.activation);
            for index in captures..captures + arity {
                let input = callback
                    .abi
                    .semantic_inputs
                    .iter()
                    .find(|input| input.semantic_index == index)
                    .expect("used integer callback argument has an ABI binding");
                assert_eq!(
                    input.layout.reprs.as_ref(),
                    &[AbiValueRepr::RawInt],
                    "callback argument ABI"
                );
            }
            assert_eq!(
                callback.abi.return_layout.layout.reprs.as_ref(),
                &[AbiValueRepr::RawInt],
                "callback result ABI"
            );
        }
    }
}

#[test]
fn compatible_apply_shares_in_both_admission_orders() {
    let mut counts = Vec::new();
    for name in ["apply_compatible", "apply_reversed"] {
        let run = witness(name);
        run.assert_int_callbacks("main", 2, 1);
        counts.push((name, run.counts("apply_one/2")));
    }
    assert!(
        counts.iter().all(|(_, counts)| *counts == (1, 1)),
        "admission order cannot change sharing; (witness, ever-analyzed owners, emitted bodies): {counts:?}"
    );
}

#[test]
fn repeated_compatible_admissions_preserve_selection_and_share() {
    let run = witness("apply_repeated");
    run.assert_int_callbacks("main", 2, 1);
    run.assert_shared(&["apply_one/2"]);
}

#[test]
fn incompatible_callback_result_separates_only_its_interface() {
    let mut run = witness("apply_incompatible");
    let int = run.compiler.world_mut().types_mut().int();
    let atom = run.compiler.world_mut().types_mut().atom_lit("ok");
    let bodies = run.bodies("apply_one/2");
    assert_eq!(
        bodies
            .iter()
            .map(|body| body.abi.materialized.return_ty)
            .collect::<HashSet<_>>(),
        HashSet::from([int, atom]),
        "compatible int results and incompatible atom results remain exact"
    );
    assert_eq!(
        run.counts("apply_one/2"),
        (2, 2),
        "two int callbacks share; int -> atom has its own owner and body"
    );
}

#[test]
fn compose_keeps_ordered_callback_result_dependencies_while_sharing() {
    witness("compose").assert_shared(&["compose/3"]);
}

#[test]
fn twice_uses_the_first_result_as_its_second_invocation_domain() {
    let mut run = witness("twice_transition");
    let twice = run.bodies("twice/2")[0].key.activation.function;
    let int = run.compiler.world_mut().types_mut().int();
    let middle = run.compiler.world_mut().types_mut().atom_lit("middle");
    let binary = run.compiler.world_mut().types_mut().str_t();
    let calls = run
        .calls
        .iter()
        .filter(|(key, _)| key.activation.function == twice)
        .collect::<Vec<_>>();
    assert_eq!(
        calls.len(),
        2,
        "the same callable has two separate source invocation ports"
    );
    let interfaces = calls
        .iter()
        .map(|(_, summary)| {
            assert_eq!(summary.targets.len(), 1);
            (summary.targets[0].surface_inputs.clone(), summary.return_ty)
        })
        .collect::<HashSet<_>>();
    assert_eq!(
        interfaces,
        HashSet::from([(vec![int], Some(middle)), (vec![middle], Some(binary))]),
        "int -> :middle -> binary must not become two calls on int or a blended return"
    );
    assert_eq!(
        run.compiler
            .world()
            .activation_return(&run.bodies("twice/2")[0].key.activation),
        Some(binary)
    );
}

#[test]
fn equal_callback_results_share_the_following_tuple_relationship() {
    witness("wrap_after").assert_shared(&["wrap_after/2"]);
}

#[test]
fn a_second_equal_callback_result_adds_no_equivalent_tuple_transfer_work() {
    let count = |name| {
        let run = witness(name);
        let mut sites: Vec<(StepSite, usize)> = Vec::new();
        for (function, site) in &run.tuple_attempts {
            if run.label(*function) != "wrap_after/2" {
                continue;
            }
            if let Some((_, count)) = sites.iter_mut().find(|(candidate, _)| candidate == site) {
                *count += 1;
            } else {
                sites.push((*site, 1));
            }
        }
        assert_eq!(sites.len(), 1, "the witness must reach its one source Tuple transfer");
        sites[0]
    };
    let one = count("wrap_after_single");
    let two = count("wrap_after");
    assert_eq!(one.0, two.0, "both runs measure the same unchanged source operation");
    // Count attempts, including provisional rounds, rather than assuming a
    // fixed number of solver passes. The extra callback must not duplicate
    // higher-order transfer work once its result supplies the same int input.
    assert_eq!(
        two.1, one.1,
        "a second int result must reuse the tuple transfer; (site, one callback attempts)={one:?}, (site, two callback attempts)={two:?}"
    );
}

#[test]
fn forwarding_apply2_preserves_each_callback_and_shares() {
    witness("fwd_apply2").assert_shared(&["fwd/2", "apply2/2"]);
}

#[test]
fn called_twice_preserves_each_callback_and_shares() {
    witness("called_twice").assert_shared(&["called/2", "twice/2"]);
}

fn assert_fold_chain(run: &Witness) {
    let mut labels = vec![
        "Enum.reduce/3".to_owned(),
        "Enumerable.List.reduce/3".into(),
        "List.reduce/3".into(),
        "List.reduce_cont/3".into(),
        "List.reduce_step/3".into(),
        "Enum.reduce_finish/1".into(),
    ];
    let adapters = run
        .program
        .executables()
        .iter()
        .map(|body| run.label(body.key.activation.function))
        .filter(|label| label.starts_with("Enum.reduce/3#lambda@"))
        .collect::<HashSet<_>>();
    assert_eq!(
        adapters.len(),
        1,
        "the generated adapter is part of the fold-sharing proof"
    );
    labels.extend(adapters);
    run.assert_shared(&labels.iter().map(String::as_str).collect::<Vec<_>>());
}

#[test]
fn distinct_reducers_share_every_named_fold_helper_and_adapter() {
    let run = witness("reduce_distinct");
    run.assert_int_callbacks("main", 2, 2);
    assert_fold_chain(&run);
}

#[test]
fn repeating_the_same_reducer_preserves_existing_fold_sharing() {
    assert_fold_chain(&witness("reduce_same"));
}

#[test]
fn captured_scale_values_survive_the_shared_fold_chain() {
    let run = witness("reduce_captured_scale");
    run.assert_int_callbacks("scaled", 1, 2);
    assert_fold_chain(&run);
}

fn assert_closed_int_apply(name: &str, callback_owner: &str, callback_functions: usize) {
    let run = witness(name);
    run.assert_shared(&["apply_one/2"]);
    run.assert_int_callbacks(callback_owner, callback_functions, 1);
    let apply = run.bodies("apply_one/2")[0];
    let mut violations = Vec::new();
    if apply.abi.param_reprs.len() < 2 || apply.abi.param_reprs.iter().any(|repr| *repr != AbiValueRepr::RawInt) {
        violations.push(format!(
            "selector/environment and x must be raw integer lanes: {:?}",
            apply.abi.param_reprs
        ));
    }
    if apply.abi.return_layout.layout.reprs.as_ref() != [AbiValueRepr::RawInt] {
        violations.push(format!(
            "the shared invocation result must be RawInt: {:?}",
            apply.abi.return_layout.layout.reprs
        ));
    }
    if !run.program.construction_wrappers().is_empty() {
        violations.push(format!(
            "a closed called-only set needs no public construction wrappers: {}",
            run.program.construction_wrappers().len()
        ));
    }
    assert!(
        violations.is_empty(),
        "{name}: typed closed callable contract:\n{}",
        violations.join("\n")
    );
}

#[test]
fn joined_picker_has_typed_closed_dispatch_on_the_existing_shared_body() {
    assert_closed_int_apply("joined_picker", "choose", 2);
}

#[test]
fn joined_captured_alternatives_keep_their_actual_environment() {
    assert_closed_int_apply("joined_captured", "choose", 2);
}

#[test]
fn joined_callable_captured_by_an_adapter_keeps_selection_and_raw_abi() {
    assert_closed_int_apply("joined_nested", "wrap", 1);
}
