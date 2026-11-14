//! A group of recursive jobs concludes together, for readers outside it.
//!
//! A recursive function's return type is found by a climb: each function of the
//! cycle is analyzed again as the others' answers grow, until nothing moves.
//! A caller outside the cycle must see the answer the climb ends on, once. It
//! must not read a rung of the climb, because each rung it reads keys a callee
//! activation of its own.
//!
//! Each case drives a fixture through the product pull and reads the work the
//! drive did off the telemetry the production path emits: the activations
//! analyzed, the return-type revisions published, and the return types each
//! analysis read.

use std::cell::RefCell;
use std::rc::Rc;

use super::drive::{FactKey, Job};
use super::drive_harness::Drive;
use super::dump::DumpStage;
use super::identity::FunctionId;
use super::world::JobCompletion;
use super::{ActivationKey, World};
use crate::fast_hash::{HashMap, HashSet};
use crate::telemetry::ConfiguredTelemetry;

/// One analysis that read a return type: who read it, whose it was, and the
/// revision the fact stood at when the reader finished.
#[derive(Debug, Clone)]
struct ReturnRead {
    reader: ActivationKey,
    callee: ActivationKey,
    revision: Option<u64>,
    concluding: bool,
}

/// What a drive did, observed off its telemetry.
#[derive(Clone, Default)]
struct Climb {
    analyses: Rc<RefCell<HashMap<ActivationKey, u64>>>,
    revisions: Rc<RefCell<HashMap<ActivationKey, u64>>>,
    analysis_runs: Rc<RefCell<u64>>,
    return_reads: Rc<RefCell<Vec<ReturnRead>>>,
}

impl Climb {
    fn install(&self, telemetry: &ConfiguredTelemetry) {
        let analyses = Rc::clone(&self.analyses);
        telemetry.attach_raw_event2::<World, ActivationKey, _>(
            &["fz", "compiler2", "activation_analysis", "defined"],
            move |_, _, _, _, activation| *analyses.borrow_mut().entry(activation.clone()).or_default() += 1,
        );
        let revisions = Rc::clone(&self.revisions);
        telemetry.attach_raw_event2::<World, ActivationKey, _>(
            &["fz", "compiler2", "return_type", "defined"],
            move |_, _, _, _, activation| *revisions.borrow_mut().entry(activation.clone()).or_default() += 1,
        );
        let runs = Rc::clone(&self.analysis_runs);
        let reads = Rc::clone(&self.return_reads);
        telemetry.attach_raw_event2::<World, JobCompletion, _>(
            &["fz", "compiler2", "work_graph", "applied"],
            move |_, _, _, world, completion| {
                let Job::AnalyzeActivation(reader) = &completion.job else {
                    return;
                };
                *runs.borrow_mut() += 1;
                for read in world.job_reads(&completion.job) {
                    if let FactKey::ReturnType(callee) = read.fact() {
                        reads.borrow_mut().push(ReturnRead {
                            reader: reader.clone(),
                            callee: callee.clone(),
                            revision: world.fact_revision(read.fact()),
                            concluding: completion.blocked.is_empty(),
                        });
                    }
                }
            },
        );
    }

    fn activations_of(&self, function: FunctionId) -> HashSet<ActivationKey> {
        self.analyses
            .borrow()
            .keys()
            .filter(|key| key.function == function)
            .cloned()
            .collect()
    }

    fn return_revisions_of(&self, function: FunctionId) -> u64 {
        self.revisions
            .borrow()
            .iter()
            .filter(|(key, _)| key.function == function)
            .map(|(_, count)| *count)
            .sum()
    }

    fn reads_of_returns_of(&self, reader: FunctionId, callee: FunctionId) -> Vec<ReturnRead> {
        self.return_reads
            .borrow()
            .iter()
            .filter(|read| read.reader.function == reader && read.callee.function == callee)
            .cloned()
            .collect()
    }
}

fn climb_of(drive: Drive) -> (Climb, super::drive_harness::Settled) {
    let climb = Climb::default();
    climb.install(drive.telemetry());
    let settled = drive.dump_stage(DumpStage::Backend);
    (climb, settled)
}

/// `decode` is the entry of a cycle (`val`, `object`, `object_value`); `same`
/// is the caller's helper that takes `decode`'s result. The climb leaves
/// `decode` one return type, read once, so `same` has one activation.
#[test]
fn a_caller_outside_a_recursive_decoder_reads_its_return_type_once() {
    let (climb, settled) = climb_of(Drive::fixture(1290));
    let decode = settled.functions().id_in_module("J", "decode", 1);
    let same = settled.functions().id_in_module("T", "same", 2);

    assert_eq!(
        climb.activations_of(same).len(),
        1,
        "same/2 is analyzed for the one type decode concludes with, not for each rung of its climb"
    );
    assert_eq!(
        climb.return_revisions_of(decode),
        1,
        "decode's return type is published once, at its final revision"
    );
}

/// Three functions call each other in a ring; `main` is outside it. The
/// ring's group forms when the last function reads the first's answer, climbs
/// by wakes, and closes once, so the one analysis of `main` that concludes
/// reads the first function's return type at the revision the ring ends on.
#[test]
fn a_caller_outside_a_ring_of_three_reads_its_return_type_once_at_the_final_revision() {
    let (climb, settled) = climb_of(Drive::fixture(1292));
    let a = settled.functions().id_in_module("M", "a", 1);
    let main = settled.functions().id_in_module("M", "main", 0);

    let concluding_reads: Vec<_> = climb
        .reads_of_returns_of(main, a)
        .into_iter()
        .filter(|read| read.concluding)
        .collect();
    assert_eq!(
        concluding_reads.len(),
        1,
        "main concludes once with a's return type: {concluding_reads:?}"
    );
    let final_revision = settled
        .world()
        .fact_revision(&FactKey::ReturnType(concluding_reads[0].callee.clone()));
    assert_eq!(
        concluding_reads[0].revision, final_revision,
        "and reads it at its final revision"
    );
}

/// `val`, `object` and `array` climb together through `object_value` and
/// `array_value`. Each activation of those joins the climb, so a reader that
/// took an unfinished step of it would key activations of its own and each of
/// those would climb in turn. The climb runs inside its group and `main`'s
/// three decodes wait for it to close.
const NESTED_DECODERS_ANALYSES: u64 = 151;
/// The distinct activations of `array_value`: one for each shape of accumulator
/// the decoders pass it, however many steps the climb takes.
const NESTED_DECODERS_ARRAY_VALUE_ACTIVATIONS: usize = 2;

#[test]
fn nested_recursive_decoders_climb_inside_their_group_without_a_ladder_of_activations() {
    let (climb, settled) = climb_of(Drive::fixture(1291));
    let array_value = settled.functions().id("array_value", 2);

    assert_eq!(
        *climb.analysis_runs.borrow(),
        NESTED_DECODERS_ANALYSES,
        "the nested cycles are analyzed once per step of their own climb and no more"
    );
    assert_eq!(
        climb.activations_of(array_value).len(),
        NESTED_DECODERS_ARRAY_VALUE_ACTIVATIONS,
        "array_value gets an activation per accumulator shape, not one per unfinished step"
    );
}

/// `roundtrip/1` compares `JSON.decode/1`'s result with its input. The decoder
/// is a cycle, so `same/2` is analyzed for the types the decoder concludes
/// with: eight, as worked out by hand. A reader that took an unfinished step
/// of the climb would key an activation for each step it saw.
#[test]
fn a_json_roundtrip_analyzes_its_comparison_helper_for_the_eight_types_the_decoder_concludes_with() {
    let (climb, settled) = climb_of(Drive::behavior_fixture("json_roundtrip"));
    let same = settled.functions().id("same", 2);

    assert_eq!(climb.activations_of(same).len(), 8);
}
