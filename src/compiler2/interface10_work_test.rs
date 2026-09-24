//! Work-sharing acceptance measures evaluator invocations, not job starts or
//! the number of owners left after compilation. Allocation snapshots use the
//! runtime's existing process-exit event, without adding measurement calls to FZ.

use super::drive_test::{FunctionCapture, function_id, generated_function_ids};
use super::{
    ActivationInput, ActivationInputAlternatives, ActivationInputRow, ActivationKey, CallSiteId, CodeSubmission,
    Compiler2, ControlEntryId, ExecutableNeed, FunctionId, FunctionSkeleton, LoweredStep, LoweredTail, RootSubmission,
    StepSite,
};
use crate::exec::runtime::DbgCapture;
use crate::ir_codegen::{PidId, Process};
use crate::telemetry::ConfiguredTelemetry;
use fz_runtime::heap::HeapAllocStats;
use std::cell::RefCell;
use std::collections::{BTreeMap, HashSet};
use std::rc::Rc;

const PREFIX: &[&str] = &["fz", "compiler2", "inference_work"];

#[derive(Clone, Default)]
struct WorkCapture(Rc<RefCell<Vec<(FunctionId, &'static str)>>>);

impl WorkCapture {
    fn install(&self, tel: &ConfiguredTelemetry) {
        let records = self.0.clone();
        tel.attach_raw_event2::<FunctionId, FunctionSkeleton, _>(PREFIX, move |name, _, _, function, _| {
            records.borrow_mut().push((*function, name[name.len() - 1]));
        });
        let records = self.0.clone();
        tel.attach_raw_event2::<ActivationKey, ActivationInputAlternatives, _>(PREFIX, move |name, _, _, key, _| {
            records.borrow_mut().push((key.function, name[name.len() - 1]));
        });
        let records = self.0.clone();
        tel.attach_raw_event2::<ActivationKey, ActivationInputRow, _>(PREFIX, move |name, _, _, key, _| {
            records.borrow_mut().push((key.function, name[name.len() - 1]));
        });
        let records = self.0.clone();
        tel.attach_raw_event3::<ActivationKey, u32, Vec<ActivationInput>, _>(PREFIX, move |name, _, _, key, _, _| {
            records.borrow_mut().push((key.function, name[name.len() - 1]));
        });
        let records = self.0.clone();
        tel.attach_raw_event3::<ActivationKey, StepSite, LoweredStep, _>(PREFIX, move |name, _, _, key, _, _| {
            records.borrow_mut().push((key.function, name[name.len() - 1]));
        });
        let records = self.0.clone();
        tel.attach_raw_event3::<ActivationKey, ControlEntryId, LoweredTail, _>(PREFIX, move |name, _, _, key, _, _| {
            records.borrow_mut().push((key.function, name[name.len() - 1]));
        });
        let records = self.0.clone();
        tel.attach_raw_event3::<ActivationKey, CallSiteId, ActivationKey, _>(PREFIX, move |name, _, _, key, _, _| {
            records.borrow_mut().push((key.function, name[name.len() - 1]));
        });
        let records = self.0.clone();
        tel.attach_raw_event2::<ActivationKey, Vec<ActivationKey>, _>(PREFIX, move |name, _, _, key, _| {
            records.borrow_mut().push((key.function, name[name.len() - 1]));
        });
        let records = self.0.clone();
        tel.attach_raw_event2::<ActivationKey, usize, _>(PREFIX, move |name, _, _, key, _| {
            records.borrow_mut().push((key.function, name[name.len() - 1]));
        });
    }

    fn for_function(&self, function: FunctionId) -> BTreeMap<&'static str, usize> {
        let mut counts = BTreeMap::new();
        for (owner, name) in self.0.borrow().iter() {
            if *owner == function {
                *counts.entry(*name).or_default() += 1;
            }
        }
        counts
    }
}

fn compile(
    source: &str,
) -> (
    Compiler2<ConfiguredTelemetry>,
    super::RootId,
    FunctionCapture,
    WorkCapture,
) {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let work = WorkCapture::default();
    work.install(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("interface10_work.fz".into()),
        text: source.into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .product_executable_inventory(root)
        .expect("ordinary backend product must settle");
    (compiler, root, functions, work)
}

#[test]
fn a_cached_product_request_repeats_no_inference_work() {
    let (mut compiler, root, functions, work) =
        compile("def apply_one(f, x), do: f.(x)\ndef main(), do: apply_one(fn x -> x + 1 end, 2)\n");
    let apply = function_id(&functions, "apply_one", 2);
    let counts = work.for_function(apply);
    assert_eq!(
        counts.get("skeleton_lowered"),
        Some(&1),
        "one installed source skeleton"
    );
    assert!(
        counts.get("activation_walk").copied().unwrap_or(0) > 0,
        "measure actual evaluator entry"
    );
    assert!(
        counts.get("tail_transfer_attempt").copied().unwrap_or(0) > 0,
        "measure actual body work"
    );
    work.0.borrow_mut().clear();
    compiler
        .product_executable_inventory(root)
        .expect("repeat the same public product demand");
    assert!(
        work.0.borrow().is_empty(),
        "a cached product must not secretly repeat inference"
    );
}

#[test]
fn a_second_compatible_callback_adds_callback_work_without_rewalking_apply() {
    let source = |second: bool| {
        format!(
            "def apply_one(f, x), do: f.(x)\ndef main(), do: {{apply_one(fn x -> x + 1 end, 2), {}}}\n",
            if second { "apply_one(fn x -> x * 2 end, 2)" } else { "0" },
        )
    };
    let mut observed = Vec::new();
    for second in [false, true] {
        let (_, _, functions, work) = compile(&source(second));
        let apply = function_id(&functions, "apply_one", 2);
        let main = function_id(&functions, "main", 0);
        let callback_functions = generated_function_ids(&functions, main)
            .into_iter()
            .collect::<HashSet<_>>();
        let analyzed_callbacks = work
            .0
            .borrow()
            .iter()
            .filter(|(function, name)| *name == "activation_walk" && callback_functions.contains(function))
            .map(|(function, _)| *function)
            .collect::<HashSet<_>>();
        assert_eq!(
            analyzed_callbacks.len(),
            if second { 2 } else { 1 },
            "each implementation needs analysis"
        );
        let mut counts = work.for_function(apply);
        eprintln!("apply second_callback={second}: {counts:?}");
        assert_eq!(counts.remove("skeleton_lowered"), Some(1));
        // New bindings legitimately route targets. The claim below concerns
        // reinterpreting the unchanged higher-order body, not target wiring.
        counts.remove("invocation_target_attempt");
        observed.push(counts);
    }
    assert_eq!(
        observed[1], observed[0],
        "a compatible binding must not repeat apply's body/row/transfer work"
    );
}

#[test]
fn runtime_allocation_measurement_preserves_distinct_callback_results() {
    let cases = [
        (
            "apply",
            include_str!("../../fixtures2/behavior/interface10_apply_compatible.fz"),
            vec!["3", "4"],
        ),
        (
            "reduce",
            include_str!("../../fixtures2/behavior/interface10_reduce_distinct.fz"),
            vec!["7", "6"],
        ),
        (
            "captured",
            include_str!("../../fixtures2/behavior/interface10_reduce_captured_scale.fz"),
            vec!["6", "60"],
        ),
        (
            "joined",
            include_str!("../../fixtures2/behavior/interface10_joined_picker.fz"),
            vec!["3", "4"],
        ),
    ];
    for (name, source, expected) in cases {
        for jit in [false, true] {
            let tel = ConfiguredTelemetry::new();
            let snapshots = Rc::new(RefCell::new(Vec::<HeapAllocStats>::new()));
            let sink = snapshots.clone();
            tel.attach_raw_event2::<PidId, Process, _>(
                &["fz", "runtime", "process_exited"],
                move |_, _, _, _, process| sink.borrow_mut().push(process.heap.alloc_stats_snapshot()),
            );
            let dbg = DbgCapture::new();
            let mut compiler = Compiler2::new(tel);
            compiler.set_output(dbg.sink());
            compiler.submit_code(CodeSubmission {
                name: Some(format!("{name}.fz")),
                text: source.into(),
            });
            let root = compiler.submit_root(RootSubmission {
                module_name: None,
                name: "main".into(),
                arity: 0,
                need: ExecutableNeed::Value,
            });
            if jit {
                compiler.run_root_jit(root)
            } else {
                compiler.run_root_interp(root).map(|_| ())
            }
            .unwrap_or_else(|error| panic!("{name} jit={jit}: {error}"));
            assert_eq!(dbg.lines(), expected, "{name} jit={jit}");
            let stats = snapshots
                .borrow()
                .last()
                .copied()
                .expect("runtime exit allocation snapshot");
            eprintln!(
                "{name} jit={jit}: closure={:?}, scalar_box={:?}, frame={:?}",
                stats.closure, stats.scalar_box, stats.frame,
            );
            assert!(
                stats.scalar_box.allocs >= 2,
                "the two dbg results exercise the scalar allocation counter"
            );
            if name != "joined" {
                assert_eq!(
                    stats.closure.allocs, 0,
                    "typed direct callback controls must not allocate closures"
                );
            }
        }
    }
}
