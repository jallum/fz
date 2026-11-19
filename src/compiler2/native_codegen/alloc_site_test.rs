//! The counters compiled code increments, observed through a real run: each
//! test compiles a program, runs it, and reads the sites the run reports.

use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;
use fz_runtime::alloc_site::AllocSiteCount;
use fz_runtime::heap::{AllocStat, HeapAllocKind, HeapAllocStats};
use fz_runtime::process::{PidId, Process};
use fz_runtime::telemetry::{ALLOC_SITE, PROCESS_EXITED};
use std::cell::RefCell;
use std::rc::Rc;

/// What one run reported: the sites that allocated, and what its only
/// process counted for itself.
struct SiteRun {
    sites: Vec<AllocSiteCount>,
    process: HeapAllocStats,
}

fn run(source: &str) -> SiteRun {
    let tel = ConfiguredTelemetry::new();
    let sites = Rc::new(RefCell::new(Vec::new()));
    let site_sink = Rc::clone(&sites);
    tel.attach_raw_event1::<AllocSiteCount, _>(&ALLOC_SITE, move |_, _, _, site| {
        site_sink.borrow_mut().push(site.clone());
    });
    let processes = Rc::new(RefCell::new(Vec::new()));
    let process_sink = Rc::clone(&processes);
    tel.attach_raw_event2::<PidId, Process, _>(&PROCESS_EXITED, move |_, _, _, _, process| {
        process_sink.borrow_mut().push(process.heap.alloc_stats_snapshot());
    });
    let mut compiler = Compiler2::new(tel);
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler.submit_code(CodeSubmission {
        name: Some("alloc_sites.fz".to_string()),
        text: source.to_string(),
    });
    compiler
        .run_root_jit(root)
        .unwrap_or_else(|error| panic!("the program should run end-to-end: {error}"));
    let processes = processes.borrow();
    assert_eq!(processes.len(), 1, "the program runs one process");
    SiteRun {
        sites: sites.take(),
        process: processes[0],
    }
}

/// `step` loops once through itself, and a callee in a call cycle can suspend,
/// so each call of it places a frame.
const COUNTING_LOOP: &str = "
def count(0, acc), do: acc
def count(n, acc), do: count(n - 1, step(acc, 1) + 1)

def step(acc, 0), do: acc
def step(acc, k), do: step(acc, k - 1)

def main(), do: count(1000, 0)
";

/// What the sites of `kind` placed, summed.
fn placed(sites: &[AllocSiteCount], kind: HeapAllocKind) -> AllocStat {
    sites
        .iter()
        .filter(|site| site.kind == kind)
        .fold(AllocStat::default(), |sum, site| AllocStat {
            allocs: sum.allocs + site.placed.allocs,
            bytes: sum.bytes + site.placed.bytes,
        })
}

/// The sites are a breakdown of what the process counts for itself: nothing
/// is counted twice and nothing is missed, whether compiled code placed the
/// object or a runtime function did.
#[test]
fn the_sites_of_a_one_process_program_sum_to_what_its_process_counted() {
    let run = run(COUNTING_LOOP);
    let process = run.process;
    assert!(
        process.continuation.allocs >= 1000,
        "the loop places a frame per iteration"
    );
    let counted_by_process = [
        (HeapAllocKind::ListCons, process.list_cons),
        (HeapAllocKind::Struct, process.struct_),
        (HeapAllocKind::Continuation, process.continuation),
        (HeapAllocKind::Map, process.map),
        (HeapAllocKind::Bitstring, process.bitstring),
        (HeapAllocKind::BinView, process.binview),
        (HeapAllocKind::BinRef, process.binref),
        (HeapAllocKind::ScalarBox, process.scalar_box),
        (HeapAllocKind::Resource, process.resource),
        (HeapAllocKind::Other, process.other),
    ];
    for (kind, counted) in counted_by_process {
        assert_eq!(placed(&run.sites, kind), counted, "{kind:?}");
    }
}

/// A process starts counting once the scheduler has built the two closures
/// that enter it; the program's sites count those as well, because the
/// program placed them.
#[test]
fn the_sites_also_count_the_closures_that_enter_the_process() {
    let run = run(COUNTING_LOOP);
    assert_eq!(
        placed(&run.sites, HeapAllocKind::Closure).allocs,
        run.process.closure.allocs + 2
    );
}

/// A site names the function whose code allocates, so a count can be read
/// against the source.
#[test]
fn the_loops_frames_are_counted_at_a_site_in_the_loop() {
    let run = run(COUNTING_LOOP);
    let busiest = run
        .sites
        .iter()
        .max_by_key(|site| site.placed.allocs)
        .expect("the run reports a site");
    assert!(
        busiest.function.contains("count"),
        "busiest site is in {}",
        busiest.function
    );
    assert!(
        busiest.placed.allocs >= 1000,
        "one frame per iteration, counted {busiest:?}"
    );
    assert_eq!(
        busiest.placed.bytes % busiest.placed.allocs,
        0,
        "a compiled site's frames are one size"
    );
}
