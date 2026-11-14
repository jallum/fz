//! Quiescence is a property of the whole drive stack. A drive nested beneath
//! another can still be moved by the frame beneath it, so only the outermost
//! drain may settle a waiting fact as unknown; a nested drive that runs dry
//! unwinds, leaves its request standing, and is served again. These tests read
//! the `--log-telemetry` stream of real compiles: `work_graph.quiesced` carries
//! the drive-stack depth of the drain that arbitrated, and `pull.drive.deferred`
//! names each drive that unwound instead.

use std::fs::{File, read_dir, remove_file};
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::{Command, id};
use std::sync::atomic::{AtomicU64, Ordering};

const FZ2_BIN: &str = env!("CARGO_BIN_EXE_fz2");
const FIXTURES: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/fixtures");

/// Fixtures whose compile defers at least one nested drive.
const FIXTURES_THAT_DEFER: [&str; 7] = ["00592", "00593", "00708", "00870", "00871", "00877", "00882"];
const DEFEXCEPTION: &str = "00882";

fn fixture_source(number: &str) -> PathBuf {
    let prefix = format!("{number}_");
    read_dir(FIXTURES)
        .expect("list fixtures")
        .map(|entry| entry.expect("fixture entry").path())
        .find(|path| {
            path.extension().is_some_and(|extension| extension == "fz")
                && path
                    .file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| name.starts_with(&prefix))
        })
        .unwrap_or_else(|| panic!("no fixture numbered {number}"))
}

static TRACES: AtomicU64 = AtomicU64::new(0);

/// Every telemetry event of one interpreted compile of the fixture. A fixture
/// may end in the compile error it exists to show; the trace is read either way.
fn compile_events(number: &str) -> Vec<serde_json::Value> {
    let trace = std::env::temp_dir().join(format!(
        "fz2_whole_stack_{}_{}_{number}.jsonl",
        id(),
        TRACES.fetch_add(1, Ordering::Relaxed)
    ));
    Command::new(FZ2_BIN)
        .arg("--log-telemetry")
        .arg(&trace)
        .arg("interp")
        .arg(fixture_source(number))
        .output()
        .expect("invoke fz2 interp with telemetry");
    let events = read_events(&trace);
    let _ = remove_file(&trace);
    events
}

fn read_events(trace: &Path) -> Vec<serde_json::Value> {
    BufReader::new(File::open(trace).expect("open telemetry trace"))
        .lines()
        .map(|line| serde_json::from_str(&line.expect("telemetry line is UTF-8")).expect("telemetry line is JSON"))
        .collect()
}

fn named<'a>(events: &'a [serde_json::Value], suffix: &[&str]) -> Vec<&'a serde_json::Value> {
    let full = ["fz", "compiler2"]
        .into_iter()
        .chain(suffix.iter().copied())
        .collect::<Vec<_>>();
    events
        .iter()
        .filter(|event| event["name"] == serde_json::json!(full))
        .collect()
}

fn depth_of(event: &serde_json::Value) -> u64 {
    event["metadata"]["depth"]
        .as_u64()
        .expect("event carries a stack depth")
}

/// A drain with another drive beneath it never arbitrates: every
/// `work_graph.quiesced` of these compiles comes from the outermost drive, and
/// the compiles do arbitrate there, so the rule is not vacuously met.
#[test]
fn no_fact_is_settled_by_a_drain_beneath_another_drive() {
    for number in FIXTURES_THAT_DEFER {
        let events = compile_events(number);
        let depths = named(&events, &["work_graph", "quiesced"])
            .into_iter()
            .map(depth_of)
            .collect::<Vec<_>>();
        assert!(depths.contains(&1), "fixture {number} never arbitrated");
        assert!(
            depths.iter().all(|depth| *depth <= 1),
            "fixture {number}: a drain settled facts with drives nested beneath one another, at depths {depths:?}"
        );
    }
}

/// Compiling `defexception` unwinds a nested drive exactly this many times. A
/// deferral is a request served again, so the count is the price of the rule on
/// this program: a rise means more nested drives ran dry, a fall means fewer.
#[test]
fn defexception_defers_exactly_these_drives() {
    let events = compile_events(DEFEXCEPTION);
    let deferred = named(&events, &["pull", "drive", "deferred"]);
    assert_eq!(deferred.len(), 3);
}

/// Only a drive with another drive beneath it defers, and each deferral names
/// the drive's scope and product.
#[test]
fn a_deferral_names_its_scope_and_product_and_is_nested() {
    let events = compile_events(DEFEXCEPTION);
    let deferred = named(&events, &["pull", "drive", "deferred"]);
    assert!(!deferred.is_empty(), "the compile deferred nothing");
    for event in deferred {
        assert!(event["metadata"]["product"]["kind"].is_string(), "no product: {event}");
        assert!(event["metadata"]["scope"].is_string(), "no scope: {event}");
        assert!(depth_of(event) > 1, "a drive with nothing beneath it deferred: {event}");
    }
}
