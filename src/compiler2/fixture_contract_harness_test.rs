use super::fixture_facts::{canonical_call_edge_facts, render_canonical_call_edge_snapshot};
use super::fixture_metadata::{
    EdgeAssertion, FixtureMetadata, MetricAssertion, fixture_frontmatter_prefix_bytes, parse_fixture_metadata,
};
use super::{DriveOutcome, ExecutableNeed, FactKey, Job};
use crate::telemetry::ConfiguredTelemetry;
use crate::telemetry::handler::{Event, Handler};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

#[derive(Debug)]
struct ContractFixture {
    path: PathBuf,
    name: String,
    source: String,
    contract: FixtureMetadata,
}

#[derive(Debug)]
struct EvaluatedFixture {
    facts: Vec<super::fixture_facts::CanonicalCallEdgeFact>,
    snapshot: String,
    metrics: BTreeMap<String, u64>,
}

#[derive(Default)]
struct ReturnWideningCounter {
    count: Arc<Mutex<u64>>,
}

impl ReturnWideningCounter {
    fn handler(&self) -> Box<dyn Handler> {
        let count = Arc::clone(&self.count);
        Box::new(move |event: &Event<'_, '_, '_>| {
            if event.name == ["fz", "compiler2", "return_type", "widened"] {
                let mut count = count.lock().expect("return widening counter lock");
                *count += 1;
            }
        })
    }

    fn get(&self) -> u64 {
        *self.count.lock().expect("return widening counter lock")
    }
}

fn assert_resolved(outcome: DriveOutcome<Job, FactKey>, message: &str) {
    assert!(matches!(outcome, DriveOutcome::Resolved), "{message}: {outcome:?}");
}

fn discover_contract_fixtures() -> Vec<ContractFixture> {
    let filter = std::env::var("FIXTURE2_CONTRACT_FILTER").ok();
    let mut pending = vec![PathBuf::from("fixtures2")];
    let mut paths = Vec::new();
    while let Some(dir) = pending.pop() {
        for entry in fs::read_dir(&dir).unwrap_or_else(|e| panic!("read {}: {}", dir.display(), e)) {
            let path = entry.expect("fixtures2 entry").path();
            if path.is_dir() {
                pending.push(path);
            } else if path.extension().is_some_and(|ext| ext == "fz") {
                paths.push(path);
            }
        }
    }
    let mut fixtures = paths
        .into_iter()
        .filter_map(|path| {
            let source = fs::read_to_string(&path).expect("fixture source");
            let contract = parse_fixture_metadata(&source).expect("fixture frontmatter parse")?;
            if !contract.participates_in_compiler_contracts() {
                return None;
            }
            let name = path.file_stem().expect("fixture stem").to_string_lossy().into_owned();
            if filter.as_ref().is_some_and(|filter| !name.contains(filter)) {
                return None;
            }
            Some(ContractFixture {
                path,
                name,
                source,
                contract,
            })
        })
        .collect::<Vec<_>>();
    fixtures.sort_by(|left, right| left.name.cmp(&right.name));
    fixtures
}

fn evaluate_fixture(fixture: &ContractFixture) -> EvaluatedFixture {
    let root = fixture
        .contract
        .compiler
        .root
        .as_ref()
        .unwrap_or_else(|| panic!("fixture {} is missing `root:`", fixture.name));

    let tel = ConfiguredTelemetry::new();
    let widened = ReturnWideningCounter::default();
    tel.attach(&["fz", "compiler2", "return_type", "widened"], widened.handler());

    let mut world = crate::compiler2::World::new(&tel);
    world.submit_code(Some(fixture.path.display().to_string()), fixture.source.clone());
    let root_id = world.submit_root(None, root.name.clone(), root.arity, ExecutableNeed::Value);
    assert_resolved(
        world.drive(),
        &format!("fixture {} should compile and settle", fixture.name),
    );

    let prefix = fixture_frontmatter_prefix_bytes(&fixture.source)
        .expect("fixture frontmatter prefix")
        .unwrap_or(0);
    let facts = normalize_fact_spans(canonical_call_edge_facts(&world, root_id), prefix);
    let snapshot = render_canonical_call_edge_snapshot(&facts);
    let closure = world.semantic_closure(root_id);
    let root_code = world.function_definition(world.root_function(root_id)).0.code;
    let local_activations = closure
        .activations
        .iter()
        .filter(|activation| world.function_definition(activation.function).0.code == root_code)
        .count() as u64;
    let local_executables = closure
        .executables
        .iter()
        .filter(|executable| world.function_definition(executable.activation.function).0.code == root_code)
        .count() as u64;
    let mut metrics = BTreeMap::new();
    metrics.insert("semantic.activations".to_string(), local_activations);
    metrics.insert("semantic.executables".to_string(), local_executables);
    metrics.insert("semantic.callsites".to_string(), facts.len() as u64);
    metrics.insert("call_edges.count".to_string(), facts.len() as u64);
    metrics.insert("return_type.widened".to_string(), widened.get());

    EvaluatedFixture {
        facts,
        snapshot,
        metrics,
    }
}

fn normalize_fact_spans(
    facts: Vec<super::fixture_facts::CanonicalCallEdgeFact>,
    prefix: u32,
) -> Vec<super::fixture_facts::CanonicalCallEdgeFact> {
    facts
        .into_iter()
        .map(|mut fact| {
            fact.caller = normalize_label_spans(&fact.caller, prefix);
            fact.callsite = normalize_label_spans(&fact.callsite, prefix);
            for target in &mut fact.targets {
                target.target = normalize_label_spans(&target.target, prefix);
            }
            fact
        })
        .collect()
}

fn normalize_label_spans(label: &str, prefix: u32) -> String {
    let mut out = String::with_capacity(label.len());
    let mut index = 0usize;
    while index < label.len() {
        let ch = label[index..].chars().next().expect("char at byte offset");
        if ch != '@' {
            out.push(ch);
            index += ch.len_utf8();
            continue;
        }
        let bytes = label.as_bytes();
        let start_digits = take_digits(bytes, index + 1);
        if start_digits == index + 1 || start_digits >= bytes.len() || bytes[start_digits] != b'-' {
            out.push('@');
            index += 1;
            continue;
        }
        let end_digits = take_digits(bytes, start_digits + 1);
        if end_digits == start_digits + 1 {
            out.push('@');
            index += 1;
            continue;
        }
        let start = label[index + 1..start_digits].parse::<u32>().expect("span start");
        let end = label[start_digits + 1..end_digits].parse::<u32>().expect("span end");
        out.push('@');
        out.push_str(&(start - prefix).to_string());
        out.push('-');
        out.push_str(&(end - prefix).to_string());
        index = end_digits;
    }
    out
}

fn take_digits(bytes: &[u8], mut index: usize) -> usize {
    while index < bytes.len() && bytes[index].is_ascii_digit() {
        index += 1;
    }
    index
}

fn snapshot_sidecar_path(path: &Path, snapshot_name: &str) -> PathBuf {
    sibling_with_suffix(path, snapshot_name)
}

fn actual_artifact_path(path: &Path, artifact: &str) -> PathBuf {
    sibling_with_suffix(path, &format!("actual.{artifact}"))
}

fn sibling_with_suffix(path: &Path, suffix: &str) -> PathBuf {
    let stem = path.file_stem().expect("fixture stem").to_string_lossy();
    path.with_file_name(format!("{stem}.{suffix}"))
}

fn bless_enabled() -> bool {
    std::env::var_os("BLESS").is_some()
}

fn check_fixture_metrics(fixture: &ContractFixture, evaluated: &EvaluatedFixture) -> Option<String> {
    let metrics = &fixture.contract.compiler.metric_assertions;
    if metrics.is_empty() {
        return None;
    }
    let mut failures = Vec::new();
    for MetricAssertion { name, expected } in metrics {
        let actual = evaluated
            .metrics
            .get(name)
            .copied()
            .unwrap_or_else(|| panic!("fixture {} requested unknown metric `{name}`", fixture.name));
        if actual != *expected {
            failures.push(format!("{name}: expected {expected}, actual {actual}"));
        }
    }
    if failures.is_empty() {
        let _ = fs::remove_file(actual_artifact_path(&fixture.path, "contract_metrics"));
        return None;
    }
    let actual = evaluated
        .metrics
        .iter()
        .map(|(name, value)| format!("{name}: {value}"))
        .collect::<Vec<_>>()
        .join("\n");
    fs::write(
        actual_artifact_path(&fixture.path, "contract_metrics"),
        format!("{actual}\n"),
    )
    .expect("write actual contract metrics");
    Some(format!(
        "fixture {} metric assertion failure(s):\n{}",
        fixture.name,
        failures.join("\n")
    ))
}

fn check_fixture_edges(fixture: &ContractFixture, evaluated: &EvaluatedFixture) -> Option<String> {
    let edges = &fixture.contract.compiler.edge_assertions;
    if edges.is_empty() {
        return None;
    }
    let mut failures = Vec::new();
    for EdgeAssertion {
        caller,
        callsite,
        dispatch,
        target,
    } in edges
    {
        let matched = evaluated.facts.iter().any(|fact| {
            fact.caller == *caller
                && fact.callsite == *callsite
                && fact.dispatch == *dispatch
                && fact.targets.iter().any(|candidate| candidate.target == *target)
        });
        if !matched {
            failures.push(format!("{caller} | {callsite} | {dispatch} | {target}"));
        }
    }
    if failures.is_empty() {
        let _ = fs::remove_file(actual_artifact_path(&fixture.path, "contract_edges"));
        return None;
    }
    fs::write(
        actual_artifact_path(&fixture.path, "contract_edges"),
        &evaluated.snapshot,
    )
    .expect("write actual contract edges");
    Some(format!(
        "fixture {} edge assertion failure(s):\n{}\nactual canonical snapshot:\n{}",
        fixture.name,
        failures.join("\n"),
        evaluated.snapshot
    ))
}

fn check_fixture_snapshot(fixture: &ContractFixture, evaluated: &EvaluatedFixture) -> Option<String> {
    let snapshot_name = fixture.contract.compiler.call_edge_snapshot.as_deref()?;
    let snapshot_path = snapshot_sidecar_path(&fixture.path, snapshot_name);
    if bless_enabled() {
        fs::write(&snapshot_path, &evaluated.snapshot).expect("bless canonical snapshot");
        let _ = fs::remove_file(actual_artifact_path(&fixture.path, "call_edges"));
        return None;
    }
    let expected = fs::read_to_string(&snapshot_path).unwrap_or_else(|_| {
        panic!(
            "fixture {} is missing snapshot {}",
            fixture.name,
            snapshot_path.display()
        )
    });
    if expected == evaluated.snapshot {
        let _ = fs::remove_file(actual_artifact_path(&fixture.path, "call_edges"));
        return None;
    }
    fs::write(actual_artifact_path(&fixture.path, "call_edges"), &evaluated.snapshot)
        .expect("write actual canonical snapshot");
    Some(format!(
        "fixture {} snapshot mismatch ({}).\nexpected:\n{}\nactual:\n{}",
        fixture.name,
        snapshot_path.display(),
        expected,
        evaluated.snapshot
    ))
}

fn require_fixtures(fixtures: &[ContractFixture]) {
    assert!(
        !fixtures.is_empty(),
        "no fixtures2 compiler contracts selected; \
         set FIXTURE2_CONTRACT_FILTER only when you intend to narrow the run"
    );
}

#[test]
fn compiler2_contracts() {
    let fixtures = discover_contract_fixtures();
    require_fixtures(&fixtures);
    let mut failures = Vec::new();
    for fixture in &fixtures {
        let evaluated = evaluate_fixture(fixture);
        failures.extend(check_fixture_metrics(fixture, &evaluated));
        failures.extend(check_fixture_edges(fixture, &evaluated));
        failures.extend(check_fixture_snapshot(fixture, &evaluated));
    }
    assert!(
        failures.is_empty(),
        "compiler2 contract failure(s):\n\n{}",
        failures.join("\n\n")
    );
}
