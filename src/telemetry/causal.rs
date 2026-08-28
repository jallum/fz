//! Causal replay of the public compiler2 trace (fz-kdt.34.6).
//!
//! Reads a public JSONL log — nothing else — and answers the question
//! fz-kdt.34 exists to answer: *did every evaluation of every formula have new
//! input evidence?*
//!
//! # Causality is derived, not stored
//!
//! The scheduler records WHICH facts a job read (`DependencyIndex.reads`) but
//! never at what revision, and the product engine is the opposite. So "did this
//! formula's input move since its own prior conclusion?" cannot be answered by
//! asking either engine without a second dependency ledger. It IS answerable by
//! replaying the ordered stream. For evaluation `e` of formula `F` at stream
//! position `t`, the moved inputs are exactly
//!
//! ```text
//! (F's reads UNION F's blocked-set from its previous completion)
//!   for which a movement appears in [F's previous conclusion, t)
//! ```
//!
//! Two boundaries in that rule are load-bearing and both were measured:
//!
//! - `reads` ALONE is not enough. `reads` and `waits` are separate maps, and a
//!   job re-run because a WAIT became satisfiable has the fact only in `waits`.
//!   `Dependencies::Reads` keeps that variant alive so the acceptance test can
//!   show it false-flagging real work as uncaused (37/30/19 evaluations on the
//!   three target fixtures) where `Dependencies::ReadsAndBlocked` reports zero.
//! - the window INCLUDES the previous conclusion's own movements. A formula
//!   that writes a fact it also reads wakes itself, and the movement that
//!   causes the next evaluation is carried by the previous completion.
//!
//! # Raw ids join; canonical identity compares
//!
//! Replay joins on RAW ids: within one process they are exact, free, and the
//! only thing that distinguishes two arena neighbours. They are useless across
//! processes (fz-kdt.47 measured 16 differing arena slots over four runs), so
//! every reported identity is translated through the stream's own
//! `fz.compiler2.canon.*` definition lines at REPORT time. `canonical_multiset`
//! is the comparand two runs are compared by.
//!
//! Sorting happens only in that packaging step: the report's `BTreeMap`s are
//! the presentation boundary, and replay itself never orders anything.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use serde_json::Value as Json;

use super::handler::EventKind;

/// One line of the public JSONL stream, parsed back into a structured event.
#[derive(Debug, Clone)]
pub struct PublicEvent {
    pub name: Vec<String>,
    pub kind: EventKind,
    pub span_id: u64,
    pub parent_span_id: u64,
    pub measurements: Json,
    pub metadata: Json,
    /// The `"semantic"` sibling of `metadata` — the projection the sink
    /// computes from `&World` (a completion's `reads`, a callsite's summary).
    pub semantic: Json,
}

impl PublicEvent {
    /// Looks up one key in this event's `metadata` object. `None` if the
    /// event has no metadata object, or the key is absent.
    pub fn metadata_key(&self, key: &str) -> Option<&Json> {
        self.metadata.get(key)
    }

    fn named(&self, name: &[&str]) -> bool {
        self.name.iter().map(String::as_str).eq(name.iter().copied())
    }
}

/// Parses the newline-delimited public JSONL stream `JsonlBackend` writes into
/// structured events, in emission order.
pub fn parse_public_trace(bytes: &[u8]) -> Vec<PublicEvent> {
    let text = std::str::from_utf8(bytes).expect("public JSONL stream must be valid UTF-8");
    text.lines().map(parse_public_event).collect()
}

fn parse_public_event(line: &str) -> PublicEvent {
    let value: Json =
        serde_json::from_str(line).unwrap_or_else(|error| panic!("malformed public JSONL line: {error}\n{line}"));
    let name = value["name"]
        .as_array()
        .unwrap_or_else(|| panic!("public JSONL line missing \"name\" array: {line}"))
        .iter()
        .map(|part| {
            part.as_str()
                .unwrap_or_else(|| panic!("non-string name part: {line}"))
                .to_string()
        })
        .collect();
    let kind = match value["kind"].as_str() {
        Some("event") => EventKind::Event,
        Some("span_start") => EventKind::SpanStart,
        Some("span_stop") => EventKind::SpanStop,
        Some("span_exception") => EventKind::SpanException,
        other => panic!("public JSONL line has unknown \"kind\" {other:?}: {line}"),
    };
    let span_id = value["span_id"]
        .as_u64()
        .unwrap_or_else(|| panic!("non-u64 span_id: {line}"));
    let parent_span_id = value["parent_span_id"]
        .as_u64()
        .unwrap_or_else(|| panic!("non-u64 parent_span_id: {line}"));
    PublicEvent {
        name,
        kind,
        span_id,
        parent_span_id,
        measurements: value["measurements"].clone(),
        metadata: value["metadata"].clone(),
        semantic: value["semantic"].clone(),
    }
}

/// The stream's own raw-id dictionary, read from its `fz.compiler2.canon.*`
/// definition lines. A log carries one; two logs are comparable through them.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct CanonTables {
    types: HashMap<u64, String>,
    functions: HashMap<u64, String>,
}

impl CanonTables {
    /// Collects every definition line in the stream.
    pub fn from_stream(events: &[PublicEvent]) -> Self {
        let mut tables = Self::default();
        for event in events {
            tables.define(event);
        }
        tables
    }

    fn define(&mut self, event: &PublicEvent) {
        let Some(canon) = event.metadata.get("canon").and_then(Json::as_str) else {
            return;
        };
        if event.named(CANON_TYPE)
            && let Some(id) = event.metadata.get("type_id").and_then(Json::as_u64)
        {
            self.types.insert(id, canon.to_string());
        }
        if event.named(CANON_FUNCTION)
            && let Some(id) = event.metadata.get("function_id").and_then(Json::as_u64)
        {
            self.functions.insert(id, canon.to_string());
        }
    }

    pub fn types(&self) -> usize {
        self.types.len()
    }

    pub fn functions(&self) -> usize {
        self.functions.len()
    }

    /// A raw `Ty`'s canonical form. An id the stream never defined renders as
    /// `?ty:N` rather than panicking, so a report over a truncated log is
    /// still readable — `CausalReport::undefined_first_uses` is what asserts
    /// the stream is complete.
    fn ty(&self, id: u64) -> String {
        self.types.get(&id).cloned().unwrap_or_else(|| format!("?ty:{id}"))
    }

    fn function(&self, id: u64) -> String {
        self.functions.get(&id).cloned().unwrap_or_else(|| format!("?fn:{id}"))
    }
}

const CANON_TYPE: &[&str] = &["fz", "compiler2", "canon", "type"];
const CANON_FUNCTION: &[&str] = &["fz", "compiler2", "canon", "function"];
const APPLIED: &[&str] = &["fz", "compiler2", "work_graph", "applied"];
const PRODUCT_SETTLED: &[&str] = &["fz", "compiler2", "pull", "product", "settled"];
const PRODUCT_CACHE_HIT: &[&str] = &["fz", "compiler2", "pull", "product", "cache_hit"];
const PRODUCT_DISPLACED: &[&str] = &["fz", "compiler2", "pull", "product", "displaced"];
const SESSION_FINISHED: &[&str] = &["fz", "compiler2", "pull", "session", "finished"];

/// Fields that describe a fact's STATE rather than its identity. Stripping
/// them is what lets a `reads` entry, a `blocked` wait, a `changed` record and
/// a `movements` post-state all name the same fact with one key.
const STATE_FIELDS: &[&str] = &[
    "use",
    "revision",
    "settled",
    "old_revision",
    "new_revision",
    "old_settled",
    "new_settled",
    "opaque_type",
    "rebased",
    "changed",
    "wakes",
    "movements",
    "blocked",
];

/// Which dependency set an evaluation may name as its cause.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Dependencies {
    /// The scheduler's `reads` alone — the derivation the stream *looks* like
    /// it supports. Kept so the acceptance test can measure it false-flagging
    /// wait-satisfied work as uncaused.
    Reads,
    /// `reads` UNION the blocked-set of the formula's previous completion.
    ReadsAndBlocked,
}

/// How one evaluation of a formula was caused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Cause {
    /// The formula's first evaluation: there is no previous conclusion to have
    /// moved away from.
    Initial,
    /// At least one dependency's REVISION moved in the window.
    Content,
    /// No revision moved; a dependency's SETTLEDNESS flipped — a wait became
    /// satisfiable.
    Readiness,
    /// Nothing in the dependency set moved. Must never happen.
    Uncaused,
}

/// Work attributed to one formula (one canonical job identity).
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct FormulaWork {
    pub evaluations: u64,
    pub initial: u64,
    pub content_caused: u64,
    pub readiness_caused: u64,
    pub uncaused: u64,
    pub changed_outputs: u64,
    pub unchanged_outputs: u64,
    pub wakes: u64,
    pub blocked_completions: u64,
}

/// Work attributed to one product (one canonical `ProductKey`).
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ProductWork {
    pub settlements: u64,
    pub changed: u64,
    pub unchanged: u64,
    pub cache_hits: u64,
    pub displacements: u64,
    pub generations: BTreeSet<u64>,
}

/// The pull sessions' own work-start accounting, summed over every session in
/// the stream.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct SessionWork {
    pub sessions: u64,
    pub producer_pokes: u64,
    pub ignition: u64,
    pub changed_revision_wake: u64,
    pub standing_root_frontier: u64,
    pub activation_frontier: u64,
    pub blocked_waiter_expansion: u64,
    pub unsanctioned_work_starts: u64,
    pub root_scans: u64,
}

/// An evaluation the replay could not attribute to a moved input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UncausedEvaluation {
    pub position: usize,
    pub formula: String,
    pub dependencies: Vec<String>,
}

/// A raw id an event named before the stream defined it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UndefinedFirstUse {
    pub position: usize,
    pub event: String,
    pub reference: String,
}

/// Everything the public stream says about the work a compile did.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CausalReport {
    pub formulas: BTreeMap<String, FormulaWork>,
    pub products: BTreeMap<String, ProductWork>,
    pub sessions: SessionWork,
    pub canon: CanonTables,
    /// Evaluations with no moved input. The acceptance contract is that this
    /// is empty under `Dependencies::ReadsAndBlocked`.
    pub uncaused: Vec<UncausedEvaluation>,
    /// Readiness-caused evaluations for which no `Settled`/`SettledPresence`
    /// wake named the formula in the window — a readiness cause claimed
    /// without the wake that carries it.
    pub readiness_without_settled_wake: Vec<UncausedEvaluation>,
    /// References to raw ids the stream had not yet defined. The
    /// self-describing contract is that this is empty.
    pub undefined_first_uses: Vec<UndefinedFirstUse>,
}

impl CausalReport {
    /// The derivation fz-kdt.34 specifies.
    pub fn derive(events: &[PublicEvent]) -> Self {
        Self::derive_with(events, Dependencies::ReadsAndBlocked)
    }

    pub fn derive_with(events: &[PublicEvent], dependencies: Dependencies) -> Self {
        Replay::new(events).run(events, dependencies)
    }

    /// The comparand. Every counted dimension flattened onto canonical
    /// identity strings, so two runs — two PROCESSES — compare by what work
    /// they did rather than by where their arenas happened to put it.
    pub fn canonical_multiset(&self) -> BTreeMap<String, u64> {
        let mut multiset = BTreeMap::new();
        for (formula, work) in &self.formulas {
            let mut put = |dimension: &str, count: u64| {
                multiset.insert(format!("formula\u{1}{formula}\u{1}{dimension}"), count);
            };
            put("evaluations", work.evaluations);
            put("initial", work.initial);
            put("content_caused", work.content_caused);
            put("readiness_caused", work.readiness_caused);
            put("uncaused", work.uncaused);
            put("changed_outputs", work.changed_outputs);
            put("unchanged_outputs", work.unchanged_outputs);
            put("wakes", work.wakes);
            put("blocked_completions", work.blocked_completions);
        }
        for (product, work) in &self.products {
            let mut put = |dimension: &str, count: u64| {
                multiset.insert(format!("product\u{1}{product}\u{1}{dimension}"), count);
            };
            put("settlements", work.settlements);
            put("changed", work.changed);
            put("unchanged", work.unchanged);
            put("cache_hits", work.cache_hits);
            put("displacements", work.displacements);
            put("generations", work.generations.len() as u64);
        }
        let session = &self.sessions;
        for (dimension, count) in [
            ("sessions", session.sessions),
            ("producer_pokes", session.producer_pokes),
            ("ignition", session.ignition),
            ("changed_revision_wake", session.changed_revision_wake),
            ("standing_root_frontier", session.standing_root_frontier),
            ("activation_frontier", session.activation_frontier),
            ("blocked_waiter_expansion", session.blocked_waiter_expansion),
            ("unsanctioned_work_starts", session.unsanctioned_work_starts),
            ("root_scans", session.root_scans),
        ] {
            multiset.insert(format!("session\u{1}{dimension}"), count);
        }
        multiset
    }

    /// Totals across every formula, for a headline.
    pub fn formula_totals(&self) -> FormulaWork {
        let mut totals = FormulaWork::default();
        for work in self.formulas.values() {
            totals.evaluations += work.evaluations;
            totals.initial += work.initial;
            totals.content_caused += work.content_caused;
            totals.readiness_caused += work.readiness_caused;
            totals.uncaused += work.uncaused;
            totals.changed_outputs += work.changed_outputs;
            totals.unchanged_outputs += work.unchanged_outputs;
            totals.wakes += work.wakes;
            totals.blocked_completions += work.blocked_completions;
        }
        totals
    }

    /// Totals across every product, for a headline.
    pub fn product_totals(&self) -> ProductWork {
        let mut totals = ProductWork::default();
        for work in self.products.values() {
            totals.settlements += work.settlements;
            totals.changed += work.changed;
            totals.unchanged += work.unchanged;
            totals.cache_hits += work.cache_hits;
            totals.displacements += work.displacements;
        }
        totals
    }
}

/// One fact movement, at the stream position that carried it.
struct Movement {
    position: usize,
    content: bool,
    readiness: bool,
}

/// What the replay remembers about a formula between its evaluations. Keyed by
/// RAW identity: two arena-distinct activations are two formulas here even when
/// they share a canonical form, because each has its own conclusion history.
#[derive(Default)]
struct FormulaHistory {
    last_conclusion: Option<usize>,
    blocked: HashSet<String>,
}

struct Replay {
    canon: CanonTables,
    movements: HashMap<String, Vec<Movement>>,
    settled_wakes: HashMap<String, Vec<usize>>,
    history: HashMap<String, FormulaHistory>,
    defined_types: HashSet<u64>,
    defined_functions: HashSet<u64>,
    report: CausalReport,
}

impl Replay {
    fn new(events: &[PublicEvent]) -> Self {
        Self {
            canon: CanonTables::from_stream(events),
            movements: HashMap::new(),
            settled_wakes: HashMap::new(),
            history: HashMap::new(),
            defined_types: HashSet::new(),
            defined_functions: HashSet::new(),
            report: CausalReport {
                formulas: BTreeMap::new(),
                products: BTreeMap::new(),
                sessions: SessionWork::default(),
                canon: CanonTables::default(),
                uncaused: Vec::new(),
                readiness_without_settled_wake: Vec::new(),
                undefined_first_uses: Vec::new(),
            },
        }
    }

    /// One forward pass. Classification only ever looks backwards, so the
    /// movements and wakes an event carries are recorded AFTER it is
    /// classified — which is also what makes the window's lower bound
    /// inclusive: a formula's own previous conclusion is already indexed.
    fn run(mut self, events: &[PublicEvent], dependencies: Dependencies) -> CausalReport {
        for (position, event) in events.iter().enumerate() {
            self.note_definitions(position, event);
            if event.named(APPLIED) {
                self.apply(position, event, dependencies);
            } else if event.named(PRODUCT_SETTLED) {
                self.settle_product(event);
            } else if event.named(PRODUCT_CACHE_HIT) {
                self.product(event).cache_hits += 1;
            } else if event.named(PRODUCT_DISPLACED) {
                self.product(event).displacements += 1;
            } else if event.named(SESSION_FINISHED) {
                self.finish_session(event);
            }
        }
        self.report.canon = self.canon;
        self.report
    }

    /// Consumes definition lines and reports any raw id used before one.
    fn note_definitions(&mut self, position: usize, event: &PublicEvent) {
        if event.named(CANON_TYPE) {
            if let Some(id) = event.metadata.get("type_id").and_then(Json::as_u64) {
                self.defined_types.insert(id);
            }
            return;
        }
        if event.named(CANON_FUNCTION) {
            if let Some(id) = event.metadata.get("function_id").and_then(Json::as_u64) {
                self.defined_functions.insert(id);
            }
            return;
        }
        let mut references = References::default();
        references.walk(&event.metadata);
        references.walk(&event.semantic);
        let name = event.name.join(".");
        for id in references.types {
            if !self.defined_types.contains(&id) {
                self.report.undefined_first_uses.push(UndefinedFirstUse {
                    position,
                    event: name.clone(),
                    reference: format!("type:{id}"),
                });
            }
        }
        for id in references.functions {
            if !self.defined_functions.contains(&id) {
                self.report.undefined_first_uses.push(UndefinedFirstUse {
                    position,
                    event: name.clone(),
                    reference: format!("function:{id}"),
                });
            }
        }
    }

    fn apply(&mut self, position: usize, event: &PublicEvent, dependencies: Dependencies) {
        let Some(completion) = event.metadata.get("completion") else {
            return;
        };
        let raw_formula = identity(completion, None);
        let canonical_formula = identity(completion, Some(&self.canon));
        let reads = fact_set(event.semantic.get("reads"));
        let blocked = fact_set(completion.get("blocked"));
        let previous = self
            .history
            .get(&raw_formula)
            .and_then(|history| history.last_conclusion);
        let deps = self.dependency_set(&raw_formula, &reads, dependencies);
        let cause = match previous {
            None => Cause::Initial,
            Some(previous) => self.cause(previous, position, &deps),
        };

        let work = self.report.formulas.entry(canonical_formula.clone()).or_default();
        work.evaluations += 1;
        if array(completion.get("changed")).is_empty() {
            work.unchanged_outputs += 1;
        } else {
            work.changed_outputs += 1;
        }
        work.wakes += array(completion.get("wakes")).len() as u64;
        if !blocked.is_empty() {
            work.blocked_completions += 1;
        }
        match cause {
            Cause::Initial => work.initial += 1,
            Cause::Content => work.content_caused += 1,
            Cause::Readiness => work.readiness_caused += 1,
            Cause::Uncaused => work.uncaused += 1,
        }

        if matches!(cause, Cause::Uncaused) {
            let mut names = deps
                .iter()
                .map(|fact| canonicalize(fact, &self.canon))
                .collect::<Vec<_>>();
            names.sort();
            self.report.uncaused.push(UncausedEvaluation {
                position,
                formula: canonical_formula.clone(),
                dependencies: names,
            });
        }
        if matches!(cause, Cause::Readiness) && !self.woken_by_settled(&raw_formula, position) {
            self.report.readiness_without_settled_wake.push(UncausedEvaluation {
                position,
                formula: canonical_formula,
                dependencies: Vec::new(),
            });
        }

        self.record_movements(position, completion);
        self.record_wakes(position, completion);
        let history = self.history.entry(raw_formula).or_default();
        history.last_conclusion = Some(position);
        history.blocked = blocked;
    }

    /// The facts an evaluation may name as its cause. `reads` is the current
    /// completion's read set; the blocked-set is the one the formula's PREVIOUS
    /// completion recorded, because that is the wait whose satisfaction re-ran
    /// it.
    fn dependency_set(
        &self,
        raw_formula: &str,
        reads: &HashSet<String>,
        dependencies: Dependencies,
    ) -> HashSet<String> {
        match dependencies {
            Dependencies::Reads => reads.clone(),
            Dependencies::ReadsAndBlocked => {
                let blocked = self.history.get(raw_formula).map(|history| &history.blocked);
                reads.iter().chain(blocked.into_iter().flatten()).cloned().collect()
            }
        }
    }

    fn cause(&self, previous: usize, position: usize, deps: &HashSet<String>) -> Cause {
        let mut content = false;
        let mut readiness = false;
        for fact in deps {
            for movement in self.movements.get(fact).into_iter().flatten() {
                if movement.position >= previous && movement.position < position {
                    content |= movement.content;
                    readiness |= movement.readiness;
                }
            }
        }
        match (content, readiness) {
            (true, _) => Cause::Content,
            (false, true) => Cause::Readiness,
            (false, false) => Cause::Uncaused,
        }
    }

    fn woken_by_settled(&self, raw_formula: &str, position: usize) -> bool {
        let previous = self
            .history
            .get(raw_formula)
            .and_then(|history| history.last_conclusion)
            .unwrap_or(0);
        self.settled_wakes
            .get(raw_formula)
            .into_iter()
            .flatten()
            .any(|at| *at >= previous && *at < position)
    }

    /// Indexes every fact this completion moved. `changed` carries the
    /// before/after pair that splits content from readiness; `movements`
    /// carries the post-state of every fact the step touched, which is the
    /// wider set. A fact in `movements` with no `changed` record moved without
    /// changing either, so it can cause nothing.
    fn record_movements(&mut self, position: usize, completion: &Json) {
        let mut classified = HashMap::new();
        for change in array(completion.get("changed")) {
            let content = change.get("old_revision") != change.get("new_revision");
            let readiness = change.get("old_settled") != change.get("new_settled");
            classified.insert(identity(change, None), (content, readiness));
        }
        let mut seen = HashSet::new();
        for movement in array(completion.get("movements")) {
            let key = identity(movement, None);
            let (content, readiness) = classified.get(&key).copied().unwrap_or((false, false));
            seen.insert(key.clone());
            self.movements.entry(key).or_default().push(Movement {
                position,
                content,
                readiness,
            });
        }
        for (key, (content, readiness)) in classified {
            if seen.contains(&key) {
                continue;
            }
            self.movements.entry(key).or_default().push(Movement {
                position,
                content,
                readiness,
            });
        }
    }

    /// A wake whose cause is `Settled`/`SettledPresence` is the readiness
    /// evidence: agenda state no fact movement reconstructs.
    fn record_wakes(&mut self, position: usize, completion: &Json) {
        for wake in array(completion.get("wakes")) {
            let settled = wake
                .get("cause")
                .and_then(|cause| cause.get("use"))
                .and_then(Json::as_str)
                .is_some_and(|marker| marker != "current");
            if !settled {
                continue;
            }
            if let Some(job) = wake.get("job") {
                self.settled_wakes
                    .entry(identity(job, None))
                    .or_default()
                    .push(position);
            }
        }
    }

    fn product(&mut self, event: &PublicEvent) -> &mut ProductWork {
        let key = event.metadata.get("product").map_or_else(
            || "?product".to_string(),
            |product| identity(product, Some(&self.canon)),
        );
        self.report.products.entry(key).or_default()
    }

    fn settle_product(&mut self, event: &PublicEvent) {
        let generation = event
            .metadata
            .get("settlement")
            .and_then(|settlement| settlement.get("generation"))
            .and_then(Json::as_u64);
        let changed = event
            .metadata
            .get("settlement")
            .and_then(|settlement| settlement.get("changed"))
            .and_then(Json::as_bool)
            .unwrap_or(false);
        let work = self.product(event);
        work.settlements += 1;
        if changed {
            work.changed += 1;
        } else {
            work.unchanged += 1;
        }
        if let Some(generation) = generation {
            work.generations.insert(generation);
        }
    }

    fn finish_session(&mut self, event: &PublicEvent) {
        let Some(session) = event.metadata.get("session") else {
            return;
        };
        let count = |key: &str| session.get(key).and_then(Json::as_u64).unwrap_or(0);
        let tally = &mut self.report.sessions;
        tally.sessions += 1;
        tally.producer_pokes += count("producer_pokes");
        tally.ignition += count("work_starts_ignition");
        tally.changed_revision_wake += count("work_starts_changed_revision_wake");
        tally.standing_root_frontier += count("work_starts_standing_root_frontier");
        tally.activation_frontier += count("work_starts_activation_frontier");
        tally.blocked_waiter_expansion += count("work_starts_blocked_waiter_expansion");
        tally.unsanctioned_work_starts += count("unsanctioned_work_starts");
        tally.root_scans += count("root_scans");
    }
}

/// The raw `Ty` and `FunctionId` ids an event's payload names.
#[derive(Default)]
struct References {
    types: Vec<u64>,
    functions: Vec<u64>,
}

impl References {
    fn walk(&mut self, value: &Json) {
        match value {
            Json::Object(fields) => {
                for (key, field) in fields {
                    match (key.as_str(), field) {
                        ("arrow", Json::Number(id)) => self.types.extend(id.as_u64()),
                        ("function_id", Json::Number(id)) => self.functions.extend(id.as_u64()),
                        ("input", Json::Array(tys)) => {
                            self.types.extend(tys.iter().filter_map(Json::as_u64));
                        }
                        _ => self.walk(field),
                    }
                }
            }
            Json::Array(items) => {
                for item in items {
                    self.walk(item);
                }
            }
            _ => {}
        }
    }
}

fn array(value: Option<&Json>) -> &[Json] {
    value.and_then(Json::as_array).map_or(&[], Vec::as_slice)
}

fn fact_set(value: Option<&Json>) -> HashSet<String> {
    array(value).iter().map(|fact| identity(fact, None)).collect()
}

/// Re-renders a raw identity string through the canon tables, for report text.
fn canonicalize(raw: &str, canon: &CanonTables) -> String {
    serde_json::from_str::<Json>(raw).map_or_else(|_| raw.to_string(), |value| identity(&value, Some(canon)))
}

/// The identity of one payload object: its fields minus everything that
/// describes state, rendered in key order.
///
/// `BTreeMap` rather than `serde_json::Map` and a nested object rendered as a
/// STRING: both make the order a property of this function rather than of
/// `serde_json`'s feature flags. Passing `canon` substitutes each raw id for
/// its canonical form — the same shape, addressed by meaning.
fn identity(value: &Json, canon: Option<&CanonTables>) -> String {
    let mut fields = BTreeMap::new();
    if let Some(object) = value.as_object() {
        for (key, field) in object {
            if STATE_FIELDS.contains(&key.as_str()) {
                continue;
            }
            fields.insert(key.clone(), identity_field(key, field, canon));
        }
    }
    serde_json::to_string(&fields).expect("identity fields are plain JSON")
}

fn identity_field(key: &str, field: &Json, canon: Option<&CanonTables>) -> Json {
    match (canon, key, field) {
        (Some(canon), "arrow", Json::Number(id)) => Json::String(canon.ty(id.as_u64().unwrap_or_default())),
        (Some(canon), "function_id", Json::Number(id)) => Json::String(canon.function(id.as_u64().unwrap_or_default())),
        (Some(canon), "input", Json::Array(tys)) => Json::Array(
            tys.iter()
                .map(|ty| Json::String(canon.ty(ty.as_u64().unwrap_or_default())))
                .collect(),
        ),
        (_, _, Json::Object(_)) => Json::String(identity(field, canon)),
        _ => field.clone(),
    }
}
