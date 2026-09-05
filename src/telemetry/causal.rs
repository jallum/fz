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
//! Two boundaries in that rule are load-bearing:
//!
//! - `reads` ALONE is not enough. `reads` and `waits` are separate maps, and a
//!   job re-run because a WAIT became satisfiable has the fact only in `waits`.
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
//! Sorting happens only in that packaging step: `canonical_multiset` is the
//! presentation boundary, and replay itself never orders anything.

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
const QUIESCED: &[&str] = &["fz", "compiler2", "work_graph", "quiesced"];
const PRODUCT_SETTLED: &[&str] = &["fz", "compiler2", "pull", "product", "settled"];
const PRODUCT_CACHE_HIT: &[&str] = &["fz", "compiler2", "pull", "product", "cache_hit"];
const PRODUCT_DISPLACED: &[&str] = &["fz", "compiler2", "pull", "product", "displaced"];
const PRODUCT_REQUESTED: &[&str] = &["fz", "compiler2", "pull", "product", "requested"];
const PRODUCT_EVALUATED: &[&str] = &["fz", "compiler2", "pull", "product", "evaluated"];
const PRODUCT_COPUBLISHED: &[&str] = &["fz", "compiler2", "pull", "product", "copublished"];
const DEPENDENCIES_MOVED: &[&str] = &["fz", "compiler2", "work_graph", "dependencies_moved"];
const SESSION_STARTED: &[&str] = &["fz", "compiler2", "pull", "session", "started"];
const SESSION_FINISHED: &[&str] = &["fz", "compiler2", "pull", "session", "finished"];
const BACKEND_REQUEST_STARTED: &[&str] = &["fz", "compiler2", "backend_request", "started"];
const BACKEND_REQUEST_FINISHED: &[&str] = &["fz", "compiler2", "backend_request", "finished"];
const RECURSIVE_GROUP_SEARCHED: &[&str] = &["fz", "compiler2", "pull", "recursive_group", "searched"];
const RECURSIVE_GROUP_PUBLISHED: &[&str] = &["fz", "compiler2", "pull", "recursive_group", "published"];

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
    /// Nothing in the dependency set moved. Kept explicit so a causal gap is
    /// measured rather than silently assigned to an adjacent event.
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

impl FormulaWork {
    fn add(&mut self, work: &Self) {
        self.evaluations += work.evaluations;
        self.initial += work.initial;
        self.content_caused += work.content_caused;
        self.readiness_caused += work.readiness_caused;
        self.uncaused += work.uncaused;
        self.changed_outputs += work.changed_outputs;
        self.unchanged_outputs += work.unchanged_outputs;
        self.wakes += work.wakes;
        self.blocked_completions += work.blocked_completions;
    }
}

/// Work attributed to one product (one canonical `ProductKey`).
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ProductWork {
    pub requests: u64,
    pub evaluations: u64,
    pub settlements: u64,
    pub distinct_generations: u64,
    pub changed: u64,
    pub unchanged: u64,
    pub cache_hits: u64,
    pub retained_cache_hits: u64,
    pub displacements: u64,
    pub first_productions: u64,
    pub reproductions: u64,
    pub equal_reproductions: u64,
    pub cross_request_recomputations: u64,
    pub copublications: u64,
    pub unexplained_evaluations: u64,
    pub recursive_members: u64,
}

/// One exact product identity as it appeared on the public stream. The raw
/// structured value remains authoritative inside a process; canonical folding
/// is a separate reporting operation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RawProductKey {
    pub raw: Json,
}

impl RawProductKey {
    fn new(raw: &Json) -> Self {
        let mut raw = raw.clone();
        if let Some(fields) = raw.as_object_mut() {
            fields.remove("opaque_type");
        }
        Self { raw }
    }

    /// The structured product variant carried by the production event.
    pub fn kind(&self) -> Option<&str> {
        self.raw.get("kind").and_then(Json::as_str)
    }

    /// Reporting-only canonical presentation for cross-process comparison.
    /// Raw structured identity remains the in-process authority.
    pub fn canonical_identity(&self, canon: &CanonTables) -> String {
        render_identity(&canonical_product_value(&self.raw, canon))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct RawIdentity(Json);

impl RawIdentity {
    fn new(raw: &Json) -> Self {
        Self(identity_value(raw, None))
    }

    fn canonical(&self, canon: &CanonTables) -> String {
        render_identity(&identity_value(&self.0, Some(canon)))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProductEvaluationCause {
    Initial,
    FactMovement,
    ProductMovement,
    Displacement,
    Mixed,
    Unexplained,
}

impl ProductEvaluationCause {
    fn name(&self) -> &'static str {
        match self {
            Self::Initial => "initial",
            Self::FactMovement => "fact_movement",
            Self::ProductMovement => "product_movement",
            Self::Displacement => "displacement",
            Self::Mixed => "mixed",
            Self::Unexplained => "unexplained",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProductEvaluationWait {
    Product(RawProductKey),
    Fact(Json),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProductEvaluationTriggerKind {
    Fact,
    ProductSettlement,
    ProductCacheHit,
    ProductDisplacement,
    Displacement,
}

impl ProductEvaluationTriggerKind {
    fn name(self) -> &'static str {
        match self {
            Self::Fact => "fact_movement",
            Self::ProductSettlement => "product_settlement",
            Self::ProductCacheHit => "product_cache_hit",
            Self::ProductDisplacement => "dependency_displacement",
            Self::Displacement => "self_displacement",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProductEvaluationTrigger {
    pub position: usize,
    pub dependency: ProductEvaluationWait,
    pub kind: ProductEvaluationTriggerKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProductEvaluationRecord {
    pub position: usize,
    pub prior_evaluation: Option<usize>,
    pub session: u64,
    pub request: u64,
    pub product: RawProductKey,
    pub prior_waits: Vec<ProductEvaluationWait>,
    pub triggers: Vec<ProductEvaluationTrigger>,
    pub cause: ProductEvaluationCause,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProductPublicationKind {
    Copublished,
    RecursiveGroup,
}

impl ProductPublicationKind {
    fn name(self) -> &'static str {
        match self {
            Self::Copublished => "copublished",
            Self::RecursiveGroup => "recursive_group",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProductPublicationRecord {
    pub position: usize,
    pub session: u64,
    pub publisher: RawProductKey,
    pub peer: RawProductKey,
    pub kind: ProductPublicationKind,
}

/// Aggregate pending-graph query work. Exact publisher/member identity lives
/// in the sibling `ProductPublicationRecord`s rather than being folded into
/// these traversal totals.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct RecursiveSearchWork {
    pub searches: u64,
    pub candidate_inventory: u64,
    pub vertex_visits: u64,
    pub edge_scans: u64,
    pub closed_cycles: u64,
    pub group_members: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecursiveSearchRecord {
    pub position: usize,
    pub session: u64,
    pub request: Option<u64>,
    pub product: RawProductKey,
    pub dependency: RawProductKey,
    pub work: RecursiveSearchWork,
    pub cause: Option<ProductEvaluationCause>,
}

/// One fact KIND's lifecycle over a whole compile, read from the `changed`
/// entries every applied step carries: the distinct facts of that kind the
/// stream named, how many times one appeared out of nothing, and how many
/// times one lost its last publisher.
///
/// `first_appearances > distinct` is the retract-and-remint signature — a fact
/// withdrawn and later re-derived appears from nothing twice.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct FactLifecycle {
    pub distinct: u64,
    pub first_appearances: u64,
    pub retractions: u64,
}

/// The ground-shift traffic in the stream: wakes the scheduler classified as
/// shifts (each one unsettles and rebases the job it wakes) and the
/// completions that ran under a discharged rebase.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ShiftWork {
    pub shift_wakes: u64,
    pub rebased_completions: u64,
}

/// The pull sessions' own work-start accounting, summed over every session in
/// the stream.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct SessionWork {
    pub sessions: u64,
    pub producer_pokes: u64,
    pub ignition: u64,
    pub changed_revision_wake: u64,
    pub activation_frontier: u64,
    pub blocked_waiter_expansion: u64,
    pub unsanctioned_work_starts: u64,
    pub root_scans: u64,
    pub drain_discovery_sweeps: u64,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct FinalPopulation {
    pub reachable_executables: u64,
    pub construction_wrappers: u64,
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
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct CausalReport {
    pub formulas: BTreeMap<String, FormulaWork>,
    pub products: HashMap<RawProductKey, ProductWork>,
    pub product_evaluations: Vec<ProductEvaluationRecord>,
    pub product_publications: Vec<ProductPublicationRecord>,
    pub recursive_search: RecursiveSearchWork,
    pub recursive_searches: Vec<RecursiveSearchRecord>,
    pub sessions: SessionWork,
    pub final_population: FinalPopulation,
    /// Per fact-kind appearance/retraction accounting (fz-kdt.63).
    pub lifecycles: BTreeMap<String, FactLifecycle>,
    /// Ground-shift traffic (fz-kdt.63).
    pub shifts: ShiftWork,
    pub canon: CanonTables,
    /// Evaluations with no moved input, retained with exact formula and
    /// dependency identity rather than hidden in an aggregate.
    pub uncaused: Vec<UncausedEvaluation>,
    /// Readiness-caused evaluations for which no `Settled`
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
        Replay::new(events).run(events)
    }

    /// Derives one report per completed pull request while retaining a
    /// run-wide canonical dictionary. A product whose first-generation
    /// settlement names a key already produced by an earlier request is
    /// counted as cross-request recomputation; this is the signal that exposes
    /// today's fresh-session repopulation and tomorrow's retained reuse.
    pub fn derive_requests(events: &[PublicEvent]) -> Vec<Self> {
        let mut replay = Replay::new(events);
        let mut reports = Vec::new();
        for (index, event) in events.iter().enumerate() {
            replay.process(index, event);
            if event.named(BACKEND_REQUEST_FINISHED) {
                reports.push(replay.take_report());
            }
        }
        replay.assert_complete();
        reports
    }

    /// The comparand. Every counted dimension flattened onto canonical
    /// identity strings, so two runs — two PROCESSES — compare by what work
    /// they did rather than by where their arenas happened to put it.
    pub fn canonical_multiset(&self) -> BTreeMap<String, u64> {
        let mut multiset = BTreeMap::new();
        let (product_names, fact_names, identities) = canonical_identities(self);
        for (identity, id) in &identities {
            put_count(&mut multiset, format!("identity\u{1}{id}\u{1}{identity}"), 1);
        }
        for (formula, work) in &self.formulas {
            let mut put = |dimension: &str, count| {
                put_count(&mut multiset, format!("formula\u{1}{formula}\u{1}{dimension}"), count);
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
            let product = product_identity(product, &product_names, &identities);
            let mut put = |dimension: &str, count| {
                put_count(&mut multiset, format!("product\u{1}{product}\u{1}{dimension}"), count);
            };
            put("settlements", work.settlements);
            put("distinct_generations", work.distinct_generations);
            put("requests", work.requests);
            put("evaluations", work.evaluations);
            put("changed", work.changed);
            put("unchanged", work.unchanged);
            put("cache_hits", work.cache_hits);
            put("retained_cache_hits", work.retained_cache_hits);
            put("displacements", work.displacements);
            put("first_productions", work.first_productions);
            put("reproductions", work.reproductions);
            put("equal_reproductions", work.equal_reproductions);
            put("cross_request_recomputations", work.cross_request_recomputations);
            put("copublications", work.copublications);
            put("unexplained_evaluations", work.unexplained_evaluations);
            put("recursive_members", work.recursive_members);
        }
        for evaluation in &self.product_evaluations {
            let mut prior_waits = evaluation
                .prior_waits
                .iter()
                .map(|wait| canonical_wait(wait, &product_names, &fact_names, &identities))
                .collect::<Vec<_>>();
            prior_waits.sort_by_cached_key(render_identity);
            let mut triggers = evaluation
                .triggers
                .iter()
                .map(|trigger| {
                    serde_json::json!({
                        "kind": trigger.kind.name(),
                        "dependency": canonical_wait(&trigger.dependency, &product_names, &fact_names, &identities),
                    })
                })
                .collect::<Vec<_>>();
            triggers.sort_by_cached_key(render_identity);
            let signature = serde_json::json!({
                "product": product_identity(&evaluation.product, &product_names, &identities),
                "cause": evaluation.cause.name(),
                "prior_waits": prior_waits,
                "triggers": triggers,
            });
            put_count(
                &mut multiset,
                format!("product_evaluation\u{1}{}", render_identity(&signature)),
                1,
            );
        }
        for publication in &self.product_publications {
            let signature = serde_json::json!({
                "kind": publication.kind.name(),
                "publisher": product_identity(&publication.publisher, &product_names, &identities),
                "peer": product_identity(&publication.peer, &product_names, &identities),
            });
            put_count(
                &mut multiset,
                format!("product_publication\u{1}{}", render_identity(&signature)),
                1,
            );
        }
        for search in &self.recursive_searches {
            let signature = serde_json::json!({
                "product": product_identity(&search.product, &product_names, &identities),
                "dependency": product_identity(&search.dependency, &product_names, &identities),
                "cause": search.cause.map(|cause| cause.name()),
                "candidate_inventory": search.work.candidate_inventory,
                "vertex_visits": search.work.vertex_visits,
                "edge_scans": search.work.edge_scans,
                "closed_cycles": search.work.closed_cycles,
                "group_members": search.work.group_members,
            });
            put_count(
                &mut multiset,
                format!("recursive_search_record\u{1}{}", render_identity(&signature)),
                1,
            );
        }
        for (dimension, count) in [
            ("searches", self.recursive_search.searches),
            ("candidate_inventory", self.recursive_search.candidate_inventory),
            ("vertex_visits", self.recursive_search.vertex_visits),
            ("edge_scans", self.recursive_search.edge_scans),
            ("closed_cycles", self.recursive_search.closed_cycles),
            ("group_members", self.recursive_search.group_members),
        ] {
            put_count(&mut multiset, format!("recursive_search\u{1}{dimension}"), count);
        }
        let session = &self.sessions;
        for (dimension, count) in [
            ("sessions", session.sessions),
            ("producer_pokes", session.producer_pokes),
            ("ignition", session.ignition),
            ("changed_revision_wake", session.changed_revision_wake),
            ("activation_frontier", session.activation_frontier),
            ("blocked_waiter_expansion", session.blocked_waiter_expansion),
            ("unsanctioned_work_starts", session.unsanctioned_work_starts),
            ("root_scans", session.root_scans),
            ("drain_discovery_sweeps", session.drain_discovery_sweeps),
        ] {
            put_count(&mut multiset, format!("session\u{1}{dimension}"), count);
        }
        for (kind, lifecycle) in &self.lifecycles {
            for (dimension, count) in [
                ("distinct", lifecycle.distinct),
                ("first_appearances", lifecycle.first_appearances),
                ("retractions", lifecycle.retractions),
            ] {
                put_count(
                    &mut multiset,
                    format!("fact_lifecycle\u{1}{kind}\u{1}{dimension}"),
                    count,
                );
            }
        }
        for (dimension, count) in [
            ("shift_wakes", self.shifts.shift_wakes),
            ("rebased_completions", self.shifts.rebased_completions),
        ] {
            put_count(&mut multiset, format!("ground_shift\u{1}{dimension}"), count);
        }
        put_count(
            &mut multiset,
            "population\u{1}reachable_executables".to_string(),
            self.final_population.reachable_executables,
        );
        put_count(
            &mut multiset,
            "population\u{1}construction_wrappers".to_string(),
            self.final_population.construction_wrappers,
        );
        multiset
    }

    /// Totals across every formula, for a headline.
    pub fn formula_totals(&self) -> FormulaWork {
        let mut totals = FormulaWork::default();
        for work in self.formulas.values() {
            totals.add(work);
        }
        totals
    }

    /// Totals across every product, for a headline.
    pub fn product_totals(&self) -> ProductWork {
        let mut totals = ProductWork::default();
        for work in self.products.values() {
            totals.requests += work.requests;
            totals.evaluations += work.evaluations;
            totals.settlements += work.settlements;
            totals.distinct_generations += work.distinct_generations;
            totals.changed += work.changed;
            totals.unchanged += work.unchanged;
            totals.cache_hits += work.cache_hits;
            totals.retained_cache_hits += work.retained_cache_hits;
            totals.displacements += work.displacements;
            totals.first_productions += work.first_productions;
            totals.reproductions += work.reproductions;
            totals.equal_reproductions += work.equal_reproductions;
            totals.cross_request_recomputations += work.cross_request_recomputations;
            totals.copublications += work.copublications;
            totals.unexplained_evaluations += work.unexplained_evaluations;
            totals.recursive_members += work.recursive_members;
        }
        totals
    }

    pub fn distinct_demanded_products(&self) -> usize {
        self.products.values().filter(|work| work.requests > 0).count()
    }
}

fn put_count(multiset: &mut BTreeMap<String, u64>, key: String, count: u64) {
    if count > 0 {
        *multiset.entry(key).or_default() += count;
    }
}

fn canonical_identities(
    report: &CausalReport,
) -> (
    HashMap<RawProductKey, String>,
    HashMap<RawIdentity, String>,
    BTreeMap<String, u64>,
) {
    let mut products = HashMap::new();
    let mut facts = HashMap::new();
    let mut remember_product = |product: &RawProductKey| {
        products
            .entry(product.clone())
            .or_insert_with(|| product.canonical_identity(&report.canon));
    };
    for product in report.products.keys() {
        remember_product(product);
    }
    for evaluation in &report.product_evaluations {
        remember_product(&evaluation.product);
        for wait in evaluation
            .prior_waits
            .iter()
            .chain(evaluation.triggers.iter().map(|trigger| &trigger.dependency))
        {
            match wait {
                ProductEvaluationWait::Product(product) => remember_product(product),
                ProductEvaluationWait::Fact(fact) => {
                    let fact = RawIdentity::new(fact);
                    facts
                        .entry(fact.clone())
                        .or_insert_with(|| fact.canonical(&report.canon));
                }
            }
        }
    }
    for publication in &report.product_publications {
        remember_product(&publication.publisher);
        remember_product(&publication.peer);
    }
    for search in &report.recursive_searches {
        remember_product(&search.product);
        remember_product(&search.dependency);
    }
    let names = products
        .values()
        .chain(facts.values())
        .cloned()
        .collect::<BTreeSet<_>>();
    let identities = names
        .into_iter()
        .enumerate()
        .map(|(id, identity)| (identity, id as u64))
        .collect();
    (products, facts, identities)
}

fn product_identity(
    product: &RawProductKey,
    products: &HashMap<RawProductKey, String>,
    identities: &BTreeMap<String, u64>,
) -> u64 {
    identities[&products[product]]
}

fn canonical_wait(
    wait: &ProductEvaluationWait,
    products: &HashMap<RawProductKey, String>,
    facts: &HashMap<RawIdentity, String>,
    identities: &BTreeMap<String, u64>,
) -> Json {
    match wait {
        ProductEvaluationWait::Product(product) => {
            serde_json::json!({"product": product_identity(product, products, identities)})
        }
        ProductEvaluationWait::Fact(fact) => {
            let identity = RawIdentity::new(fact);
            serde_json::json!({
                "fact": identities[&facts[&identity]],
                "use": fact.get("use").cloned().unwrap_or(Json::Null),
            })
        }
    }
}

fn evaluation_cause(initial: bool, triggers: &[ProductEvaluationTrigger]) -> ProductEvaluationCause {
    if initial {
        return ProductEvaluationCause::Initial;
    }
    let fact = triggers
        .iter()
        .any(|trigger| trigger.kind == ProductEvaluationTriggerKind::Fact);
    let product = triggers.iter().any(|trigger| {
        matches!(
            trigger.kind,
            ProductEvaluationTriggerKind::ProductSettlement
                | ProductEvaluationTriggerKind::ProductCacheHit
                | ProductEvaluationTriggerKind::ProductDisplacement
        )
    });
    let displacement = triggers
        .iter()
        .any(|trigger| trigger.kind == ProductEvaluationTriggerKind::Displacement);
    match (fact, product, displacement) {
        (false, false, false) => ProductEvaluationCause::Unexplained,
        (true, false, false) => ProductEvaluationCause::FactMovement,
        (false, true, false) => ProductEvaluationCause::ProductMovement,
        (false, false, true) => ProductEvaluationCause::Displacement,
        _ => ProductEvaluationCause::Mixed,
    }
}

/// One fact movement, at the stream position that carried it.
struct Movement {
    position: usize,
    content: bool,
    readiness: bool,
}

#[derive(Debug, Clone)]
struct WaitIdentity {
    wait: ProductEvaluationWait,
    lookup: WaitLookup,
}

#[derive(Debug, Clone)]
enum WaitLookup {
    Product(RawProductKey),
    Fact(RawIdentity),
}

impl WaitIdentity {
    fn from_json(wait: &Json) -> Option<Self> {
        if let Some(product) = wait.get("product") {
            let product = RawProductKey::new(product);
            return Some(Self {
                wait: ProductEvaluationWait::Product(product.clone()),
                lookup: WaitLookup::Product(product),
            });
        }
        wait.get("fact").map(|fact| Self {
            wait: ProductEvaluationWait::Fact(fact.clone()),
            lookup: WaitLookup::Fact(RawIdentity::new(fact)),
        })
    }
}

#[derive(Debug, Clone, Copy)]
struct ProductMovement {
    position: usize,
    kind: ProductEvaluationTriggerKind,
}

struct SessionReplay {
    id: u64,
    movements: HashMap<RawProductKey, Vec<ProductMovement>>,
    requests: HashMap<u64, (RawProductKey, usize)>,
    evaluations: HashMap<RawProductKey, (usize, Vec<WaitIdentity>)>,
}

impl SessionReplay {
    fn new(id: u64) -> Self {
        Self {
            id,
            movements: HashMap::new(),
            requests: HashMap::new(),
            evaluations: HashMap::new(),
        }
    }
}

/// What the replay remembers about a formula between its evaluations. Keyed by
/// RAW identity: two arena-distinct activations are two formulas here even when
/// they share a canonical form, because each has its own conclusion history.
#[derive(Default)]
struct FormulaHistory {
    last_conclusion: Option<usize>,
    blocked: HashSet<RawIdentity>,
}

struct Replay {
    canon: CanonTables,
    movements: HashMap<RawIdentity, Vec<Movement>>,
    settled_wakes: HashMap<RawIdentity, Vec<usize>>,
    named_facts: HashMap<String, HashSet<RawIdentity>>,
    history: HashMap<RawIdentity, FormulaHistory>,
    formula_work: HashMap<RawIdentity, FormulaWork>,
    sessions: Vec<SessionReplay>,
    product_requests: HashSet<(u64, u64)>,
    request_open: bool,
    has_completed_request: bool,
    prior_request_products: HashSet<RawProductKey>,
    current_request_settlements: HashSet<RawProductKey>,
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
            named_facts: HashMap::new(),
            history: HashMap::new(),
            formula_work: HashMap::new(),
            sessions: Vec::new(),
            product_requests: HashSet::new(),
            request_open: false,
            has_completed_request: false,
            prior_request_products: HashSet::new(),
            current_request_settlements: HashSet::new(),
            defined_types: HashSet::new(),
            defined_functions: HashSet::new(),
            report: CausalReport::default(),
        }
    }

    /// One forward pass. Classification only ever looks backwards, so the
    /// movements and wakes an event carries are recorded AFTER it is
    /// classified — which is also what makes the window's lower bound
    /// inclusive: a formula's own previous conclusion is already indexed.
    fn run(mut self, events: &[PublicEvent]) -> CausalReport {
        for (position, event) in events.iter().enumerate() {
            self.process(position, event);
        }
        self.assert_complete();
        self.take_report()
    }

    fn process(&mut self, position: usize, event: &PublicEvent) {
        self.note_definitions(position, event);
        if event.named(BACKEND_REQUEST_STARTED) {
            assert!(!self.request_open, "backend requests must not overlap");
            assert_eq!(
                event.metadata["request"]["status"].as_str(),
                Some("started"),
                "backend request start must carry its typed lifecycle state"
            );
            self.request_open = true;
        } else if event.named(BACKEND_REQUEST_FINISHED) {
            assert!(self.request_open, "backend request finished without a start");
            self.request_open = false;
            let request = &event.metadata["request"];
            match request.get("status").and_then(Json::as_str) {
                Some("success") => {
                    self.report.final_population.reachable_executables =
                        request.get("executables").and_then(Json::as_u64).unwrap_or(0);
                    self.report.final_population.construction_wrappers =
                        request.get("construction_wrappers").and_then(Json::as_u64).unwrap_or(0);
                }
                Some("failure") => {}
                status => panic!("backend request finish carried invalid lifecycle state {status:?}"),
            }
            self.prior_request_products
                .extend(self.current_request_settlements.drain());
            self.has_completed_request = true;
        } else if event.named(SESSION_STARTED) {
            let session = event.metadata["session_id"].as_u64().expect("session start identity");
            assert!(
                !self.sessions.iter().any(|active| active.id == session),
                "session {session} started twice"
            );
            self.sessions.push(SessionReplay::new(session));
        } else if event.named(APPLIED) {
            self.apply(position, event);
        } else if event.named(QUIESCED) || event.named(DEPENDENCIES_MOVED) {
            self.record_non_formula_step(position, event);
        } else if event.named(PRODUCT_SETTLED) {
            self.settle_product(position, event);
        } else if event.named(PRODUCT_CACHE_HIT) {
            self.cache_hit(position, event);
        } else if event.named(PRODUCT_DISPLACED) {
            self.product(event).displacements += 1;
            self.record_product_movement(position, event, ProductEvaluationTriggerKind::ProductDisplacement);
        } else if event.named(PRODUCT_REQUESTED) {
            self.request_product(position, event);
        } else if event.named(PRODUCT_EVALUATED) {
            self.evaluate_product(position, event);
        } else if event.named(PRODUCT_COPUBLISHED) {
            self.record_publication(position, event, ProductPublicationKind::Copublished);
        } else if event.named(RECURSIVE_GROUP_PUBLISHED) {
            self.record_publication(position, event, ProductPublicationKind::RecursiveGroup);
        } else if event.named(RECURSIVE_GROUP_SEARCHED) {
            self.record_recursive_group(position, event);
        } else if event.named(SESSION_FINISHED) {
            self.finish_session(event);
            let session = event.metadata["session_id"].as_u64().expect("session finish identity");
            let active = self.sessions.pop().expect("session finished without a start");
            assert_eq!(active.id, session, "session lifecycles must be nested");
        }
    }

    fn assert_complete(&self) {
        assert!(self.sessions.is_empty(), "unfinished product sessions in causal stream");
        assert!(!self.request_open, "backend request started without finishing");
    }

    fn take_report(&mut self) -> CausalReport {
        let mut report = std::mem::take(&mut self.report);
        for (formula, work) in std::mem::take(&mut self.formula_work) {
            report
                .formulas
                .entry(formula.canonical(&self.canon))
                .or_default()
                .add(&work);
        }
        self.named_facts.clear();
        report.canon = self.canon.clone();
        report
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

    fn apply(&mut self, position: usize, event: &PublicEvent) {
        let Some(completion) = event.metadata.get("completion") else {
            return;
        };
        let raw_formula = RawIdentity::new(completion);
        let reads = fact_set(event.semantic.get("reads"));
        let blocked = fact_set(completion.get("blocked"));
        let previous = self
            .history
            .get(&raw_formula)
            .and_then(|history| history.last_conclusion);
        let deps = self.dependency_set(&raw_formula, &reads);
        let cause = match previous {
            None => Cause::Initial,
            Some(previous) => self.cause(previous, position, &deps),
        };

        let work = self.formula_work.entry(raw_formula.clone()).or_default();
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
            let mut names = deps.iter().map(|fact| fact.canonical(&self.canon)).collect::<Vec<_>>();
            names.sort();
            self.report.uncaused.push(UncausedEvaluation {
                position,
                formula: raw_formula.canonical(&self.canon),
                dependencies: names,
            });
        }
        if matches!(cause, Cause::Readiness) && !self.woken_by_settled(&raw_formula, position) {
            self.report.readiness_without_settled_wake.push(UncausedEvaluation {
                position,
                formula: raw_formula.canonical(&self.canon),
                dependencies: Vec::new(),
            });
        }

        self.record_movements(position, completion);
        self.record_wakes(position, completion);
        self.record_ground_shifts(completion);
        let history = self.history.entry(raw_formula).or_default();
        history.last_conclusion = Some(position);
        history.blocked = blocked;
    }

    /// A drain-arbiter or external dependency step. No scheduler formula ran,
    /// so there is nothing to classify, but its movements and wakes are exact
    /// evidence for later formula evaluations.
    fn record_non_formula_step(&mut self, position: usize, event: &PublicEvent) {
        let Some(step) = event.metadata.get("step") else {
            return;
        };
        self.record_movements(position, step);
        self.record_wakes(position, step);
        self.record_ground_shifts(step);
    }

    /// The step's own ground-shift accounting: what each `changed` entry did
    /// to its fact's existence, how many of the wakes it caused were
    /// classified as shifts, and whether the step itself discharged a rebase
    /// (a job completion carries `rebased`; the drain arbiter's step has no
    /// such field and counts none). All read straight off the emitted step —
    /// nothing here reconstructs scheduler state.
    fn record_ground_shifts(&mut self, step: &Json) {
        if step.get("rebased").and_then(Json::as_bool).unwrap_or(false) {
            self.report.shifts.rebased_completions += 1;
        }
        for change in array(step.get("changed")) {
            let Some(kind) = change.get("kind").and_then(Json::as_str) else {
                continue;
            };
            let appeared = change.get("old_revision").is_none_or(Json::is_null);
            let retracted = change.get("new_revision").is_none_or(Json::is_null);
            let lifecycle = self.report.lifecycles.entry(kind.to_string()).or_default();
            if appeared && !retracted {
                lifecycle.first_appearances += 1;
            }
            if retracted && !appeared {
                lifecycle.retractions += 1;
            }
            if self
                .named_facts
                .entry(kind.to_string())
                .or_default()
                .insert(RawIdentity::new(change))
            {
                lifecycle.distinct += 1;
            }
        }
        for wake in array(step.get("wakes")) {
            if wake.get("shift").and_then(Json::as_bool).unwrap_or(false) {
                self.report.shifts.shift_wakes += 1;
            }
        }
    }

    /// The facts an evaluation may name as its cause. `reads` is the current
    /// completion's read set; the blocked-set is the one the formula's PREVIOUS
    /// completion recorded, because that is the wait whose satisfaction re-ran
    /// it.
    fn dependency_set(&self, raw_formula: &RawIdentity, reads: &HashSet<RawIdentity>) -> HashSet<RawIdentity> {
        let blocked = self.history.get(raw_formula).map(|history| &history.blocked);
        reads.iter().chain(blocked.into_iter().flatten()).cloned().collect()
    }

    fn cause(&self, previous: usize, position: usize, deps: &HashSet<RawIdentity>) -> Cause {
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

    fn woken_by_settled(&self, raw_formula: &RawIdentity, position: usize) -> bool {
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
            let content = revision(change, "old_revision") != revision(change, "new_revision");
            let readiness = change.get("old_settled") != change.get("new_settled");
            classified.insert(RawIdentity::new(change), (content, readiness));
        }
        let mut seen = HashSet::new();
        for movement in array(completion.get("movements")) {
            let key = RawIdentity::new(movement);
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

    /// A wake whose cause is `Settled` is the readiness
    /// evidence: agenda state no fact movement reconstructs.
    fn record_wakes(&mut self, position: usize, completion: &Json) {
        for wake in array(completion.get("wakes")) {
            let settled = wake
                .get("cause")
                .and_then(|cause| cause.get("use"))
                .and_then(Json::as_str)
                == Some("settled");
            if !settled {
                continue;
            }
            if let Some(job) = wake.get("job") {
                self.settled_wakes
                    .entry(RawIdentity::new(job))
                    .or_default()
                    .push(position);
            }
        }
    }

    fn product(&mut self, event: &PublicEvent) -> &mut ProductWork {
        let key = event
            .metadata
            .get("product")
            .map(RawProductKey::new)
            .unwrap_or_else(|| RawProductKey::new(&Json::Null));
        self.report.products.entry(key).or_default()
    }

    fn record_publication(&mut self, position: usize, event: &PublicEvent, kind: ProductPublicationKind) {
        let Some(publisher) = event.metadata.get("publisher") else {
            return;
        };
        let Some(peer) = event.metadata.get("peer") else {
            return;
        };
        let publisher = RawProductKey::new(publisher);
        let work = self.report.products.entry(publisher.clone()).or_default();
        match kind {
            ProductPublicationKind::Copublished => work.copublications += 1,
            ProductPublicationKind::RecursiveGroup => work.recursive_members += 1,
        }
        self.report.product_publications.push(ProductPublicationRecord {
            position,
            session: self
                .sessions
                .last()
                .map(|session| session.id)
                .expect("product publication outside a session"),
            publisher,
            peer: RawProductKey::new(peer),
            kind,
        });
    }

    fn cache_hit(&mut self, position: usize, event: &PublicEvent) {
        let Some(product) = event.metadata.get("product") else {
            return;
        };
        let key = RawProductKey::new(product);
        let retained = self.has_completed_request
            && self.prior_request_products.contains(&key)
            && !self.current_request_settlements.contains(&key);
        let work = self.report.products.entry(key).or_default();
        work.cache_hits += 1;
        work.retained_cache_hits += u64::from(retained);
        self.record_product_movement(position, event, ProductEvaluationTriggerKind::ProductCacheHit);
    }

    fn request_product(&mut self, position: usize, event: &PublicEvent) {
        let Some(product) = event.metadata.get("product") else {
            return;
        };
        let session = self.sessions.last_mut().expect("product request outside a session");
        let session_id = session.id;
        let key = RawProductKey::new(product);
        let request = event.metadata["request_id"].as_u64().expect("product request identity");
        assert!(
            session.requests.insert(request, (key.clone(), position)).is_none(),
            "session {} reused product request {request}",
            session.id
        );
        assert!(
            self.product_requests.insert((session_id, request)),
            "session {session_id} reused product request {request} across activations"
        );
        self.report.products.entry(key).or_default().requests += 1;
    }

    fn settle_product(&mut self, position: usize, event: &PublicEvent) {
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
        let Some(product) = event.metadata.get("product") else {
            return;
        };
        let key = RawProductKey::new(product);
        let cross_request = self.has_completed_request
            && generation == Some(1)
            && changed
            && self.prior_request_products.contains(&key);
        self.current_request_settlements.insert(key.clone());
        let work = self.report.products.entry(key).or_default();
        work.settlements += 1;
        if changed {
            work.changed += 1;
            work.distinct_generations += 1;
        } else {
            work.unchanged += 1;
        }
        if !changed {
            work.equal_reproductions += 1;
        } else if generation == Some(1) {
            work.first_productions += 1;
        } else {
            work.reproductions += 1;
        }
        work.cross_request_recomputations += u64::from(cross_request);
        self.record_product_movement(position, event, ProductEvaluationTriggerKind::ProductSettlement);
    }

    fn record_recursive_group(&mut self, position: usize, event: &PublicEvent) {
        let Some(search) = event.metadata.get("search") else {
            return;
        };
        let Some(product) = event.metadata.get("product") else {
            return;
        };
        let Some(dependency) = event.metadata.get("dependency") else {
            return;
        };
        let count = |key: &str| search.get(key).and_then(Json::as_u64).unwrap_or(0);
        let cycle_closed = search.get("cycle_closed").and_then(Json::as_bool).unwrap_or(false);
        let work = RecursiveSearchWork {
            searches: 1,
            candidate_inventory: count("candidate_inventory"),
            vertex_visits: count("vertex_visits"),
            edge_scans: count("edge_scans"),
            closed_cycles: u64::from(cycle_closed),
            group_members: count("group_members"),
        };
        let totals = &mut self.report.recursive_search;
        totals.searches += work.searches;
        totals.candidate_inventory += work.candidate_inventory;
        totals.vertex_visits += work.vertex_visits;
        totals.edge_scans += work.edge_scans;
        totals.closed_cycles += work.closed_cycles;
        totals.group_members += work.group_members;
        self.report.recursive_searches.push(RecursiveSearchRecord {
            position,
            session: self
                .sessions
                .last()
                .map(|session| session.id)
                .expect("recursive search outside a session"),
            request: None,
            product: RawProductKey::new(product),
            dependency: RawProductKey::new(dependency),
            work,
            cause: None,
        });
    }

    fn record_product_movement(&mut self, position: usize, event: &PublicEvent, kind: ProductEvaluationTriggerKind) {
        let Some(product) = event.metadata.get("product") else {
            return;
        };
        self.sessions
            .last_mut()
            .expect("product movement outside a session")
            .movements
            .entry(RawProductKey::new(product))
            .or_default()
            .push(ProductMovement { position, kind });
    }

    fn evaluate_product(&mut self, position: usize, event: &PublicEvent) {
        let Some(product) = event.metadata.get("product") else {
            return;
        };
        let session = self.sessions.last().expect("product evaluation outside a session");
        let product = RawProductKey::new(product);
        let request = event.metadata["request_id"]
            .as_u64()
            .expect("product evaluation request identity");
        let session_id = session.id;
        let (requested_product, started) = session.requests[&request].clone();
        assert_eq!(
            requested_product, product,
            "session {session_id} request {request} evaluated a different product"
        );
        let prior = session.evaluations.get(&product).cloned();
        let prior_waits = prior
            .as_ref()
            .map(|(_, waits)| waits.iter().map(|wait| wait.wait.clone()).collect())
            .unwrap_or_default();
        let mut triggers = Vec::new();
        if let Some((previous, waits)) = &prior {
            for wait in waits {
                match &wait.lookup {
                    WaitLookup::Product(dependency) => {
                        for movement in session
                            .movements
                            .get(dependency)
                            .into_iter()
                            .flatten()
                            .filter(|movement| movement.position >= *previous && movement.position < started)
                        {
                            triggers.push(ProductEvaluationTrigger {
                                position: movement.position,
                                dependency: wait.wait.clone(),
                                kind: movement.kind,
                            });
                        }
                    }
                    WaitLookup::Fact(dependency) => {
                        for movement in self
                            .movements
                            .get(dependency)
                            .into_iter()
                            .flatten()
                            .filter(|movement| movement.position >= *previous && movement.position < started)
                        {
                            triggers.push(ProductEvaluationTrigger {
                                position: movement.position,
                                dependency: wait.wait.clone(),
                                kind: ProductEvaluationTriggerKind::Fact,
                            });
                        }
                    }
                }
            }
            for movement in session
                .movements
                .get(&product)
                .into_iter()
                .flatten()
                .filter(|movement| {
                    movement.kind == ProductEvaluationTriggerKind::ProductDisplacement
                        && movement.position >= *previous
                        && movement.position < started
                })
            {
                triggers.push(ProductEvaluationTrigger {
                    position: movement.position,
                    dependency: ProductEvaluationWait::Product(product.clone()),
                    kind: ProductEvaluationTriggerKind::Displacement,
                });
            }
        }
        let cause = evaluation_cause(prior.is_none(), &triggers);
        let waits = event
            .metadata
            .get("outcome")
            .and_then(|outcome| outcome.get("waits"))
            .and_then(Json::as_array)
            .into_iter()
            .flatten()
            .filter_map(WaitIdentity::from_json)
            .collect::<Vec<_>>();
        self.sessions
            .last_mut()
            .expect("product evaluation outside a session")
            .evaluations
            .insert(product.clone(), (position, waits));
        for search in self.report.recursive_searches.iter_mut().filter(|search| {
            search.session == session_id
                && search.product == product
                && search.position >= started
                && search.position < position
        }) {
            search.request = Some(request);
            search.cause = Some(cause);
        }
        let work = self.report.products.entry(product.clone()).or_default();
        work.evaluations += 1;
        work.unexplained_evaluations += u64::from(cause == ProductEvaluationCause::Unexplained);
        self.report.product_evaluations.push(ProductEvaluationRecord {
            position,
            prior_evaluation: prior.as_ref().map(|(position, _)| *position),
            session: session_id,
            request,
            product,
            prior_waits,
            triggers,
            cause,
        });
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
        tally.activation_frontier += count("work_starts_activation_frontier");
        tally.blocked_waiter_expansion += count("work_starts_blocked_waiter_expansion");
        tally.unsanctioned_work_starts += count("unsanctioned_work_starts");
        tally.root_scans += count("root_scans");
        tally.drain_discovery_sweeps += count("drain_discovery_sweeps");
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
                        ("input" | "surface" | "surface_tys", Json::Array(tys)) => {
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

/// One side of a `changed` entry's revision pair, as the ENGINE compares it.
/// A cumulative fact present at bottom renders `0` and an absent one renders
/// `null`, and no reader can tell those apart, so both read as 0 here --
/// `FactChange::content_changed` says the same thing
/// (`.agent/docs/fact-engine.md`, *Absence is bottom*). Only a cumulative fact
/// is ever minted at 0, so a replacing fact's appearance and retraction still
/// count as movements.
fn revision(change: &Json, field: &str) -> u64 {
    change.get(field).and_then(Json::as_u64).unwrap_or(0)
}

fn array(value: Option<&Json>) -> &[Json] {
    value.and_then(Json::as_array).map_or(&[], Vec::as_slice)
}

fn fact_set(value: Option<&Json>) -> HashSet<RawIdentity> {
    array(value).iter().map(RawIdentity::new).collect()
}

/// Canonical reporting projection for a product key. Unlike fact identity,
/// every product field is semantic; this substitutes stream-local ids without
/// filtering state-shaped names that a product is allowed to own.
fn canonical_product_value(value: &Json, canon: &CanonTables) -> Json {
    match value {
        Json::Object(fields) => Json::Object(
            fields
                .iter()
                .map(|(key, field)| {
                    let field = match (key.as_str(), field) {
                        ("arrow", Json::Number(id)) => Json::String(canon.ty(id.as_u64().unwrap_or_default())),
                        ("function_id", Json::Number(id)) => {
                            Json::String(canon.function(id.as_u64().unwrap_or_default()))
                        }
                        ("input" | "surface" | "surface_tys", Json::Array(tys)) => Json::Array(
                            tys.iter()
                                .map(|ty| {
                                    ty.as_u64().map_or_else(
                                        || canonical_product_value(ty, canon),
                                        |id| Json::String(canon.ty(id)),
                                    )
                                })
                                .collect(),
                        ),
                        _ => canonical_product_value(field, canon),
                    };
                    (key.clone(), field)
                })
                .collect(),
        ),
        Json::Array(items) => Json::Array(items.iter().map(|item| canonical_product_value(item, canon)).collect()),
        _ => value.clone(),
    }
}

/// The structured identity of one payload object: its fields minus everything
/// that describes state. Canonical type/function text is substituted only
/// while packaging a report for display or cross-process comparison.
fn identity_value(value: &Json, canon: Option<&CanonTables>) -> Json {
    let mut fields = serde_json::Map::new();
    if let Some(object) = value.as_object() {
        for (key, field) in object {
            if STATE_FIELDS.contains(&key.as_str()) {
                continue;
            }
            fields.insert(key.clone(), identity_field(key, field, canon));
        }
    }
    Json::Object(fields)
}

fn identity_field(key: &str, field: &Json, canon: Option<&CanonTables>) -> Json {
    match (canon, key, field) {
        (canon, "product", _) => canon.map_or_else(|| field.clone(), |canon| canonical_product_value(field, canon)),
        (Some(canon), "arrow", Json::Number(id)) => Json::String(canon.ty(id.as_u64().unwrap_or_default())),
        (Some(canon), "function_id", Json::Number(id)) => Json::String(canon.function(id.as_u64().unwrap_or_default())),
        (Some(canon), "input" | "surface" | "surface_tys", Json::Array(tys)) => Json::Array(
            tys.iter()
                .map(|ty| Json::String(canon.ty(ty.as_u64().unwrap_or_default())))
                .collect(),
        ),
        (_, _, Json::Object(_)) => identity_value(field, canon),
        _ => field.clone(),
    }
}

fn render_identity(identity: &Json) -> String {
    serde_json::to_string(identity).expect("identity fields are plain JSON")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dependency_identity_preserves_the_complete_nested_product_key() {
        let raw = serde_json::json!({
            "kind": "Product", "root_id": 7, "use": "settled", "revision": 3,
            "product": {"kind": "test_product", "revision": 2, "nested": {"changed": true}}
        });
        assert_eq!(
            RawIdentity::new(&raw).0,
            serde_json::json!({
                "kind": "Product", "root_id": 7,
                "product": {"kind": "test_product", "revision": 2, "nested": {"changed": true}}
            })
        );
    }

    #[test]
    fn construction_target_surfaces_use_the_trace_type_dictionary() {
        let canon = CanonTables {
            types: HashMap::from([(7, "int".to_string()), (8, "atom".to_string())]),
            functions: HashMap::new(),
        };
        let raw = serde_json::json!({
            "kind": "DeriveCallableConstructionTarget",
            "surface": [7, 8],
        });

        assert_eq!(
            serde_json::from_str::<Json>(&RawIdentity::new(&raw).canonical(&canon)).unwrap(),
            serde_json::json!({
                "kind": "DeriveCallableConstructionTarget",
                "surface": ["int", "atom"],
            })
        );
        let mut references = References::default();
        references.walk(&raw);
        assert_eq!(references.types, vec![7, 8]);
    }

    #[test]
    fn raw_product_identity_removes_only_its_renderer_annotation() {
        let raw = serde_json::json!({
            "opaque_type": "fz::compiler2::pull::ProductKey",
            "kind": "runtime_demand",
            "use": "settled",
            "revision": 3,
            "old_revision": 2,
            "new_revision": 3,
            "settled": true,
            "changed": false,
            "waits": [{"use": "current", "revision": 7}],
            "nested": {"opaque_type": "semantic nested field", "changed": true},
        });
        let normalized = RawProductKey::new(&raw);
        assert_eq!(
            normalized.raw,
            serde_json::json!({
                "kind": "runtime_demand",
                "use": "settled",
                "revision": 3,
                "old_revision": 2,
                "new_revision": 3,
                "settled": true,
                "changed": false,
                "waits": [{"use": "current", "revision": 7}],
                "nested": {"opaque_type": "semantic nested field", "changed": true},
            })
        );

        let mut other_renderer = raw.clone();
        other_renderer["opaque_type"] = Json::String("another renderer type".to_string());
        assert_eq!(normalized, RawProductKey::new(&other_renderer));
        for field in [
            "use",
            "revision",
            "old_revision",
            "new_revision",
            "settled",
            "changed",
            "waits",
            "nested",
        ] {
            let mut changed = raw.clone();
            changed[field] = Json::Null;
            assert_ne!(normalized, RawProductKey::new(&changed), "{field} remains semantic");
        }
    }

    #[test]
    fn canonical_product_identity_substitutes_ids_without_filtering_fields() {
        let canon = CanonTables {
            types: HashMap::from([(7, "int".to_string())]),
            functions: HashMap::from([(11, "module.function".to_string())]),
        };
        let raw = serde_json::json!({
            "opaque_type": "renderer annotation",
            "kind": "runtime_demand",
            "arrow": 7,
            "function_id": 11,
            "input": [7],
            "use": "settled",
            "revision": 3,
            "settled": true,
            "changed": false,
            "nested": {
                "opaque_type": "semantic nested field",
                "changed": true,
                "items": [{"use": "current", "revision": 9}],
            },
        });
        let product = RawProductKey::new(&raw);
        let canonical = product.canonical_identity(&canon);
        assert_eq!(
            serde_json::from_str::<Json>(&canonical).unwrap(),
            serde_json::json!({
                "kind": "runtime_demand",
                "arrow": "int",
                "function_id": "module.function",
                "input": ["int"],
                "use": "settled",
                "revision": 3,
                "settled": true,
                "changed": false,
                "nested": {
                    "opaque_type": "semantic nested field",
                    "changed": true,
                    "items": [{"use": "current", "revision": 9}],
                },
            })
        );

        let mut renderer_variant = raw.clone();
        renderer_variant["opaque_type"] = Json::String("other renderer".to_string());
        assert_eq!(
            canonical,
            RawProductKey::new(&renderer_variant).canonical_identity(&canon)
        );
        for field in ["use", "revision", "settled", "changed", "nested"] {
            let mut variant = raw.clone();
            variant[field] = Json::Null;
            assert_ne!(
                canonical,
                RawProductKey::new(&variant).canonical_identity(&canon),
                "canonical reporting must preserve {field}"
            );
        }

        let mut nested_opaque_variant = raw.clone();
        nested_opaque_variant["nested"]["opaque_type"] = Json::String("other semantic nested field".to_string());
        assert_ne!(
            canonical,
            RawProductKey::new(&nested_opaque_variant).canonical_identity(&canon)
        );
        let mut nested_array_variant = raw.clone();
        nested_array_variant["nested"]["items"][0]["changed"] = Json::Bool(true);
        assert_ne!(
            canonical,
            RawProductKey::new(&nested_array_variant).canonical_identity(&canon)
        );

        let mut report = CausalReport {
            canon,
            ..CausalReport::default()
        };
        report.products.insert(
            product,
            ProductWork {
                requests: 1,
                ..ProductWork::default()
            },
        );
        for variant in [
            {
                let mut variant = raw;
                variant["use"] = Json::String("current".to_string());
                variant
            },
            nested_opaque_variant,
            nested_array_variant,
        ] {
            report.products.insert(
                RawProductKey::new(&variant),
                ProductWork {
                    requests: 1,
                    ..ProductWork::default()
                },
            );
        }
        let requests = report
            .canonical_multiset()
            .into_iter()
            .filter(|(key, _)| key.starts_with("product\u{1}") && key.ends_with("\u{1}requests"))
            .collect::<Vec<_>>();
        assert_eq!(
            requests.len(),
            4,
            "canonical multiset must retain top-level, nested-object, and nested-array product state"
        );
        assert!(requests.iter().all(|(_, count)| *count == 1));
    }
}
