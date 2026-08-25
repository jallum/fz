//! The running pull-only guard: every job entering the agenda on a
//! production-driven path must be attributable to a sanctioned
//! `WorkStartReason` (see `scheduler.rs`), and no producer may discover work
//! by scanning the whole fact table (`Scheduler::fact_keys`).
//!
//! Each case drives one fixture through the real front door (`submit_code` +
//! `submit_root`, exactly the CLI/product path) to its backend product and
//! reads the finished pull session's `WorkStartTally` through the session's
//! own accessor. The guard asserts three things:
//!
//! - `unsanctioned_work_starts() == 0` — no job entered the agenda under
//!   `WorkStartReason::Unclassified`. A future enqueue call site that forgets
//!   to pass a sanctioned reason — the shape a reintroduced `follow_up`-style
//!   push would take — lands here by construction and trips this red.
//! - `root_scans == 0` — no producer discovered work by scanning the whole
//!   fact table.
//! - `ignition == 2` — `Ignition` tags ONLY the true external front-door
//!   work-starts (one `submit_code`'s `IndexCode`, one `submit_root`'s
//!   `SeedRoot`). This is the soundness assertion: it fails if any internal
//!   (mid-job) caller ever drives a job as `Ignition` again — the exact hole
//!   this guard originally exposed in `ensure_runtime_module` (a runtime
//!   module minted mid-job via `submit_code`, mislabeled the external front
//!   door). With that push eliminated, `unsanctioned == 0` holds because
//!   there is no misclassified push left, not because one is hidden under
//!   `Ignition`.
//!
//! NOTE ON THE GUARD'S BOUNDARY: this catches an *untagged* enqueue (a new
//! call site that omits a reason → `Unclassified`). It does not by itself
//! catch a deliberately *mislabeled* push (a new internal caller that passes,
//! say, `Ignition` by hand). The `ignition == N` assertion is the backstop
//! for exactly that class: if the external ignition count ever exceeds the
//! true front-door count, an internal caller mislabeled its work-start.

use super::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

/// One `submit_code` (its `IndexCode`) plus one `submit_root` (its `SeedRoot`)
/// are the only external ignitions for a single-file, single-root fixture.
/// `ScopeCode` is only enqueued by `submit_code` when a root already exists,
/// which it does not at `submit_code` time here (the root is submitted after),
/// so it is not an ignition — it is pulled.
const EXTERNAL_IGNITIONS: u64 = 2;

fn assert_pull_only(name: &str, source: &str) {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some(name.to_string()),
        text: source.to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let tally = compiler
        .drive_root_backend_work_starts(root_id)
        .unwrap_or_else(|error| panic!("{name} should drive to its backend product: {error}"));

    assert_eq!(
        tally.unsanctioned_work_starts(),
        0,
        "{name}: {} job(s) entered the agenda without an attributable sanctioned WorkStartReason \
         -- this is exactly the shape a reintroduced push would take",
        tally.unsanctioned_work_starts(),
    );
    assert_eq!(
        tally.root_scans, 0,
        "{name}: {} whole-fact-table scan(s) were taken -- a root-scan discovered work instead of \
         following a named dependency",
        tally.root_scans,
    );
    assert_eq!(
        tally.ignition, EXTERNAL_IGNITIONS,
        "{name}: Ignition fired {} times but only {EXTERNAL_IGNITIONS} external front-door \
         ignitions exist (one submit_code, one submit_root) -- any excess is an internal \
         (mid-job) caller mislabeling its work-start as the external front door",
        tally.ignition,
    );
}

#[test]
fn pull_only_guard_holds_for_quicksort() {
    assert_pull_only(
        "fixtures2/00001_quicksort_plus_foo.fz",
        include_str!("../../fixtures2/00001_quicksort_plus_foo.fz"),
    );
}

#[test]
fn pull_only_guard_holds_for_enum_reduce_operator_ref() {
    assert_pull_only(
        "fixtures2/00181_enum_reduce_operator_ref.fz",
        include_str!("../../fixtures2/00181_enum_reduce_operator_ref.fz"),
    );
}

#[test]
fn pull_only_guard_holds_for_macro_quote_unquote() {
    assert_pull_only(
        "fixtures2/00111_macro_quote_unquote.fz",
        include_str!("../../fixtures2/00111_macro_quote_unquote.fz"),
    );
}

#[test]
fn pull_only_guard_holds_for_nested_call_from_outside_module() {
    assert_pull_only(
        "fixtures2/00059_nested_call_from_outside.fz",
        include_str!("../../fixtures2/00059_nested_call_from_outside.fz"),
    );
}

#[test]
fn pull_only_guard_holds_for_protocol_impl_dispatch() {
    assert_pull_only(
        "fixtures2/00272_protocol_impl_dispatch.fz",
        include_str!("../../fixtures2/00272_protocol_impl_dispatch.fz"),
    );
}
