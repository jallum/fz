//! Planner for executable specialization facts over `fz_ir::Module`.
//!
//! The planner's mission is to turn a settled CPS module plus activation-level
//! type facts into one authoritative execution plan. `type_infer` owns value
//! flow and activation return convergence. The planner consumes those solved
//! facts; it does not run a second return-type engine.
//!
//! `plan_module` produces a `ModulePlan`: the reachable specialization map,
//! per-specialization `SpecPlan`s, selected call edges, return-demand
//! contracts, effective returns projected from activation facts, callable
//! capabilities, effect summaries, precedence, and dead-branch facts.
//! `materialize_program` then projects that plan into executable
//! `PlannedBody`s and stable `SpecId` registration for codegen.
//!
//! A `SpecPlan` describes one executable specialization. It records local Var
//! types and block-entry environments, but those are planner facts for that
//! specialization, not a separate interprocedural type authority. It also owns
//! the dispatch facts codegen needs: local or provider-boundary call targets,
//! continuation targets, closure-call targets, and the return strategy required
//! by the caller's result context.
//!
//! The planner works data-model first:
//!
//!   * Discover specs from entry seeds and selected executable edges: direct
//!     calls, closure calls, continuations, callable boundaries, receive
//!     outcomes, and return-demand variants.
//!   * Type each discovered body locally from its `SpecKey` input and carry
//!     branch-narrowed environments for later facts.
//!   * Select call-edge and return-contract facts from the caller spec's local
//!     environment plus solved activation returns.
//!   * Revisit a spec only when those planner-owned graph facts can change.
//!   * Publish a closed `ModulePlan`; downstream passes consume it instead of
//!     rediscovering reachability, dispatch, return shape, or type flow.
//!
//! Codegen lowers the planned program mechanically. If codegen needs to decide
//! whether a branch, call target, continuation, or return lane is live, the
//! planner has failed to put the fact in the model.

pub mod closures;
pub mod diagnostics;
pub(crate) mod effects;
pub(crate) mod expr_types;
pub mod fn_types;
pub(crate) mod inventory;
pub(crate) mod narrow;
pub(crate) mod planned;
pub mod pretty;
pub(crate) mod prim;
pub mod purity;
pub mod reachable;
pub(crate) mod return_context;
pub(crate) mod scc;
pub mod switch_dispatch;
pub mod type_fn;
pub(crate) mod walk;
pub mod worklist;

pub use closures::rewrite_known_target_closures;
pub use diagnostics::collect_diagnostics;
pub use fn_types::{ModulePlan, SpecPlan};
pub(crate) use narrow::{find_emptied_var, narrow_for_if};
pub(crate) use planned::materialize_program;
pub use pretty::pretty_module_plan;
pub use reachable::reachable_spec_ids;
pub use switch_dispatch::rewrite_closed_union_protocol_dispatch;
pub use worklist::{plan_callable_capabilities, plan_module};

// ----------------------------------------------------------------------
// Tests
// ----------------------------------------------------------------------

#[cfg(test)]
mod tests;
