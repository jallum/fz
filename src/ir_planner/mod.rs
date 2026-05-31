//! Flow-sensitive type inference over `fz_ir::Module`.
//!
//! For each `FnIr`, walks blocks to a fixed point producing two views:
//!
//!   * `vars: HashMap<Var, Ty>` — type at each Var's definition site
//!     (or, for block params, the union over all incoming Goto args). This
//!     is what consumers ask when they want "the" type of v.
//!   * `block_envs: HashMap<BlockId, HashMap<Var, Ty>>` — per-block entry
//!     environment with branch-narrowed types. Consumers positioned inside a
//!     specific block read this for the tightest available info (e.g. inside
//!     the truthy branch of an `If`, a `cond` predicate's operand may carry
//!     a narrower type than its definition).
//!
//! Branch narrowing:
//!   * `Term::If(cond, t, e)` inspects the stmt that bound `cond`. Predicate
//!     prims such as `And`, `Or`, `IsEmptyList`, `Eq`, `Neq`, and `TypeTest`
//!     refine the then/else environments with the facts implied by each arm.
//!   * `Stmt::Let(_, ListHead(v))` types the head as `list_element_type(v)`.
//!   * `Stmt::Let(_, ListTail(v))` types the tail as the list shape itself
//!     (possibly empty -> list_of(elem) ∪ nil; we union with nil).
//!   * `Stmt::Let(_, TupleField(v, i))` uses `tuple_projections` over the
//!     max arity tuple shape in env[v].
//!   * `Stmt::Let(_, MapGet(m, k))` uses `map_field_lookup` when `k` is a
//!     singleton literal.

pub mod closures;
pub mod diagnostics;
pub(crate) mod effects;
pub(crate) mod expr_types;
pub mod fn_types;
pub(crate) mod narrow;
pub mod pretty;
pub(crate) mod prim;
pub mod purity;
pub mod reachable;
pub(crate) mod return_context;
pub(crate) mod scc;
pub(crate) mod spec_witness;
pub mod switch_dispatch;
pub mod type_fn;
pub(crate) mod walk;
pub mod worklist;

#[cfg(test)]
pub(crate) use closures::resolve_closure_return;
pub use closures::rewrite_known_target_closures;
#[cfg(test)]
pub(crate) use diagnostics::check_matcher_purity;
pub use diagnostics::collect_diagnostics;
#[cfg(test)]
pub(crate) use fn_types::PLAN_MODULE_CALLS;
pub use fn_types::{ModulePlan, SpecPlan};
#[cfg(test)]
pub(crate) use narrow::narrow_for_cond;
pub(crate) use narrow::{find_emptied_var, narrow_for_if};
pub use pretty::pretty_module_plan;
pub use reachable::reachable_specs;
#[cfg(test)]
pub(crate) use reachable::{cont_input_key, cont_slot0_descr};
pub use switch_dispatch::rewrite_closed_union_protocol_dispatch;
#[cfg(test)]
pub(crate) use type_fn::type_fn;
pub use worklist::{plan_callable_capabilities, plan_module, plan_module_with_role};

// ----------------------------------------------------------------------
// Tests
// ----------------------------------------------------------------------

#[cfg(test)]
mod tests;
