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
//! Branch narrowing (fz-ul4.11.24.3):
//!   * `Term::If(cond, t, e)` inspects the stmt that bound `cond`. If it was
//!     `IsEmptyList(v)`, the truthy branch refines `v` to `nil`; the falsy
//!     branch keeps the list shape. If it was `BinOp::Eq(a, b)` and either
//!     operand is a singleton literal, the truthy branch intersects the other
//!     operand with that singleton.
//!   * `Stmt::Let(_, ListHead(v))` types the head as `list_element_type(v)`.
//!   * `Stmt::Let(_, ListTail(v))` types the tail as the list shape itself
//!     (possibly empty -> list_of(elem) ∪ nil; we union with nil).
//!   * `Stmt::Let(_, TupleField(v, i))` uses `tuple_projections` over the
//!     max arity tuple shape in env[v].
//!   * `Stmt::Let(_, MapGet(m, k))` uses `map_field_lookup` when `k` is a
//!     singleton literal.
//!
//! Consumers are still not wired (.11.24.4-.7). The pipeline hook at
//! `ir_codegen::compile()` continues to populate `CompiledModule.types`.

pub(crate) mod scc;
pub mod fn_types;
pub mod worklist;
pub(crate) mod walk;
pub mod type_fn;
pub(crate) mod prim;
pub(crate) mod expr_types;
pub(crate) mod narrow;
pub mod closures;
pub mod diagnostics;
pub mod purity;
pub mod reachable;
pub mod pretty;

pub use closures::{resolve_closure_return, rewrite_known_target_closures};
pub use diagnostics::{check_matcher_purity, collect_diagnostics};
pub use fn_types::{
    EmitterSite, FnTypes, ModuleTypes, TYPE_FN_CALLS, TYPE_MODULE_CALLS, WALK_CALLS,
    WORKLIST_POPS,
};
pub(crate) use fn_types::{
    CallsiteFnConsts, EmitsByCaller, EmitterSiteSet, HoldersMap, ProducesMap, ReturnReaders,
    SpecKey, SpecKeySet,
};
pub(crate) use narrow::{find_emptied_var, narrow_for_if};
pub use pretty::pretty_module_types;
pub use purity::{
    ImpureError, ImpureKind, ImpureTerm, check_pure_codegen, check_pure_term, prim_is_pure,
};
pub use reachable::{cont_input_key, cont_slot0_descr, reachable_specs};
pub use type_fn::type_fn;
pub use worklist::type_module;

// ----------------------------------------------------------------------
// Tests
// ----------------------------------------------------------------------

#[cfg(test)]
#[path = "../ir_typer_tests.rs"]
mod tests;
