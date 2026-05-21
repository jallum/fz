//! types-seam.1 — API seam over the concrete `Descr` implementation.
//!
//! Today every type-system consumer touches `Descr` directly. To enable
//! future representation changes (interning, BDDs, bounded polymorphism)
//! without rippling through every consumer at once, this module installs
//! the `Types` trait — a single object that owns every construction,
//! query, and decision about types — and `Ty`, an opaque handle.
//!
//! Day-one is pure wrapping: `Ty(Arc<Descr>)`, and `ConcreteTypes`
//! delegates each method to existing `Descr` impls. Later passes thread
//! `T: Types` to consumers and migrate the representation behind `Ty`.
//!
//! Parent epic: fz-mm2 (inch-worm strategy — every sub-ticket points back
//! so the plan survives compaction).

// types-seam.1 ships the API surface; consumers are migrated by .2+.
// Dead-code warnings on this module are expected until that work lands.
#![allow(dead_code)]

use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

use crate::concrete_types::{Component, Descr, LiteralSet};
use crate::type_vocab::{MapKey, TypeVarId};

/// Opaque handle to a type. Inner representation is private and is
/// expected to change (interned id, BDD root, ...) without consumer
/// impact. Consumers must go through `Types` for every operation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Ty(Arc<Descr>);

impl Ty {
    pub(crate) fn from_descr(d: Descr) -> Self {
        Ty(Arc::new(d))
    }

    pub(crate) fn any() -> Self {
        Ty::from_descr(Descr::any())
    }

    pub(crate) fn none() -> Self {
        Ty::from_descr(Descr::none())
    }

    pub(crate) fn any_vec(n: usize) -> Vec<Self> {
        vec![Ty::any(); n]
    }

    pub(crate) fn descr(&self) -> &Descr {
        &self.0
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.descr())
    }
}

/// Dominant single-axis classification of a `Ty`. `Mixed` indicates the
/// type spans multiple axes (e.g. `int | atom`) or is a compound kind
/// (tuple/list/arrow/map) we don't yet distinguish here. Consumers
/// wanting a yes/no answer should use the `is_*` predicate helpers
/// rather than matching on `Kind` directly — those helpers are stable
/// across future refinements of this enum.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Kind {
    Empty,
    Top,
    Nil,
    Bool,
    Int,
    Float,
    Atom,
    Mixed,
}

/// Substitution map for `instantiate`: every `Var(id)` occurrence in the
/// input `Ty` is replaced by `sigma[id]`.
pub type Sigma<T> = HashMap<TypeVarId, T>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallableClause<T> {
    pub args: Vec<T>,
    pub ret: T,
    pub closure: Option<(crate::fz_ir::FnId, Vec<T>)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpaqueVisibilityError {
    pub opaque: String,
    pub owner_module: String,
    pub using_module: String,
}

impl std::fmt::Display for OpaqueVisibilityError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "field of opaque type `{}` is not accessible from module `{}` \
             (declared in module `{}`)",
            self.opaque, self.using_module, self.owner_module,
        )
    }
}

pub(crate) fn check_brand_mint_visibility<T: Types>(
    _t: &mut T,
    brand_tag: &str,
    using_module: &str,
) -> Result<(), OpaqueVisibilityError> {
    let Some(owner) = crate::type_expr::opaque_owner_module(brand_tag) else {
        return Ok(());
    };
    if owner == using_module {
        Ok(())
    } else {
        Err(OpaqueVisibilityError {
            opaque: brand_tag.to_string(),
            owner_module: owner.to_string(),
            using_module: using_module.to_string(),
        })
    }
}

/// The type universe — owner of every type-system query.
///
/// Methods that may need to materialize new types take `&mut self`;
/// pure queries take `&self`. Future implementations (interning,
/// memoization) populate state on construction calls and read it on
/// queries.
pub trait Types {
    type Ty: Clone + Eq + std::hash::Hash;

    // ---- constructors --------------------------------------------------

    fn any(&mut self) -> Self::Ty;
    fn none(&mut self) -> Self::Ty;
    fn nil(&mut self) -> Self::Ty;
    fn bool(&mut self) -> Self::Ty;
    fn bool_lit(&mut self, b: bool) -> Self::Ty;
    fn int(&mut self) -> Self::Ty;
    fn int_lit(&mut self, n: i64) -> Self::Ty;
    fn float(&mut self) -> Self::Ty;
    fn float_lit(&mut self, f: f64) -> Self::Ty;
    fn atom(&mut self) -> Self::Ty;
    fn atom_lit(&mut self, name: &str) -> Self::Ty;
    fn type_var(&mut self, id: TypeVarId) -> Self::Ty;
    fn arrow(&mut self, args: &[Self::Ty], ret: Self::Ty) -> Self::Ty;
    fn tuple(&mut self, elems: &[Self::Ty]) -> Self::Ty;
    fn list(&mut self, elem: Self::Ty) -> Self::Ty;
    fn map(&mut self, fields: &[(MapKey, Self::Ty)]) -> Self::Ty;
    fn vec_i64(&mut self) -> Self::Ty;
    fn vec_f64(&mut self) -> Self::Ty;
    fn vec_u8(&mut self) -> Self::Ty;
    fn vec_bit(&mut self) -> Self::Ty;
    fn str_t(&mut self) -> Self::Ty;
    fn map_top(&mut self) -> Self::Ty;
    fn closure_lit(
        &mut self,
        fn_id: crate::fz_ir::FnId,
        captures: Vec<Self::Ty>,
        n_args: usize,
    ) -> Self::Ty;

    /// fz-axu (K3) — brand-mint. Overlay brand tag `name` on inner's
    /// structural type. Result carries both the brand label (for nominal
    /// identity / visibility) and the underlying axes.
    fn mint_brand(&mut self, inner: Self::Ty, name: &str) -> Self::Ty;

    /// Nominal opaque type tagged `name`. Two opaques with different
    /// `name`s are lattice-disjoint (this is the rule used by the
    /// @type alias resolver for `opaque T` declarations).
    fn opaque_of(&mut self, name: &str) -> Self::Ty;

    /// Nominal brand tagged `name`, with no inner structural overlay.
    /// Distinct from `mint_brand` (which carries the inner type along
    /// with the brand label).
    fn brand_of(&mut self, name: &str) -> Self::Ty;

    /// Project `a`'s list-axis element type. Returns `any` if `a` has
    /// no list axis or the list axis is unconstrained.
    fn list_element_type(&mut self, a: &Self::Ty) -> Self::Ty;

    /// Project `a`'s tuple-axis components at `arity`. Returns a vector
    /// of length `arity`; positions with no matching shape default to
    /// `any`.
    fn tuple_projections(&mut self, a: &Self::Ty, arity: usize) -> Vec<Self::Ty>;

    /// The widest arity present in `a`'s tuple-axis clauses, or 0 if
    /// `a` has no tuple axis.
    fn max_tuple_arity(&self, a: &Self::Ty) -> usize;

    /// Refine `a`'s map-axis by overlaying `(key, v)`. Used by
    /// MapUpdate to type the result of `m | { k => v }`.
    fn refine_map_field(&mut self, a: &Self::Ty, key: &MapKey, v: &Self::Ty) -> Self::Ty;

    /// Look up `key` in `a`'s map axis, returning the field's type
    /// if statically known.
    fn map_field_lookup(&mut self, a: &Self::Ty, key: &MapKey) -> Option<Self::Ty>;

    /// fz-rh5.6 — widen `a` for use as a recursive-call spec key.
    /// Idempotent, monotone, height-bounded; the worklist's termination
    /// proof depends on `widen` collapsing nested structural depth after
    /// `WIDEN_AT` visits.
    fn widen(&mut self, a: &Self::Ty) -> Self::Ty;

    // ---- lattice ops ---------------------------------------------------

    fn union(&mut self, a: Self::Ty, b: Self::Ty) -> Self::Ty;
    fn intersect(&mut self, a: Self::Ty, b: Self::Ty) -> Self::Ty;
    fn complement(&mut self, a: Self::Ty) -> Self::Ty;
    fn difference(&mut self, a: Self::Ty, b: Self::Ty) -> Self::Ty;

    // ---- predicates ----------------------------------------------------

    fn is_empty(&self, a: &Self::Ty) -> bool;
    fn is_top(&self, a: &Self::Ty) -> bool;
    fn is_subtype(&self, a: &Self::Ty, b: &Self::Ty) -> bool;
    fn is_disjoint(&self, a: &Self::Ty, b: &Self::Ty) -> bool;
    fn is_equivalent(&self, a: &Self::Ty, b: &Self::Ty) -> bool;

    /// Count top-level named type vars across a spec key. Used by
    /// most-specific-wins dispatch ordering: fewer vars = more concrete.
    fn key_var_count(&self, key: &[Self::Ty]) -> usize;

    /// Query-key subsumption with positional type-var binding for spec lookup.
    fn key_subsumes_with(
        &self,
        query: &Self::Ty,
        key: &Self::Ty,
        sigma: &mut Sigma<Self::Ty>,
    ) -> bool;

    // ---- introspection -------------------------------------------------

    fn kind_of(&self, a: &Self::Ty) -> Kind;

    /// Coarser than `is_disjoint`: true iff `a` and `b` share at least
    /// one populated axis (basic kind, atoms, ints, floats, tuples,
    /// lists, arrows, maps, opaques, brands, vars). Used by lints that
    /// want to flag cross-kind comparisons (`x == :ok` when `x: int`)
    /// without firing on within-axis literal-disjoint cases (`1 == 2`).
    fn kinds_overlap(&self, a: &Self::Ty, b: &Self::Ty) -> bool;

    /// If `a` is a pure opaque-nominal type — a singleton on the
    /// `opaques` axis with every other axis empty — return the opaque
    /// tag name. Otherwise None. Used by lints that need to know
    /// "is this value an opaque, and which one?" (opaque-arithmetic
    /// rejection, opaque-visibility checks).
    fn opaque_singleton(&self, a: &Self::Ty) -> Option<String>;

    /// If `a` is a single brand mint with no other axes — i.e. a single
    /// element on the `brands` axis with every other axis empty —
    /// return the brand tag name. Otherwise None. Mirrors
    /// `opaque_singleton` for the brand axis.
    fn brand_singleton(&self, a: &Self::Ty) -> Option<String>;

    /// Check whether `a` (treated as an opaque-nominal type) is
    /// visible from `using_module`. If `a` is not a pure opaque, or is
    /// a built-in opaque with no owner module, the check trivially
    /// succeeds.
    fn check_opaque_visibility(
        &self,
        a: &Self::Ty,
        using_module: &str,
    ) -> Result<(), OpaqueVisibilityError>;

    /// True iff `a` is a singleton-literal value — a single int_lit,
    /// float_lit, atom_lit, etc. Used by if-condition narrowing on
    /// equality predicates to refine the non-singleton operand.
    fn is_singleton_lit(&self, a: &Self::Ty) -> bool;

    /// If `a` is a singleton integer literal, return its value.
    /// Used by binop folding (numeric_result_fold, compare_result).
    fn as_int_singleton(&self, a: &Self::Ty) -> Option<i64>;

    /// If `a` is a singleton float literal, return its value.
    fn as_float_singleton(&self, a: &Self::Ty) -> Option<f64>;

    /// Structural depth of `a` under the current representation.
    fn depth(&self, a: &Self::Ty) -> usize;

    /// If `a` is a singleton atom literal, return its name.
    fn as_atom_singleton(&self, a: &Self::Ty) -> Option<String>;

    /// If `a` is a singleton closure literal, return the callee fn id
    /// and captured literal values.
    fn closure_lit_parts(&self, a: &Self::Ty) -> Option<(crate::fz_ir::FnId, Vec<Self::Ty>)>;

    /// If `a` has only pure positive callable clauses, return each
    /// clause's argument pattern, return type, and optional closure-literal
    /// target metadata. `None` means the callable shape is absent or too
    /// broad to drive closure-return narrowing.
    fn callable_clauses(&mut self, a: &Self::Ty) -> Option<Vec<CallableClause<Self::Ty>>>;

    /// If `a` is a literal tuple, return its elements in order.
    fn tuple_lit_elems(&self, a: &Self::Ty) -> Option<Vec<Self::Ty>>;

    /// If `a` is a singleton literal suitable as a map key, return it.
    fn as_map_key(&self, a: &Self::Ty) -> Option<MapKey> {
        self.as_atom_singleton(a)
            .map(MapKey::Atom)
            .or_else(|| self.as_int_singleton(a).map(MapKey::Int))
    }

    /// Migration bridge: query a concrete seam `Ty` for map-key shape.
    fn concrete_as_map_key(&self, a: &Ty) -> Option<MapKey> {
        a.descr().as_map_key()
    }

    /// Migration bridge: check whether a concrete seam `Ty` is a closure lit
    /// and recover its fn id plus captured values.
    fn concrete_closure_lit_parts(&self, a: &Ty) -> Option<(crate::fz_ir::FnId, Vec<Ty>)> {
        let lit = a.descr().as_closure_lit()?;
        Some((lit.fn_id, lit.captures.clone()))
    }

    /// Concrete helper: join the return side of a concrete seam callable.
    fn concrete_arrow_join_return(&mut self, a: &Ty) -> Ty {
        Ty::from_descr(a.descr().arrow_join_return())
    }

    /// Exact match for the empty-list literal: `list_of(none())`.
    fn is_empty_list_lit(&self, a: &Self::Ty) -> bool;

    /// Render `a` for user-facing diagnostics. Owned-string return
    /// day-one; consumers `format!("{}", t.display(&ty))`-style.
    fn display(&self, a: &Self::Ty) -> String;

    /// Length-bounded rendering for diagnostic notes. Caps each
    /// literal-set axis at a small fixed count so a huge union
    /// (`int_lit(1) | ... | int_lit(N)`) doesn't crowd a `= note:`
    /// line. Distinct from `display()`, which is exact (used by
    /// golden tests).
    fn display_for_diag(&self, a: &Self::Ty) -> String;

    // ---- substitution --------------------------------------------------

    fn instantiate(&mut self, a: &Self::Ty, sigma: &Sigma<Self::Ty>) -> Self::Ty;
    fn collect_instantiation_subst(
        &mut self,
        pattern: &Self::Ty,
        witness: &Self::Ty,
        sigma: &mut Sigma<Self::Ty>,
    );

    // ---- adoption-ease predicates (default; built on kind_of) ---------

    fn is_integer(&self, a: &Self::Ty) -> bool {
        matches!(self.kind_of(a), Kind::Int)
    }
    fn is_floating(&self, a: &Self::Ty) -> bool {
        matches!(self.kind_of(a), Kind::Float)
    }
    fn is_nil(&self, a: &Self::Ty) -> bool {
        matches!(self.kind_of(a), Kind::Nil)
    }
    fn is_bool(&self, a: &Self::Ty) -> bool {
        matches!(self.kind_of(a), Kind::Bool)
    }
    /// True when `a`'s classification is purely atom-shaped — atom, bool,
    /// or nil. Useful when a consumer wants "is this any kind of atom?"
    /// rather than the narrower `is_nil` / `is_bool`.
    fn is_atom_type(&self, a: &Self::Ty) -> bool {
        matches!(self.kind_of(a), Kind::Atom | Kind::Bool | Kind::Nil)
    }

    /// If `a` is a single bool literal (`true` or `false`), return it.
    /// Default reuses `as_atom_singleton`; future implementations may
    /// override with a more direct check.
    fn as_bool_lit(&self, a: &Self::Ty) -> Option<bool> {
        match self.as_atom_singleton(a).as_deref() {
            Some("true") => Some(true),
            Some("false") => Some(false),
            _ => None,
        }
    }

    /// True iff `a` uniquely determines a single runtime value — a
    /// singleton scalar, `nil`, or a tuple/closure whose every part is
    /// itself literal. Used by the reducer to decide whether a fold's
    /// inputs are fully known.
    fn is_literal(&self, a: &Self::Ty) -> bool {
        self.is_singleton_lit(a)
            || self.is_nil(a)
            || self
                .tuple_lit_elems(a)
                .is_some_and(|elems| elems.iter().all(|elem| self.is_literal(elem)))
            || self.closure_lit_parts(a).is_some_and(|(_, captures)| {
                captures.iter().all(|capture| self.is_literal(capture))
            })
    }

    /// True iff `a` mentions any free type variable (`Descr::var(_)`).
    /// Used by the typer to decide whether substitution is required.
    fn has_vars(&self, a: &Self::Ty) -> bool;
}

/// Day-one implementation: thin wrapper around `Descr`. Zero fields —
/// it's an oracle, not a store. Future implementations will hold
/// interning tables, memo caches, or BDD nodes.
#[derive(Debug)]
pub struct ConcreteTypes;

impl Types for ConcreteTypes {
    type Ty = Ty;

    fn any(&mut self) -> Ty {
        Ty::from_descr(Descr::any())
    }
    fn none(&mut self) -> Ty {
        Ty::from_descr(Descr::none())
    }
    fn nil(&mut self) -> Ty {
        Ty::from_descr(Descr::nil())
    }
    fn bool(&mut self) -> Ty {
        Ty::from_descr(Descr::bool_t())
    }
    fn bool_lit(&mut self, b: bool) -> Ty {
        Ty::from_descr(Descr::atom_lit(if b { "true" } else { "false" }))
    }
    fn int(&mut self) -> Ty {
        Ty::from_descr(Descr::int())
    }
    fn int_lit(&mut self, n: i64) -> Ty {
        Ty::from_descr(Descr::int_lit(n))
    }
    fn float(&mut self) -> Ty {
        Ty::from_descr(Descr::float())
    }
    fn float_lit(&mut self, f: f64) -> Ty {
        Ty::from_descr(Descr::float_lit(f))
    }
    fn atom(&mut self) -> Ty {
        Ty::from_descr(Descr::atom_top())
    }
    fn atom_lit(&mut self, name: &str) -> Ty {
        Ty::from_descr(Descr::atom_lit(name))
    }
    fn type_var(&mut self, id: TypeVarId) -> Ty {
        Ty::from_descr(Descr::var(id))
    }
    fn arrow(&mut self, args: &[Ty], ret: Ty) -> Ty {
        let args: Vec<Descr> = args.iter().map(|t| t.descr().clone()).collect();
        Ty::from_descr(Descr::arrow(args, ret.descr().clone()))
    }
    fn tuple(&mut self, elems: &[Ty]) -> Ty {
        let elems: Vec<Descr> = elems.iter().map(|t| t.descr().clone()).collect();
        Ty::from_descr(Descr::tuple_of(elems))
    }
    fn list(&mut self, elem: Ty) -> Ty {
        Ty::from_descr(Descr::list_of(elem.descr().clone()))
    }
    fn map(&mut self, fields: &[(MapKey, Ty)]) -> Ty {
        let fields: Vec<(MapKey, Descr)> = fields
            .iter()
            .map(|(k, t)| (k.clone(), t.descr().clone()))
            .collect();
        Ty::from_descr(Descr::map_of(fields))
    }
    fn vec_i64(&mut self) -> Ty {
        Ty::from_descr(Descr::vec_i64())
    }
    fn vec_f64(&mut self) -> Ty {
        Ty::from_descr(Descr::vec_f64())
    }
    fn vec_u8(&mut self) -> Ty {
        Ty::from_descr(Descr::vec_u8())
    }
    fn vec_bit(&mut self) -> Ty {
        Ty::from_descr(Descr::vec_bit())
    }
    fn str_t(&mut self) -> Ty {
        Ty::from_descr(Descr::str_t())
    }
    fn map_top(&mut self) -> Ty {
        Ty::from_descr(Descr::map_top())
    }
    fn closure_lit(&mut self, fn_id: crate::fz_ir::FnId, captures: Vec<Ty>, n_args: usize) -> Ty {
        let capture_descrs: Vec<Descr> = captures.into_iter().map(|c| c.descr().clone()).collect();
        Ty::from_descr(Descr::closure_lit(fn_id, capture_descrs, n_args))
    }
    fn mint_brand(&mut self, inner: Ty, name: &str) -> Ty {
        let mut d = inner.descr().clone();
        d.brands = LiteralSet::lit(name.to_string());
        Ty::from_descr(d)
    }
    fn opaque_of(&mut self, name: &str) -> Ty {
        Ty::from_descr(Descr::opaque_of(name))
    }
    fn brand_of(&mut self, name: &str) -> Ty {
        Ty::from_descr(Descr::brand_of(name))
    }

    fn list_element_type(&mut self, a: &Ty) -> Ty {
        concrete_list_element_type(a)
    }

    fn tuple_projections(&mut self, a: &Ty, arity: usize) -> Vec<Ty> {
        concrete_tuple_projections(a, arity)
    }

    fn max_tuple_arity(&self, a: &Ty) -> usize {
        a.descr().max_tuple_arity()
    }

    fn refine_map_field(&mut self, a: &Ty, key: &MapKey, v: &Ty) -> Ty {
        concrete_refine_map_field(a, key, v)
    }

    fn map_field_lookup(&mut self, a: &Ty, key: &MapKey) -> Option<Ty> {
        concrete_map_field_lookup(a, key)
    }

    fn widen(&mut self, a: &Ty) -> Ty {
        Ty::from_descr(a.descr().widen())
    }

    fn union(&mut self, a: Ty, b: Ty) -> Ty {
        Ty::from_descr(a.descr().union(b.descr()))
    }
    fn intersect(&mut self, a: Ty, b: Ty) -> Ty {
        Ty::from_descr(a.descr().intersect(b.descr()))
    }
    fn complement(&mut self, a: Ty) -> Ty {
        Ty::from_descr(a.descr().neg())
    }
    fn difference(&mut self, a: Ty, b: Ty) -> Ty {
        Ty::from_descr(a.descr().diff(b.descr()))
    }

    fn is_empty(&self, a: &Ty) -> bool {
        a.descr().is_empty()
    }
    fn is_top(&self, a: &Ty) -> bool {
        a.descr().is_equiv(&Descr::any())
    }
    fn is_subtype(&self, a: &Ty, b: &Ty) -> bool {
        a.descr().is_subtype(b.descr())
    }
    fn is_disjoint(&self, a: &Ty, b: &Ty) -> bool {
        a.descr().intersect(b.descr()).is_empty()
    }
    fn is_equivalent(&self, a: &Ty, b: &Ty) -> bool {
        a.descr().is_equiv(b.descr())
    }

    fn key_var_count(&self, key: &[Ty]) -> usize {
        key.iter()
            .map(|t| {
                t.descr()
                    .components()
                    .filter_map(|c| match c {
                        Component::Vars(v) => v.finite_len(),
                        _ => None,
                    })
                    .sum::<usize>()
            })
            .sum()
    }

    fn key_subsumes_with(&self, query: &Ty, key: &Ty, sigma: &mut Sigma<Ty>) -> bool {
        fn pure_var_ids(d: &Descr) -> Option<Vec<TypeVarId>> {
            let mut comps = d.components();
            let only = comps.next()?;
            if comps.next().is_some() {
                return None;
            }
            match only {
                Component::Vars(view) => {
                    let finite: Vec<TypeVarId> = view.finite()?.collect();
                    if finite.is_empty() {
                        None
                    } else {
                        Some(finite)
                    }
                }
                _ => None,
            }
        }

        let qd = query.descr();
        let kd = key.descr();
        if kd.looks_full() {
            return true;
        }
        if let Some(alphas) = pure_var_ids(kd) {
            for alpha in alphas {
                match sigma.get(&alpha) {
                    None => {
                        sigma.insert(alpha, query.clone());
                    }
                    Some(existing) => {
                        if !existing.descr().is_equiv(qd) {
                            return false;
                        }
                    }
                }
            }
            return true;
        }
        qd.is_subtype(kd)
    }

    fn kind_of(&self, a: &Ty) -> Kind {
        descr_kind(a.descr())
    }

    fn kinds_overlap(&self, a: &Ty, b: &Ty) -> bool {
        a.descr().kinds_overlap(b.descr())
    }

    fn opaque_singleton(&self, a: &Ty) -> Option<String> {
        a.descr().as_opaque_singleton().map(String::from)
    }

    fn brand_singleton(&self, a: &Ty) -> Option<String> {
        a.descr().as_brand_singleton().map(String::from)
    }

    fn check_opaque_visibility(
        &self,
        a: &Ty,
        using_module: &str,
    ) -> Result<(), OpaqueVisibilityError> {
        let Some(tag) = a.descr().as_opaque_singleton() else {
            return Ok(());
        };
        let Some(owner) = crate::type_expr::opaque_owner_module(tag) else {
            return Ok(());
        };
        if owner == using_module {
            Ok(())
        } else {
            Err(OpaqueVisibilityError {
                opaque: tag.to_string(),
                owner_module: owner.to_string(),
                using_module: using_module.to_string(),
            })
        }
    }

    fn is_singleton_lit(&self, a: &Ty) -> bool {
        a.descr().is_singleton_literal()
    }

    fn as_int_singleton(&self, a: &Ty) -> Option<i64> {
        a.descr().as_int_singleton()
    }

    fn as_float_singleton(&self, a: &Ty) -> Option<f64> {
        a.descr().as_float_singleton().map(|b| b.get())
    }

    fn depth(&self, a: &Ty) -> usize {
        a.descr().depth()
    }

    fn as_atom_singleton(&self, a: &Ty) -> Option<String> {
        a.descr().as_atom_singleton().map(String::from)
    }

    fn closure_lit_parts(&self, a: &Ty) -> Option<(crate::fz_ir::FnId, Vec<Ty>)> {
        let lit = a.descr().as_closure_lit()?;
        Some((lit.fn_id, lit.captures.clone()))
    }

    fn callable_clauses(&mut self, a: &Ty) -> Option<Vec<CallableClause<Ty>>> {
        let funcs_view = a.descr().components().find_map(|c| match c {
            Component::Funcs(v) => Some(v),
            _ => None,
        })?;
        if funcs_view.has_negations() || !funcs_view.all_clauses_have_pos() {
            return None;
        }
        Some(
            funcs_view
                .arrows()
                .map(|arrow| CallableClause {
                    args: arrow.args().iter().cloned().map(Ty::from_descr).collect(),
                    ret: Ty::from_descr(arrow.ret().clone()),
                    closure: arrow
                        .closure_lit()
                        .map(|lit| (lit.fn_id, lit.captures.clone())),
                })
                .collect(),
        )
    }

    fn tuple_lit_elems(&self, a: &Ty) -> Option<Vec<Ty>> {
        concrete_tuple_lit_elems(a)
    }

    fn is_empty_list_lit(&self, a: &Ty) -> bool {
        a.descr().is_equiv(&Descr::list_of(Descr::none()))
    }

    fn display(&self, a: &Ty) -> String {
        format!("{}", a.descr())
    }

    fn display_for_diag(&self, a: &Ty) -> String {
        a.descr().display_for_diag()
    }

    fn has_vars(&self, a: &Ty) -> bool {
        a.descr().has_vars()
    }

    fn instantiate(&mut self, a: &Ty, sigma: &Sigma<Ty>) -> Ty {
        let inner: HashMap<TypeVarId, Descr> = sigma
            .iter()
            .map(|(id, t)| (*id, t.descr().clone()))
            .collect();
        Ty::from_descr(a.descr().instantiate(&inner))
    }

    fn collect_instantiation_subst(&mut self, pattern: &Ty, witness: &Ty, sigma: &mut Sigma<Ty>) {
        let mut inner: HashMap<TypeVarId, Descr> = sigma
            .iter()
            .map(|(id, t)| (*id, t.descr().clone()))
            .collect();
        Descr::collect_subst_into(pattern.descr(), witness.descr(), &mut inner);
        *sigma = inner
            .into_iter()
            .map(|(id, d)| (id, Ty::from_descr(d)))
            .collect();
    }
}

/// Day-one single-axis classifier. Order matters: nil and bool are
/// subtypes of atom_top, so they're tested first; otherwise an
/// `atom_lit("nil")` would classify as `Atom`. Compound axes
/// (tuple/list/arrow/map) collapse to `Mixed` for now — refining them
/// is a follow-up once a consumer needs the distinction.
fn descr_kind(d: &Descr) -> Kind {
    if d.is_empty() {
        return Kind::Empty;
    }
    if d.is_equiv(&Descr::any()) {
        return Kind::Top;
    }
    if d.is_subtype(&Descr::nil()) {
        return Kind::Nil;
    }
    if d.is_subtype(&Descr::bool_t()) {
        return Kind::Bool;
    }
    if d.is_subtype(&Descr::int()) {
        return Kind::Int;
    }
    if d.is_subtype(&Descr::float()) {
        return Kind::Float;
    }
    if d.is_subtype(&Descr::atom_top()) {
        return Kind::Atom;
    }
    Kind::Mixed
}

fn concrete_list_element_type(a: &Ty) -> Ty {
    for component in a.descr().components() {
        if let Component::Lists(view) = component {
            return Ty::from_descr(view.element_type());
        }
    }
    Ty::any()
}

fn concrete_tuple_projections(a: &Ty, arity: usize) -> Vec<Ty> {
    for component in a.descr().components() {
        if let Component::Tuples(view) = component
            && let Some(comps) = view.project_all(arity)
        {
            return comps.into_iter().map(Ty::from_descr).collect();
        }
    }
    Ty::any_vec(arity)
}

fn concrete_map_field_lookup(a: &Ty, key: &MapKey) -> Option<Ty> {
    for component in a.descr().components() {
        if let Component::Maps(view) = component {
            return view.lookup(key).map(Ty::from_descr);
        }
    }
    None
}

fn concrete_refine_map_field(a: &Ty, key: &MapKey, v: &Ty) -> Ty {
    Ty::from_descr(a.descr().refine_map_field(key, v.descr()))
}

fn concrete_tuple_lit_elems(a: &Ty) -> Option<Vec<Ty>> {
    let elems = a.descr().as_tuple_singleton()?;
    let elems: Vec<Ty> = elems.iter().cloned().map(Ty::from_descr).collect();
    elems.iter().all(concrete_is_literal).then_some(elems)
}

fn concrete_is_literal(a: &Ty) -> bool {
    a.descr().is_singleton_literal()
        || a.descr().is_equiv(&Descr::nil())
        || concrete_tuple_lit_elems(a).is_some()
        || a.descr()
            .as_closure_lit()
            .is_some_and(|lit| lit.captures.iter().all(concrete_is_literal))
}

#[cfg(test)]
mod conformance_tests {
    use super::*;

    macro_rules! key_helper_conformance_tests {
        ($mod_name:ident, $ctor:expr) => {
            mod $mod_name {
                use super::*;

                #[test]
                fn key_var_count_counts_top_level_vars() {
                    let mut t = $ctor;
                    let alpha = t.type_var(TypeVarId(0));
                    let beta = t.type_var(TypeVarId(1));
                    let int_top = t.int();
                    let mixed = t.union(int_top, beta);
                    assert_eq!(t.key_var_count(&[alpha, mixed]), 2);
                }

                #[test]
                fn key_subsumes_with_binds_pure_vars() {
                    let mut t = $ctor;
                    let mut sigma = HashMap::new();
                    let int = t.int();
                    let alpha = t.type_var(TypeVarId(0));
                    assert!(t.key_subsumes_with(&int, &alpha, &mut sigma));
                    assert_eq!(sigma.get(&TypeVarId(0)), Some(&int));
                }

                #[test]
                fn key_subsumes_with_leaves_sigma_empty_for_non_pure_var_keys() {
                    let mut t = $ctor;
                    let mut sigma = HashMap::new();
                    let int = t.int();
                    let alpha = t.type_var(TypeVarId(0));
                    let int_top = t.int();
                    let union_key = t.union(int_top, alpha);
                    assert!(t.key_subsumes_with(&int, &union_key, &mut sigma));
                    assert!(sigma.is_empty());
                }
            }
        };
    }

    key_helper_conformance_tests!(concrete_types, ConcreteTypes);

    macro_rules! seam_helper_conformance_tests {
        ($mod_name:ident, $ctor:expr) => {
            mod $mod_name {
                use super::*;

                #[test]
                #[allow(clippy::approx_constant)]
                fn is_literal_recognizes_scalar_singletons() {
                    let mut t = $ctor;
                    let int = t.int_lit(42);
                    let float = t.float_lit(3.14);
                    let atom = t.atom_lit("foo");
                    let nil = t.nil();
                    let tru = t.bool_lit(true);
                    let fls = t.bool_lit(false);
                    assert!(t.is_literal(&int));
                    assert!(t.is_literal(&float));
                    assert!(t.is_literal(&atom));
                    assert!(t.is_literal(&nil));
                    assert!(t.is_literal(&tru));
                    assert!(t.is_literal(&fls));
                }

                #[test]
                fn is_literal_rejects_wide_types() {
                    let mut t = $ctor;
                    let int = t.int();
                    let float = t.float();
                    let any = t.any();
                    let bool_t = t.bool();
                    assert!(!t.is_literal(&int));
                    assert!(!t.is_literal(&float));
                    assert!(!t.is_literal(&any));
                    assert!(!t.is_literal(&bool_t));
                }

                #[test]
                fn is_literal_recognizes_literal_tuple() {
                    let mut t = $ctor;
                    let num = t.atom_lit("num");
                    let value = t.int_lit(42);
                    let tuple = t.tuple(&[num, value]);
                    assert!(t.is_literal(&tuple));
                }

                #[test]
                fn is_literal_rejects_tuple_with_wide_element() {
                    let mut t = $ctor;
                    let num = t.atom_lit("num");
                    let value = t.int();
                    let tuple = t.tuple(&[num, value]);
                    assert!(!t.is_literal(&tuple));
                }

                #[test]
                fn as_bool_lit_recognizes_true_and_false() {
                    let mut t = $ctor;
                    let tru = t.bool_lit(true);
                    let fls = t.bool_lit(false);
                    let wide = t.bool();
                    assert_eq!(t.as_bool_lit(&tru), Some(true));
                    assert_eq!(t.as_bool_lit(&fls), Some(false));
                    assert_eq!(t.as_bool_lit(&wide), None);
                }

                #[test]
                fn as_map_key_recognizes_atom_and_int_singletons() {
                    let mut t = $ctor;
                    let ok = t.atom_lit("ok");
                    let seven = t.int_lit(7);
                    let wide = t.atom();
                    assert!(matches!(
                        t.as_map_key(&ok),
                        Some(MapKey::Atom(name)) if name == "ok"
                    ));
                    assert!(matches!(t.as_map_key(&seven), Some(MapKey::Int(7))));
                    assert!(t.as_map_key(&wide).is_none());
                }

                #[test]
                fn list_element_type_projects_list_axis() {
                    let mut t = $ctor;
                    let elem = t.int();
                    let list = t.list(elem.clone());
                    let projected = t.list_element_type(&list);
                    assert!(t.is_equivalent(&projected, &elem));
                }

                #[test]
                fn list_element_type_defaults_to_any_without_list_axis() {
                    let mut t = $ctor;
                    let int = t.int();
                    let projected = t.list_element_type(&int);
                    assert!(t.is_top(&projected));
                }

                #[test]
                fn tuple_projections_fall_back_to_any() {
                    let mut t = $ctor;
                    let int = t.int();
                    let comps = t.tuple_projections(&int, 2);
                    assert_eq!(comps.len(), 2);
                    assert!(comps.iter().all(|ty| t.is_top(ty)));
                }

                #[test]
                fn tuple_projections_project_tuple_shape() {
                    let mut t = $ctor;
                    let one = t.int_lit(1);
                    let ok = t.atom_lit("ok");
                    let tuple = t.tuple(&[one.clone(), ok.clone()]);
                    let comps = t.tuple_projections(&tuple, 2);
                    assert_eq!(comps, vec![one, ok]);
                }

                #[test]
                fn map_field_lookup_returns_known_field_type() {
                    let mut t = $ctor;
                    let forty_two = t.int_lit(42);
                    let map = t.map(&[(MapKey::Atom("ok".to_string()), forty_two.clone())]);
                    let field = t
                        .map_field_lookup(&map, &MapKey::Atom("ok".to_string()))
                        .expect("known field");
                    assert!(t.is_equivalent(&field, &forty_two));
                }

                #[test]
                fn refine_map_field_overlays_field_type() {
                    let mut t = $ctor;
                    let map = t.map_top();
                    let value = t.int_lit(7);
                    let refined = t.refine_map_field(&map, &MapKey::Atom("n".to_string()), &value);
                    let field = t
                        .map_field_lookup(&refined, &MapKey::Atom("n".to_string()))
                        .expect("refined field");
                    assert!(t.is_subtype(&value, &field));
                    assert!(!t.is_empty(&field));
                }
            }
        };
    }

    seam_helper_conformance_tests!(concrete_types_helpers, ConcreteTypes);
}

// ----------------------------------------------------------------------
// Smoke tests — generic over `T: Types`. Each `smoke_*` fn is a single
// assertion-group; the `impl_smoke_suite!` macro at the bottom registers
// them as named `#[test]` fns per implementation. A new implementation
// joins the harness with one macro invocation.
// ----------------------------------------------------------------------

#[cfg(test)]
mod smoke {
    use super::*;

    pub(super) fn smoke_primitives_distinct<T: Types>(t: &mut T) {
        let i = t.int();
        let f = t.float();
        let a = t.atom();
        assert!(t.is_disjoint(&i, &f), "int vs float must be disjoint");
        assert!(t.is_disjoint(&i, &a), "int vs atom must be disjoint");
        assert!(t.is_disjoint(&f, &a), "float vs atom must be disjoint");
        assert!(!t.is_disjoint(&i, &i), "int must overlap itself");
    }

    pub(super) fn smoke_union_idempotent<T: Types>(t: &mut T) {
        let i = t.int();
        let u = t.union(i.clone(), i.clone());
        assert!(t.is_equivalent(&u, &i));
    }

    pub(super) fn smoke_intersect_idempotent<T: Types>(t: &mut T) {
        let i = t.int();
        let x = t.intersect(i.clone(), i.clone());
        assert!(t.is_equivalent(&x, &i));
    }

    pub(super) fn smoke_complement_involution<T: Types>(t: &mut T) {
        let i = t.int();
        let once = t.complement(i.clone());
        let twice = t.complement(once);
        assert!(t.is_equivalent(&twice, &i));
    }

    pub(super) fn smoke_de_morgan<T: Types>(t: &mut T) {
        let i = t.int();
        let f = t.float();
        let u = t.union(i.clone(), f.clone());
        let lhs = t.complement(u);
        let ni = t.complement(i);
        let nf = t.complement(f);
        let rhs = t.intersect(ni, nf);
        assert!(t.is_equivalent(&lhs, &rhs));
    }

    pub(super) fn smoke_subtype_reflexive<T: Types>(t: &mut T) {
        let i = t.int();
        assert!(t.is_subtype(&i, &i));
    }

    pub(super) fn smoke_int_lit_in_int<T: Types>(t: &mut T) {
        let i = t.int();
        let lit = t.int_lit(42);
        assert!(t.is_subtype(&lit, &i));
        assert!(!t.is_subtype(&i, &lit));
    }

    pub(super) fn smoke_nil_in_atom<T: Types>(t: &mut T) {
        let n = t.nil();
        let a = t.atom();
        assert!(t.is_subtype(&n, &a));
    }

    pub(super) fn smoke_top_bottom<T: Types>(t: &mut T) {
        let top = t.any();
        let bot = t.none();
        assert!(t.is_top(&top));
        assert!(t.is_empty(&bot));
        assert!(!t.is_top(&bot));
        assert!(!t.is_empty(&top));
    }

    pub(super) fn smoke_tuple_element_disjoint<T: Types>(t: &mut T) {
        let i = t.int();
        let a = t.atom();
        let ti = t.tuple(&[i]);
        let ta = t.tuple(&[a]);
        assert!(t.is_disjoint(&ti, &ta));
    }

    pub(super) fn smoke_arrow_contravariance<T: Types>(t: &mut T) {
        // f : (any) -> int  ≤  g : (int) -> int
        // (callable wherever g is, since arg type is wider; same return.)
        let any = t.any();
        let i = t.int();
        let wide = t.arrow(&[any], i.clone());
        let arg = i.clone();
        let narrow = t.arrow(std::slice::from_ref(&arg), i);
        assert!(t.is_subtype(&wide, &narrow));
    }

    pub(super) fn smoke_list_covariance<T: Types>(t: &mut T) {
        // `list` is covariant in its element: list(int_lit(42)) ⊆ list(int).
        // Note: list(int) and list(atom) are NOT disjoint — both contain
        // the empty list `[]` — so we use subtyping, not disjointness.
        let i = t.int();
        let lit = t.int_lit(42);
        let l_lit = t.list(lit);
        let l_int = t.list(i);
        assert!(t.is_subtype(&l_lit, &l_int));
        assert!(t.is_subtype(&l_lit, &l_lit));
    }

    pub(super) fn smoke_kind_classification<T: Types>(t: &mut T) {
        let i = t.int();
        assert_eq!(t.kind_of(&i), Kind::Int);
        let il = t.int_lit(7);
        assert_eq!(t.kind_of(&il), Kind::Int);
        let f = t.float();
        assert_eq!(t.kind_of(&f), Kind::Float);
        let n = t.nil();
        assert_eq!(t.kind_of(&n), Kind::Nil);
        let b = t.bool();
        assert_eq!(t.kind_of(&b), Kind::Bool);
        let al = t.atom_lit("ok");
        assert_eq!(t.kind_of(&al), Kind::Atom);
        let top = t.any();
        assert_eq!(t.kind_of(&top), Kind::Top);
        let bot = t.none();
        assert_eq!(t.kind_of(&bot), Kind::Empty);

        let i2 = t.int();
        let a2 = t.atom();
        let mixed = t.union(i2, a2);
        assert_eq!(t.kind_of(&mixed), Kind::Mixed);

        let one = t.int_lit(1);
        assert!(t.is_integer(&one));
        let f2 = t.float();
        assert!(!t.is_integer(&f2));
        let n2 = t.nil();
        assert!(t.is_atom_type(&n2));
        let b2 = t.bool();
        assert!(t.is_atom_type(&b2));
    }

    pub(super) fn smoke_display_renders<T: Types>(t: &mut T) {
        let i = t.int();
        let s = t.display(&i);
        assert!(!s.is_empty(), "display of int must not be empty");
    }

    /// Register the full smoke suite as named `#[test]` fns against an
    /// implementation. The first arg names the test submodule (visible
    /// in `cargo test` output as `types_seam::smoke::<name>::...`); the
    /// second is an expression that produces a `mut T: Types` (run once
    /// per test, so a fresh instance per case).
    macro_rules! impl_smoke_suite {
        ($impl_name:ident, $ctor:expr) => {
            mod $impl_name {
                use super::*;
                #[test]
                fn primitives_distinct() {
                    smoke_primitives_distinct(&mut $ctor);
                }
                #[test]
                fn union_idempotent() {
                    smoke_union_idempotent(&mut $ctor);
                }
                #[test]
                fn intersect_idempotent() {
                    smoke_intersect_idempotent(&mut $ctor);
                }
                #[test]
                fn complement_involution() {
                    smoke_complement_involution(&mut $ctor);
                }
                #[test]
                fn de_morgan() {
                    smoke_de_morgan(&mut $ctor);
                }
                #[test]
                fn subtype_reflexive() {
                    smoke_subtype_reflexive(&mut $ctor);
                }
                #[test]
                fn int_lit_in_int() {
                    smoke_int_lit_in_int(&mut $ctor);
                }
                #[test]
                fn nil_in_atom() {
                    smoke_nil_in_atom(&mut $ctor);
                }
                #[test]
                fn top_bottom() {
                    smoke_top_bottom(&mut $ctor);
                }
                #[test]
                fn tuple_element_disjoint() {
                    smoke_tuple_element_disjoint(&mut $ctor);
                }
                #[test]
                fn arrow_contravariance() {
                    smoke_arrow_contravariance(&mut $ctor);
                }
                #[test]
                fn list_covariance() {
                    smoke_list_covariance(&mut $ctor);
                }
                #[test]
                fn kind_classification() {
                    smoke_kind_classification(&mut $ctor);
                }
                #[test]
                fn display_renders() {
                    smoke_display_renders(&mut $ctor);
                }
            }
        };
    }

    impl_smoke_suite!(concrete, ConcreteTypes);
}

#[cfg(test)]
mod visibility_tests {
    use super::*;
    use crate::type_expr::{
        ModuleTypeEnv, build_module_type_env_for, opaque_owner_module, qualify_opaque_name,
    };

    fn alias_attr(name: &str, body_src: &str) -> crate::ast::Attribute {
        use crate::ast::{Attribute, TypeAliasDecl, TypeExprBody};
        use crate::diag::Span;
        use crate::lexer::{Lexer, Tok};
        let toks = Lexer::new(body_src).tokenize().expect("lex body");
        let body_tokens: Vec<_> = toks
            .into_iter()
            .filter(|t| !matches!(t.tok, Tok::Eof))
            .collect();
        Attribute::TypeAlias(TypeAliasDecl {
            name: name.to_string(),
            name_span: Span::DUMMY,
            body_tokens: TypeExprBody(body_tokens),
            span: Span::DUMMY,
        })
    }

    fn env_for(module: &str, attrs: &[crate::ast::Attribute]) -> ModuleTypeEnv {
        let mut ct = ConcreteTypes;
        build_module_type_env_for(&mut ct, attrs, module)
            .expect("build env")
            .0
    }

    #[test]
    fn qualify_and_invert_roundtrip() {
        let q = qualify_opaque_name("File", "t");
        assert_eq!(q, "File::t");
        assert_eq!(opaque_owner_module(&q), Some("File"));
    }

    #[test]
    fn unqualified_opaque_has_no_owner() {
        let q = qualify_opaque_name("", "resource");
        assert_eq!(q, "resource");
        assert_eq!(opaque_owner_module(&q), None);
    }

    #[test]
    fn opaque_alias_carries_declaring_module() {
        let attrs = vec![alias_attr("t", "opaque integer")];
        let env = env_for("File", &attrs);
        let ct = ConcreteTypes;
        let t = env.get("t").expect("alias resolved");
        assert_eq!(ct.opaque_singleton(t), Some("File::t".to_string()));
    }

    #[test]
    fn check_passes_inside_declaring_module() {
        let attrs = vec![alias_attr("t", "opaque integer")];
        let env = env_for("File", &attrs);
        let ct = ConcreteTypes;
        let t = env.get("t").unwrap();
        assert!(ct.check_opaque_visibility(t, "File").is_ok());
    }

    #[test]
    fn check_rejects_from_other_module() {
        let attrs = vec![alias_attr("t", "opaque integer")];
        let env = env_for("File", &attrs);
        let ct = ConcreteTypes;
        let t = env.get("t").unwrap();
        let err = ct
            .check_opaque_visibility(t, "Other")
            .expect_err("must reject");
        assert_eq!(err.opaque, "File::t");
        assert_eq!(err.owner_module, "File");
        assert_eq!(err.using_module, "Other");
        let msg = format!("{}", err);
        assert!(msg.contains("not accessible from module `Other`"));
        assert!(msg.contains("declared in module `File`"));
    }

    #[test]
    fn check_passes_on_non_opaque_types() {
        let mut ct = ConcreteTypes;
        let int = ct.int();
        let any = ct.any();
        let none = ct.none();
        assert!(ct.check_opaque_visibility(&int, "Anywhere").is_ok());
        assert!(ct.check_opaque_visibility(&any, "Anywhere").is_ok());
        assert!(ct.check_opaque_visibility(&none, "Anywhere").is_ok());
    }

    #[test]
    fn check_passes_on_unqualified_builtin_opaque() {
        let mut ct = ConcreteTypes;
        let d = ct.opaque_of("resource");
        assert!(ct.check_opaque_visibility(&d, "AnyModule").is_ok());
    }

    #[test]
    fn two_modules_declaring_t_are_distinct_opaques() {
        let a = env_for("A", &[alias_attr("t", "opaque integer")]);
        let b = env_for("B", &[alias_attr("t", "opaque integer")]);
        let mut ct = ConcreteTypes;
        let ta = a.get("t").unwrap();
        let tb = b.get("t").unwrap();
        assert_eq!(ct.opaque_singleton(ta), Some("A::t".to_string()));
        assert_eq!(ct.opaque_singleton(tb), Some("B::t".to_string()));
        let inter = ct.intersect(ta.clone(), tb.clone());
        assert!(ct.is_empty(&inter));
        assert!(ct.check_opaque_visibility(ta, "A").is_ok());
        assert!(ct.check_opaque_visibility(ta, "B").is_err());
        assert!(ct.check_opaque_visibility(tb, "B").is_ok());
        assert!(ct.check_opaque_visibility(tb, "A").is_err());
    }

    #[test]
    fn brand_mint_visibility_module_qualified() {
        let mut ct = ConcreteTypes;
        assert!(check_brand_mint_visibility(&mut ct, "M::B", "M").is_ok());
        let err = check_brand_mint_visibility(&mut ct, "M::B", "N").expect_err("must reject");
        assert_eq!(err.opaque, "M::B");
        assert_eq!(err.owner_module, "M");
        assert_eq!(err.using_module, "N");
    }

    #[test]
    fn brand_mint_visibility_unqualified_is_global() {
        let mut ct = ConcreteTypes;
        assert!(check_brand_mint_visibility(&mut ct, "utf8", "AnyModule").is_ok());
        assert!(check_brand_mint_visibility(&mut ct, "utf8", "").is_ok());
    }

    #[test]
    fn opaque_alias_wrapping_resource_is_gated() {
        let attrs = vec![alias_attr("t", "opaque resource(integer)")];
        let env = env_for("File", &attrs);
        let ct = ConcreteTypes;
        let t = env.get("t").unwrap();
        assert_eq!(ct.opaque_singleton(t), Some("File::t".to_string()));
        assert!(ct.check_opaque_visibility(t, "File").is_ok());
        assert!(ct.check_opaque_visibility(t, "Other").is_err());
    }
}
