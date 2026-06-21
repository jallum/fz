//! Shared type contracts used by compiler2 and the remaining backend substrate.
//!
//! Compiler2 owns the active concrete type kernel. This module keeps the
//! generic traits and small shared data shapes that let compiler phases talk
//! about types without depending on a particular representation.

use std::collections::HashMap;
use std::hash::Hash;

mod closure;
mod literal;
mod map;
mod poly;
mod render;
mod visibility;

pub use closure::{CallableClause, CallableValueKind, ClosureLitInfo, ClosureTarget, ClosureTypes};
pub use literal::LiteralTypes;
pub use map::MapKey;

/// A borrowed view of a module's nominal environment: the brand- and
/// opaque-tag inner-type maps. They are only ever consulted together — to
/// discharge a tag to its runtime representation — so they travel as one
/// value rather than two parallel parameters.
pub struct Nominals<'a, T> {
    pub brand_inners: &'a HashMap<String, T>,
    pub opaque_inners: &'a HashMap<String, T>,
}

// Hand-rolled so the `Copy` bound lands on the references, not on `T`
// (a derive would demand `T: Copy`, which `Descr`/`Ty` are not).
impl<T> Clone for Nominals<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T> Copy for Nominals<'_, T> {}

impl<'a, T> Nominals<'a, T> {
    pub fn new(brand_inners: &'a HashMap<String, T>, opaque_inners: &'a HashMap<String, T>) -> Self {
        Self {
            brand_inners,
            opaque_inners,
        }
    }
}

pub use poly::TypeVarId;
pub use render::RenderTypes;
pub use visibility::{OpaqueVisibilityError, VisibilityTypes};

/// Semantic specialization-key slot.
///
/// `Some(ty)` participates in key coverage. `None` is an arity-bearing,
/// position-preserving hole; it is skipped by key coverage and is not `any`.
pub type KeySlot<T> = Option<T>;

pub fn key_slots_from_tys<T>(tys: impl IntoIterator<Item = T>) -> Vec<KeySlot<T>> {
    tys.into_iter().map(Some).collect()
}

pub fn key_slots_observed<T: Clone>(key: &[KeySlot<T>]) -> Vec<T> {
    key.iter().filter_map(Clone::clone).collect()
}

pub fn key_slot_var_count<T: Types>(t: &T, key: &[KeySlot<T::Ty>]) -> usize {
    t.key_var_count(&key_slots_observed(key))
}

pub fn key_slots_to_tys<T: Types>(t: &mut T, key: &[KeySlot<T::Ty>]) -> Vec<T::Ty> {
    key.iter().map(|slot| slot.clone().unwrap_or_else(|| t.any())).collect()
}

pub fn display_key_slots<T: RenderTypes>(t: &T, key: &[KeySlot<T::Ty>]) -> String {
    let parts: Vec<String> = key
        .iter()
        .map(|slot| match slot {
            Some(ty) => t.display(ty),
            None => "_".to_string(),
        })
        .collect();
    format!("[{}]", parts.join(", "))
}

/// Substitution map for `instantiate`: every `Var(id)` occurrence in the
/// input `Ty` is replaced by `sigma[id]`.
pub type Sigma<T> = HashMap<TypeVarId, T>;

/// The type universe — owner of every type-system query.
///
/// Methods that may need to materialize new types take `&mut self`;
/// pure queries take `&self`. Future implementations (interning,
/// memoization) populate state on construction calls and read it on
/// queries.
pub trait Types {
    type Ty: Clone + Eq + Hash;

    // ---- constructors --------------------------------------------------

    fn any(&mut self) -> Self::Ty;
    fn repeat(&mut self, ty: Self::Ty, n: usize) -> Vec<Self::Ty> {
        vec![ty; n]
    }
    fn none(&mut self) -> Self::Ty;
    fn nil(&mut self) -> Self::Ty;
    fn bool(&mut self) -> Self::Ty;
    fn bool_lit(&mut self, b: bool) -> Self::Ty {
        self.atom_lit(if b { "true" } else { "false" })
    }
    fn int(&mut self) -> Self::Ty;
    fn int_lit(&mut self, n: i64) -> Self::Ty;
    fn float(&mut self) -> Self::Ty;
    fn float_lit(&mut self, f: f64) -> Self::Ty;
    fn atom(&mut self) -> Self::Ty;
    fn atom_lit(&mut self, name: &str) -> Self::Ty;
    fn type_var(&mut self, id: TypeVarId) -> Self::Ty;
    fn cpointer(&mut self) -> Self::Ty {
        self.opaque_of("cpointer")
    }
    fn resource(&mut self, payload: Self::Ty) -> Self::Ty;
    fn arrow(&mut self, args: &[Self::Ty], ret: Self::Ty) -> Self::Ty;
    fn tuple(&mut self, elems: &[Self::Ty]) -> Self::Ty;
    fn empty_list(&mut self) -> Self::Ty;
    fn list(&mut self, elem: Self::Ty) -> Self::Ty;
    fn non_empty_list(&mut self, elem: Self::Ty) -> Self::Ty {
        self.list(elem)
    }
    fn map(&mut self, fields: &[(MapKey, Self::Ty)]) -> Self::Ty;
    fn str_t(&mut self) -> Self::Ty;
    fn map_top(&mut self) -> Self::Ty;
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

    /// True iff `a` has a positive list axis. This keeps evidence-producing
    /// callers from mistaking `list_element_type`'s runtime fallback for proof.
    fn has_list_shape(&self, a: &Self::Ty) -> bool;

    fn resource_payload_type(&mut self, a: &Self::Ty) -> Option<Self::Ty>;

    /// Replace resource-shaped values with an opaque alias owned by `owner`
    /// when one exact alias body exists. Implementations may recurse through
    /// structural containers; the default is conservative.
    fn mint_owned_resource_aliases(
        &mut self,
        a: Self::Ty,
        _owner: &str,
        _opaque_inners: &HashMap<String, Self::Ty>,
    ) -> Self::Ty {
        a
    }

    /// Project `a`'s tuple-axis components at `arity`. Returns a vector
    /// of length `arity`; positions with no matching shape default to
    /// `any`.
    fn tuple_projections(&mut self, a: &Self::Ty, arity: usize) -> Vec<Self::Ty>;

    /// Project field `index` across the feasible tuple clauses of `a`.
    /// Returns `none` when no possible tuple value has that field.
    fn tuple_field_type(&mut self, a: &Self::Ty, index: usize) -> Self::Ty;

    /// The widest arity present in `a`'s tuple-axis clauses, or 0 if
    /// `a` has no tuple axis.
    fn max_tuple_arity(&self, a: &Self::Ty) -> usize;

    /// Refine `a`'s map-axis by overlaying `(key, v)`. Used by
    /// MapUpdate to type the result of `m | { k => v }`.
    fn refine_map_field(&mut self, a: &Self::Ty, key: &MapKey, v: &Self::Ty) -> Self::Ty;

    /// Look up `key` in `a`'s map axis, returning the field's type
    /// if statically known.
    fn map_field_lookup(&mut self, a: &Self::Ty, key: &MapKey) -> Option<Self::Ty>;

    /// Literal keys mentioned by `a`'s positive map clauses. Callers still use
    /// `map_field_lookup` to obtain the set-theoretic field type.
    fn map_known_keys(&self, a: &Self::Ty) -> Vec<MapKey>;

    /// fz-rh5.6 — transform `a` for use as a recursive-call spec key.
    /// The planner owns the policy for when this is applied; the type
    /// implementation owns the concrete widening transform.
    fn widen_for_recursive_spec_key(&mut self, a: &Self::Ty) -> Self::Ty;

    /// Canonicalize named type-variable ids up to alpha-equivalence while
    /// preserving their equality structure. Used when public specialization
    /// keys should not fork on fresh-id accidents alone.
    fn alpha_normalize_vars(&mut self, a: &Self::Ty) -> Self::Ty;

    /// Binary least-upper-bound in the **refinement lattice** — the
    /// finite-height widening join the specialization worklist uses to settle a
    /// recursive slot (`.agent/docs/type-specialization.md`). Distinct from
    /// `union` (the exact set-theoretic join, infinite height): `refine_widen`
    /// collapses literal axes to their base recursively, so a slot ascends only
    /// a bounded chain — `int_lit(1) ⊔ int_lit(2) = int`, and structurally
    /// `[] ⊔ nonempty_list(a) = list(a)`. Loop-invariant slots are their own LUB.
    fn refine_widen(&mut self, a: &Self::Ty, b: &Self::Ty) -> Self::Ty;

    /// The activation-identity class of `a` for non-dispatch-slot convergence
    /// in type inference. Two values share an activation only when their
    /// classes match; same-class slots then join via `refine_widen` in the
    /// stored inputs. All pure list shapes share one class (so an
    /// accumulator's emptiness/element type does not fork recursive
    /// activations — the balloon), while disjoint families (`int` vs a tagged
    /// tuple) keep distinct classes so their behaviour stays observable.
    fn convergence_class(&mut self, a: &Self::Ty) -> Self::Ty;

    // ---- lattice ops ---------------------------------------------------

    fn union(&mut self, a: Self::Ty, b: Self::Ty) -> Self::Ty;
    fn intersect(&mut self, a: Self::Ty, b: Self::Ty) -> Self::Ty;
    #[cfg(test)]
    fn complement(&mut self, a: Self::Ty) -> Self::Ty;
    fn difference(&mut self, a: Self::Ty, b: Self::Ty) -> Self::Ty;

    // ---- predicates ----------------------------------------------------

    fn is_empty(&self, a: &Self::Ty) -> bool;
    #[cfg(test)]
    fn is_top(&self, a: &Self::Ty) -> bool;
    fn is_subtype(&self, a: &Self::Ty, b: &Self::Ty) -> bool;
    /// Brand-AWARE disjointness — the typing/dispatch/boundary question.
    /// NEVER use this to decide whether two runtime values can be equal or
    /// whether a pattern can match; use `is_value_disjoint` for that.
    fn is_disjoint(&self, a: &Self::Ty, b: &Self::Ty) -> bool;
    /// Brand-BLIND disjointness in the runtime-representation model: true iff
    /// no two runtime values of `a`/`b` can ever be equal / match. The ONLY
    /// disjointness that may authorize folding `==`/`!=` or pruning a pattern
    /// arm. Tags are discharged through `nominals`.
    fn is_value_disjoint(&self, a: &Self::Ty, b: &Self::Ty, nominals: Nominals<'_, Self::Ty>) -> bool;
    /// True iff `a`/`b` are brand-AWARE disjoint yet NOT value-disjoint: they
    /// differ only by a brand/opaque the runtime erases. This is exactly the
    /// set of comparisons the old brand-aware fold broke; consumers emit a
    /// telemetry signal on it.
    fn differs_only_nominally(&self, a: &Self::Ty, b: &Self::Ty, nominals: Nominals<'_, Self::Ty>) -> bool {
        self.is_disjoint(a, b) && !self.is_value_disjoint(a, b, nominals)
    }
    fn is_equivalent(&self, a: &Self::Ty, b: &Self::Ty) -> bool {
        a == b || (self.is_subtype(a, b) && self.is_subtype(b, a))
    }

    /// Count top-level named type vars across a spec key. Used by
    /// most-specific-wins dispatch ordering: fewer vars = more concrete.
    fn key_var_count(&self, key: &[Self::Ty]) -> usize;

    /// Query-key subsumption with positional type-var binding for spec lookup.
    fn key_subsumes_with(&self, query: &Self::Ty, key: &Self::Ty, sigma: &mut Sigma<Self::Ty>) -> bool;

    /// True iff `lhs` is strictly more specific than `rhs` positionwise:
    /// every element of `lhs` is a subtype of the corresponding element
    /// of `rhs`, and at least one position is a strict subtype.
    fn key_is_strictly_more_specific(&self, lhs: &[Self::Ty], rhs: &[Self::Ty]) -> bool {
        lhs.len() == rhs.len()
            && lhs
                .iter()
                .zip(rhs.iter())
                .fold((true, false), |(all_le, any_strict), (l, r)| {
                    (all_le && self.is_subtype(l, r), any_strict || !self.is_subtype(r, l))
                })
                == (true, true)
    }

    // ---- introspection -------------------------------------------------

    /// Coarser than `is_disjoint`: true iff `a` and `b` share at least
    /// one populated axis (basic kind, atoms, ints, floats, tuples,
    /// lists, arrows, maps, opaques, brands, vars). Used by the dead-binop
    /// lint to flag cross-kind comparisons (`x == :ok` when `x: int`)
    /// without firing on within-axis literal-disjoint cases (`1 == 2`,
    /// `:ok == :err`). Pair with `is_value_disjoint` to also stay quiet on
    /// brand-vs-underlying pairs (which overlap once brands are erased).
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
    #[cfg(test)]
    fn brand_singleton(&self, a: &Self::Ty) -> Option<String>;

    /// True iff `a` is a singleton-literal value — a single int_lit,
    /// float_lit, atom_lit, etc. Used by if-condition narrowing on
    /// equality predicates to refine the non-singleton operand.
    fn is_singleton_lit(&self, a: &Self::Ty) -> bool;

    /// If `a` is a singleton integer literal, return its value.
    /// Used by binop folding (numeric_result_fold, compare_result).
    fn as_int_singleton(&self, a: &Self::Ty) -> Option<i64>;

    /// If `a` is a singleton float literal, return its value.
    fn as_float_singleton(&self, a: &Self::Ty) -> Option<f64>;

    /// If `a` is a singleton atom literal, return its name.
    fn as_atom_singleton(&self, a: &Self::Ty) -> Option<String>;

    /// If `a` is a literal tuple, return its elements in order.
    #[cfg(test)]
    fn tuple_lit_elems(&self, a: &Self::Ty) -> Option<Vec<Self::Ty>>;

    /// If `a` is a singleton literal suitable as a map key, return it.
    fn as_map_key(&self, a: &Self::Ty) -> Option<MapKey> {
        self.as_int_singleton(a)
            .map(MapKey::Int)
            .or_else(|| self.as_atom_singleton(a).map(MapKey::Atom))
    }

    /// Join the return side of a callable type.
    fn arrow_join_return(&mut self, a: &Self::Ty) -> Self::Ty;

    /// Project the parameter side of a single-clause callable type. The dual of
    /// `arrow_join_return`: returns the positive clause's argument types, or an
    /// empty vector when `a` is not a pure single-clause arrow.
    fn arrow_params(&self, a: &Self::Ty) -> Vec<Self::Ty>;

    // ---- substitution --------------------------------------------------

    fn instantiate(&mut self, a: &Self::Ty, sigma: &Sigma<Self::Ty>) -> Self::Ty;
    fn collect_instantiation_subst(&mut self, pattern: &Self::Ty, witness: &Self::Ty, sigma: &mut Sigma<Self::Ty>);

    // ---- adoption-ease predicates -------------------------------------

    fn is_integer(&self, a: &Self::Ty) -> bool;
    fn is_floating(&self, a: &Self::Ty) -> bool;
    fn is_nil(&self, a: &Self::Ty) -> bool;
    #[cfg(test)]
    fn is_bool(&self, a: &Self::Ty) -> bool;
    /// True when `a`'s classification is purely atom-shaped — atom, bool,
    /// or nil. Useful when a consumer wants "is this any kind of atom?"
    /// rather than the narrower `is_nil` / `is_bool`.
    #[cfg(test)]
    fn is_atom_type(&self, a: &Self::Ty) -> bool;

    /// True iff `a` mentions any free type variable.
    /// Used by the planner to decide whether substitution is required.
    fn has_vars(&self, a: &Self::Ty) -> bool;
}
