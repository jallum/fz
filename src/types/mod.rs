//! types.1 — stable type API over the concrete type implementation.
//!
//! Today most compiler data still stores the concrete `Ty` handle. The public
//! boundary is the `Types` trait: a single object that owns every construction,
//! query, and decision about types.
//!
//! `new()` is the system-wide default factory.
//!
//! Parent epic: fz-mm2 (inch-worm strategy — every sub-ticket points back
//! so the plan survives compaction).

use std::collections::HashMap;
use std::hash::Hash;
use std::sync::Arc;

pub mod concrete_types;

pub use concrete_types::ConcreteTypes;
pub(crate) use concrete_types::{Descr, ty_descr, ty_display};

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
/// value rather than two parallel parameters. `Module::nominals` /
/// `SpecPlan::nominals` mint a view over the owned maps.
pub struct Nominals<'a, T = Ty> {
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
pub(crate) use visibility::check_brand_mint_visibility;
pub use visibility::{OpaqueVisibilityError, VisibilityTypes};

pub type DefaultTypes = ConcreteTypes;

/// Construct the system-wide default type implementation.
pub fn new() -> DefaultTypes {
    ConcreteTypes
}

/// Opaque handle to a type. Inner representation is private and is
/// expected to change (interned id, BDD root, ...) without consumer
/// impact. Consumers must go through `Types` for every operation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Ty(pub(crate) Arc<Descr>);

/// Semantic specialization-key slot.
///
/// `Some(ty)` participates in key coverage. `None` is an arity-bearing,
/// position-preserving hole; it is skipped by key coverage and is not `any`.
pub type KeySlot<T = Ty> = Option<T>;

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

    /// Literal keys mentioned by `a`'s positive map clauses. This is an
    /// introspection hook for `src/specs` matching; callers still use
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

#[cfg(test)]
mod conformance_tests {
    use super::*;
    use std::slice;

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

                #[test]
                fn key_is_strictly_more_specific_recognizes_strict_subtype_keys() {
                    let mut t = $ctor;
                    let int = t.int();
                    let int_lit = t.int_lit(7);
                    assert!(t.key_is_strictly_more_specific(slice::from_ref(&int_lit), slice::from_ref(&int)));
                    assert!(!t.key_is_strictly_more_specific(slice::from_ref(&int), slice::from_ref(&int_lit)));
                }

                #[test]
                fn default_bool_lit_uses_reserved_atom_literals() {
                    let mut t = $ctor;
                    let true_lit = t.bool_lit(true);
                    let false_lit = t.bool_lit(false);
                    assert_eq!(t.as_atom_singleton(&true_lit).as_deref(), Some("true"));
                    assert_eq!(t.as_atom_singleton(&false_lit).as_deref(), Some("false"));
                }

                #[test]
                fn default_cpointer_is_builtin_opaque() {
                    let mut t = $ctor;
                    let ptr = t.cpointer();
                    assert_eq!(t.opaque_singleton(&ptr).as_deref(), Some("cpointer"));
                }

                #[test]
                fn default_is_equivalent_recognizes_mutual_subtypes() {
                    let mut t = $ctor;
                    let true_lit = t.bool_lit(true);
                    let false_lit = t.bool_lit(false);
                    let bool_union = t.union(true_lit, false_lit);
                    let bool_t = t.bool();
                    assert!(t.is_equivalent(&bool_union, &bool_t));
                }
            }
        };
    }

    macro_rules! seam_helper_conformance_tests {
        ($mod_name:ident, $ctor:expr) => {
            mod $mod_name {
                use super::*;

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
                fn has_list_shape_distinguishes_list_axis_from_runtime_projection_fallback() {
                    let mut t = $ctor;
                    let int = t.int();
                    let list = t.list(int.clone());
                    assert!(t.has_list_shape(&list));
                    assert!(!t.has_list_shape(&int));
                }

                #[test]
                fn list_element_type_projects_empty_list_as_none() {
                    let mut t = $ctor;
                    let empty = t.empty_list();
                    let projected = t.list_element_type(&empty);
                    assert!(t.is_empty(&projected));
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
                fn alpha_normalize_vars_collapses_alpha_equivalent_callable_shapes() {
                    let mut t = $ctor;
                    let lhs_a = t.type_var(TypeVarId(10));
                    let lhs_b = t.type_var(TypeVarId(11));
                    let lhs_ret = t.type_var(TypeVarId(12));
                    let lhs = t.arrow(
                        &[lhs_a.clone(), lhs_b, lhs_a],
                        lhs_ret,
                    );
                    let rhs_a = t.type_var(TypeVarId(30));
                    let rhs_b = t.type_var(TypeVarId(31));
                    let rhs_ret = t.type_var(TypeVarId(32));
                    let rhs = t.arrow(
                        &[rhs_a.clone(), rhs_b, rhs_a],
                        rhs_ret,
                    );

                    let lhs = t.alpha_normalize_vars(&lhs);
                    let rhs = t.alpha_normalize_vars(&rhs);
                    assert!(
                        t.is_equivalent(&lhs, &rhs),
                        "alpha-equivalent callable shapes should normalize to the same type: lhs={} rhs={}",
                        t.display(&lhs),
                        t.display(&rhs)
                    );
                }

                #[test]
                fn alpha_normalize_vars_preserves_shared_var_structure() {
                    let mut t = $ctor;
                    let repeated_var = t.type_var(TypeVarId(10));
                    let repeated = t.arrow(
                        &[repeated_var.clone(), repeated_var.clone()],
                        repeated_var,
                    );
                    let distinct_a = t.type_var(TypeVarId(20));
                    let distinct_b = t.type_var(TypeVarId(21));
                    let distinct = t.arrow(
                        &[distinct_a.clone(), distinct_b],
                        distinct_a,
                    );

                    let repeated = t.alpha_normalize_vars(&repeated);
                    let distinct = t.alpha_normalize_vars(&distinct);
                    assert!(
                        !t.is_equivalent(&repeated, &distinct),
                        "alpha-normalization must preserve equality structure: repeated={} distinct={}",
                        t.display(&repeated),
                        t.display(&distinct)
                    );
                }
            }
        };
    }

    macro_rules! semantic_helper_conformance_tests {
        ($mod_name:ident, $ctor:expr) => {
            mod $mod_name {
                use super::*;

                fn sigma_of<T>(bindings: impl IntoIterator<Item = (u32, T)>) -> Sigma<T> {
                    bindings.into_iter().map(|(id, ty)| (TypeVarId(id), ty)).collect()
                }

                #[test]
                fn arrow_join_return_union_of_clauses() {
                    let mut t = $ctor;
                    let int_arg = t.int();
                    let int_ret = t.int();
                    let int_arrow = t.arrow(&[int_arg], int_ret);
                    let str_arg = t.str_t();
                    let bool_ret = t.bool();
                    let bool_arrow = t.arrow(&[str_arg], bool_ret.clone());
                    let callable = t.union(int_arrow, bool_arrow);
                    let got = t.arrow_join_return(&callable);
                    let int = t.int();
                    let want = t.union(int, bool_ret);
                    assert!(t.is_equivalent(&got, &want));
                }

                #[test]
                fn arrow_join_return_top_is_any() {
                    let mut t = $ctor;
                    let any = t.any();
                    let got = t.arrow_join_return(&any);
                    assert!(t.is_top(&got));
                }

                #[test]
                fn arrow_join_return_empty_is_any() {
                    let mut t = $ctor;
                    let int = t.int();
                    let got = t.arrow_join_return(&int);
                    assert!(t.is_top(&got));
                }

                #[test]
                fn differs_only_nominally_holds_for_brand_vs_unbranded() {
                    let mut t = $ctor;
                    let str_inner = t.str_t();
                    let mut brand_inners = HashMap::new();
                    brand_inners.insert("utf8".to_string(), str_inner);
                    let opaque_inners = HashMap::new();
                    let utf8 = t.brand_of("utf8");
                    let plain = t.str_t();
                    assert!(t.differs_only_nominally(&utf8, &plain, Nominals::new(&brand_inners, &opaque_inners)));
                }

                #[test]
                fn has_vars_distinguishes_concrete_from_polymorphic() {
                    let mut t = $ctor;
                    let int = t.int();
                    let any = t.any();
                    let var = t.type_var(TypeVarId(0));
                    assert!(!t.has_vars(&int));
                    assert!(!t.has_vars(&any));
                    assert!(t.has_vars(&var));
                }

                #[test]
                fn instantiate_replaces_top_level_var() {
                    let mut t = $ctor;
                    let pattern = t.type_var(TypeVarId(0));
                    let int = t.int();
                    let sigma = sigma_of([(0, int.clone())]);
                    let result = t.instantiate(&pattern, &sigma);
                    assert!(t.is_equivalent(&result, &int));
                }

                #[test]
                fn instantiate_is_identity_when_no_vars_match() {
                    let mut t = $ctor;
                    let pattern = t.type_var(TypeVarId(0));
                    let int = t.int();
                    let sigma = sigma_of([(1, int)]);
                    let result = t.instantiate(&pattern, &sigma);
                    assert!(t.is_equivalent(&result, &pattern));
                }

                #[test]
                fn instantiate_walks_into_lists() {
                    let mut t = $ctor;
                    let var = t.type_var(TypeVarId(0));
                    let list_of_var = t.list(var);
                    let int = t.int();
                    let sigma = sigma_of([(0, int.clone())]);
                    let result = t.instantiate(&list_of_var, &sigma);
                    let list_of_int = t.list(int);
                    assert!(t.is_equivalent(&result, &list_of_int));
                }

                #[test]
                fn instantiate_walks_into_tuples() {
                    let mut t = $ctor;
                    let alpha = t.type_var(TypeVarId(0));
                    let beta = t.type_var(TypeVarId(1));
                    let tuple = t.tuple(&[alpha, beta]);
                    let int = t.int();
                    let str_t = t.str_t();
                    let sigma = sigma_of([(0, int.clone()), (1, str_t.clone())]);
                    let result = t.instantiate(&tuple, &sigma);
                    let expected = t.tuple(&[int, str_t]);
                    assert!(t.is_equivalent(&result, &expected));
                }

                #[test]
                fn instantiate_walks_into_arrow_args_and_ret() {
                    let mut t = $ctor;
                    let alpha = t.type_var(TypeVarId(0));
                    let beta = t.type_var(TypeVarId(1));
                    let arrow = t.arrow(&[alpha], beta);
                    let int = t.int();
                    let bool_t = t.bool();
                    let sigma = sigma_of([(0, int.clone()), (1, bool_t.clone())]);
                    let result = t.instantiate(&arrow, &sigma);
                    let expected = t.arrow(&[int], bool_t);
                    assert!(t.is_equivalent(&result, &expected));
                }

                #[test]
                fn collect_subst_binds_top_level_var_to_witness() {
                    let mut t = $ctor;
                    let pattern = t.type_var(TypeVarId(0));
                    let witness = t.int();
                    let mut sigma = HashMap::new();
                    t.collect_instantiation_subst(&pattern, &witness, &mut sigma);
                    assert_eq!(sigma.len(), 1);
                    assert!(t.is_equivalent(&sigma[&TypeVarId(0)], &witness));
                }

                #[test]
                fn collect_subst_is_noop_on_concrete_pattern() {
                    let mut t = $ctor;
                    let pattern = t.int();
                    let witness = t.int();
                    let mut sigma = HashMap::new();
                    t.collect_instantiation_subst(&pattern, &witness, &mut sigma);
                    assert!(sigma.is_empty());
                }

                #[test]
                fn collect_subst_then_instantiate_is_identity_on_concrete_args() {
                    let mut t = $ctor;
                    let pat_arg = t.type_var(TypeVarId(0));
                    let pat_ret = t.type_var(TypeVarId(0));
                    let witness = t.int();
                    let mut sigma = HashMap::new();
                    t.collect_instantiation_subst(&pat_arg, &witness, &mut sigma);
                    let resolved_ret = t.instantiate(&pat_ret, &sigma);
                    assert!(t.is_equivalent(&resolved_ret, &witness));
                }

                #[test]
                fn collect_subst_distinct_vars_bind_independently() {
                    let mut t = $ctor;
                    let alpha = t.type_var(TypeVarId(0));
                    let beta = t.type_var(TypeVarId(1));
                    let int = t.int();
                    let bool_t = t.bool();
                    let mut sigma = HashMap::new();
                    t.collect_instantiation_subst(&alpha, &int, &mut sigma);
                    t.collect_instantiation_subst(&beta, &bool_t, &mut sigma);
                    assert_eq!(sigma.len(), 2);
                    assert!(t.is_equivalent(&sigma[&TypeVarId(0)], &int));
                    assert!(t.is_equivalent(&sigma[&TypeVarId(1)], &bool_t));
                }

                #[test]
                fn tuple_field_projection_skips_impossible_mixed_arity_conjunctions() {
                    let mut t = $ctor;
                    let done_tuple = {
                        let tag = t.atom_lit("done");
                        let payload = t.int();
                        t.tuple(&[tag, payload])
                    };
                    let halted_tuple = {
                        let tag = t.atom_lit("halted");
                        let payload = t.int();
                        t.tuple(&[tag, payload])
                    };
                    let suspended_tuple = {
                        let tag = t.atom_lit("suspended");
                        let payload = t.int();
                        let continuation = t.int();
                        t.tuple(&[tag, payload, continuation])
                    };
                    let outcomes = {
                        let two = t.union(done_tuple, halted_tuple);
                        t.union(two, suspended_tuple)
                    };
                    let two_tuple = {
                        let a = t.any();
                        let b = t.any();
                        t.tuple(&[a, b])
                    };
                    let narrowed = t.intersect(outcomes, two_tuple);
                    let first = t.tuple_field_type(&narrowed, 0);
                    let expected = {
                        let done = t.atom_lit("done");
                        let halted = t.atom_lit("halted");
                        t.union(done, halted)
                    };
                    assert!(
                        t.is_equivalent(&first, &expected),
                        "projecting a 2-tuple narrowing must ignore impossible 3-tuple conjunctions, got {}",
                        t.display(&first)
                    );
                }

                #[test]
                fn refine_widen_collapses_int_literals_to_int() {
                    let mut t = $ctor;
                    let one = t.int_lit(1);
                    let two = t.int_lit(2);
                    let int = t.int();
                    let w_lits = t.refine_widen(&one, &two);
                    let w_lit_base = t.refine_widen(&one, &int);
                    let w_base = t.refine_widen(&int, &int);
                    assert!(t.is_equivalent(&w_lits, &int));
                    assert!(t.is_equivalent(&w_lit_base, &int));
                    assert!(t.is_equivalent(&w_base, &int));
                }

                #[test]
                fn refine_widen_collapses_float_literals_to_float() {
                    let mut t = $ctor;
                    let a = t.float_lit(1.0);
                    let b = t.float_lit(2.0);
                    let float = t.float();
                    let w = t.refine_widen(&a, &b);
                    assert!(t.is_equivalent(&w, &float));
                }

                #[test]
                fn refine_widen_recurses_into_list_elements() {
                    let mut t = $ctor;
                    let one = t.int_lit(1);
                    let two = t.int_lit(2);
                    let int = t.int();
                    let l1 = t.list(one);
                    let l2 = t.list(two);
                    let lint = t.list(int);
                    let w = t.refine_widen(&l1, &l2);
                    assert!(t.is_equivalent(&w, &lint));
                }

                #[test]
                fn refine_widen_merges_empty_and_non_empty_list_shapes() {
                    let mut t = $ctor;
                    let int = t.int();
                    let empty = t.empty_list();
                    let non_empty = t.non_empty_list(int.clone());
                    let expected = t.list(int);
                    let widened = t.refine_widen(&empty, &non_empty);
                    assert!(t.is_equivalent(&widened, &expected));
                }

                #[test]
                fn convergence_class_unifies_all_list_shapes_but_separates_other_families() {
                    let mut t = $ctor;
                    let int = t.int();
                    let empty = t.empty_list();
                    let nonempty = t.non_empty_list(int.clone());
                    let list = t.list(int.clone());
                    let empty_class = t.convergence_class(&empty);
                    let nonempty_class = t.convergence_class(&nonempty);
                    let list_class = t.convergence_class(&list);
                    assert!(t.is_equivalent(&empty_class, &nonempty_class));
                    assert!(t.is_equivalent(&nonempty_class, &list_class));

                    let tagged = t.tuple(&[int.clone(), int.clone()]);
                    let tagged_class = t.convergence_class(&tagged);
                    assert!(!t.is_equivalent(&tagged_class, &list_class));

                    let int_class = t.convergence_class(&int);
                    assert!(!t.is_equivalent(&int_class, &list_class));
                }

                #[test]
                fn refine_widen_recurses_into_tuple_fields() {
                    let mut t = $ctor;
                    let empty = t.empty_list();
                    let int = t.int();
                    let non_empty = t.non_empty_list(int.clone());
                    let two = t.int_lit(2);
                    let one = t.int_lit(1);
                    let lhs = t.tuple(&[empty, two]);
                    let rhs = t.tuple(&[non_empty, one]);
                    let list_int = t.list(int.clone());
                    let expected = t.tuple(&[list_int, int]);
                    let widened = t.refine_widen(&lhs, &rhs);
                    assert!(t.is_equivalent(&widened, &expected));
                }

                #[test]
                fn refine_widen_recurses_into_resource_payloads() {
                    let mut t = $ctor;
                    let one = t.int_lit(1);
                    let two = t.int_lit(2);
                    let int = t.int();
                    let lhs = t.resource(one);
                    let rhs = t.resource(two);
                    let expected = t.resource(int);
                    let widened = t.refine_widen(&lhs, &rhs);
                    assert!(t.is_equivalent(&widened, &expected));
                }

                #[test]
                fn refine_widen_recurses_into_arrow_returns_and_unions_args() {
                    let mut t = $ctor;
                    let int = t.int();
                    let float = t.float();
                    let empty = t.empty_list();
                    let one = t.int_lit(1);
                    let lhs_ret = t.tuple(&[empty, one]);
                    let lhs = t.arrow(slice::from_ref(&int), lhs_ret);
                    let non_empty = t.non_empty_list(int.clone());
                    let two = t.int_lit(2);
                    let rhs_ret = t.tuple(&[non_empty, two]);
                    let rhs = t.arrow(slice::from_ref(&float), rhs_ret);
                    let union = t.union(int.clone(), float);
                    let list_int = t.list(int.clone());
                    let ret = t.tuple(&[list_int, int]);
                    let expected = t.arrow(&[union], ret);
                    let widened = t.refine_widen(&lhs, &rhs);
                    assert!(t.is_equivalent(&widened, &expected));
                }

                #[test]
                fn refine_widen_recurses_into_map_fields() {
                    let mut t = $ctor;
                    let key = MapKey::Atom("value".to_string());
                    let int = t.int();
                    let empty = t.empty_list();
                    let one = t.int_lit(1);
                    let lhs_value = t.tuple(&[empty, one]);
                    let lhs = t.map(&[(key.clone(), lhs_value)]);
                    let non_empty = t.non_empty_list(int.clone());
                    let two = t.int_lit(2);
                    let rhs_value = t.tuple(&[non_empty, two]);
                    let rhs = t.map(&[(key.clone(), rhs_value)]);
                    let list_int = t.list(int.clone());
                    let expected_value = t.tuple(&[list_int, int]);
                    let expected = t.map(&[(key, expected_value)]);
                    let widened = t.refine_widen(&lhs, &rhs);
                    assert!(t.is_equivalent(&widened, &expected));
                }

                #[test]
                fn refine_widen_falls_back_to_union_for_incompatible_fields_monotonically() {
                    let mut t = $ctor;
                    let int = t.int();
                    let empty = t.empty_list();
                    let tuple = t.tuple(&[empty.clone(), int.clone()]);
                    let prev = t.union(int, tuple.clone());
                    let observed = tuple;
                    let widened = t.refine_widen(&prev, &observed);
                    assert!(t.is_subtype(&prev, &widened));
                    assert!(t.is_subtype(&observed, &widened));
                }

                #[test]
                fn refine_widen_keeps_int_and_float_apart_no_number_rung() {
                    let mut t = $ctor;
                    let i = t.int_lit(1);
                    let f = t.float_lit(2.0);
                    let int = t.int();
                    let float = t.float();
                    let union = t.union(int, float);
                    let any = t.any();
                    let widened = t.refine_widen(&i, &f);
                    assert!(t.is_equivalent(&widened, &union));
                    assert!(!t.is_equivalent(&widened, &any));
                }

                #[test]
                fn refine_widen_any_absorbs() {
                    let mut t = $ctor;
                    let int = t.int();
                    let any = t.any();
                    let w = t.refine_widen(&int, &any);
                    assert!(t.is_equivalent(&w, &any));
                }
            }
        };
    }

    macro_rules! closure_helper_conformance_tests {
        ($mod_name:ident, $ctor:expr) => {
            mod $mod_name {
                use super::*;

                #[test]
                fn erase_closure_identity_preserves_callable_surface_shape() {
                    let mut t = $ctor;
                    let capture = t.int_lit(10);
                    let lit = t.closure_lit(ClosureTarget(3), vec![capture], 2);
                    let erased = t.erase_closure_identity(&lit);
                    assert!(t.closure_lit_parts(&erased).is_none());
                    let clauses = t
                        .callable_clauses(&erased)
                        .expect("erased closure should remain callable");
                    assert_eq!(clauses.len(), 1);
                    assert_eq!(clauses[0].args.len(), 2);
                    assert!(clauses[0].closure.is_none());
                }
            }
        };
    }

    /// Register implementation-agnostic `Types` conformance tests.
    ///
    /// Each complete implementation gets one invocation here. Behavior that
    /// can be expressed through public `Types` hooks belongs in these suites;
    /// representation assertions stay in the implementation's own tests.
    macro_rules! impl_types_conformance_tests {
        ($key_mod:ident, $shape_mod:ident, $semantic_mod:ident, $closure_mod:ident, $ctor:expr) => {
            key_helper_conformance_tests!($key_mod, $ctor);
            seam_helper_conformance_tests!($shape_mod, $ctor);
            semantic_helper_conformance_tests!($semantic_mod, $ctor);
            closure_helper_conformance_tests!($closure_mod, $ctor);
        };
    }

    impl_types_conformance_tests!(
        concrete_types,
        concrete_types_helpers,
        concrete_types_semantics,
        concrete_types_closure,
        ConcreteTypes
    );
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
    use std::slice;

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
        let narrow = t.arrow(slice::from_ref(&arg), i);
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

    pub(super) fn smoke_core_predicates<T: Types>(t: &mut T) {
        let one = t.int_lit(1);
        let int = t.int();
        let float = t.float();
        let nil = t.nil();
        let bool_t = t.bool();
        let atom_lit = t.atom_lit("ok");
        let atom = t.atom();
        let top = t.any();
        let bot = t.none();

        assert!(t.is_integer(&one));
        assert!(t.is_integer(&int));
        assert!(!t.is_integer(&float));
        assert!(t.is_floating(&float));
        assert!(!t.is_floating(&int));
        assert!(t.is_nil(&nil));
        assert!(!t.is_nil(&top));
        assert!(t.is_bool(&bool_t));
        assert!(!t.is_bool(&atom_lit));
        assert!(t.is_atom_type(&nil));
        assert!(t.is_atom_type(&bool_t));
        assert!(t.is_atom_type(&atom));
        assert!(!t.is_atom_type(&int));
        assert!(t.is_top(&top));
        assert!(t.is_empty(&bot));
    }

    pub(super) fn smoke_display_renders<T: Types + RenderTypes>(t: &mut T) {
        let i = t.int();
        let s = t.display(&i);
        assert!(!s.is_empty(), "display of int must not be empty");
    }

    /// Register the full smoke suite as named `#[test]` fns against an
    /// implementation. The first arg names the test submodule (visible
    /// in `cargo test` output as `types::smoke::<name>::...`); the
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
                fn core_predicates() {
                    smoke_core_predicates(&mut $ctor);
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
