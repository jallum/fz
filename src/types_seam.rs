//! types-seam.1 — API seam over `crate::types::Descr`.
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
use std::sync::Arc;

use crate::types::{Descr, MapKey, TypeVarId};

/// Opaque handle to a type. Inner representation is private and is
/// expected to change (interned id, BDD root, ...) without consumer
/// impact. Consumers must go through `Types` for every operation.
#[derive(Clone)]
pub struct Ty(Arc<Descr>);

impl Ty {
    pub(crate) fn from_descr(d: Descr) -> Self {
        Ty(Arc::new(d))
    }

    pub(crate) fn descr(&self) -> &Descr {
        &self.0
    }
}

/// Migration-period view that every `Self::Ty` exposes a Descr. Lets
/// generic-T code write `ty.as_descr()` instead of `t.to_descr(&ty)`.
/// Removed once consumer locals are `Ty`-typed and no Descr fall-back
/// is needed (epic pass 5+).
pub trait AsDescr {
    fn as_descr(&self) -> Descr;
}

impl AsDescr for Ty {
    fn as_descr(&self) -> Descr {
        (*self.0).clone()
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

/// The type universe — owner of every type-system query.
///
/// Methods that may need to materialize new types take `&mut self`;
/// pure queries take `&self`. Future implementations (interning,
/// memoization) populate state on construction calls and read it on
/// queries.
pub trait Types {
    type Ty: Clone + AsDescr;

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
    fn arrow(&mut self, args: &[Self::Ty], ret: Self::Ty) -> Self::Ty;
    fn tuple(&mut self, elems: &[Self::Ty]) -> Self::Ty;
    fn list(&mut self, elem: Self::Ty) -> Self::Ty;
    fn map(&mut self, fields: &[(MapKey, Self::Ty)]) -> Self::Ty;

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

    // ---- introspection -------------------------------------------------

    fn kind_of(&self, a: &Self::Ty) -> Kind;

    /// Coarser than `is_disjoint`: true iff `a` and `b` share at least
    /// one populated axis (basic kind, atoms, ints, floats, tuples,
    /// lists, arrows, maps, opaques, brands, vars). Used by lints that
    /// want to flag cross-kind comparisons (`x == :ok` when `x: int`)
    /// without firing on within-axis literal-disjoint cases (`1 == 2`).
    fn kinds_overlap(&self, a: &Self::Ty, b: &Self::Ty) -> bool;

    /// Render `a` for user-facing diagnostics. Owned-string return
    /// day-one; consumers `format!("{}", t.display(&ty))`-style.
    fn display(&self, a: &Self::Ty) -> String;

    // ---- substitution --------------------------------------------------

    fn instantiate(&mut self, a: &Self::Ty, sigma: &Sigma<Self::Ty>) -> Self::Ty;

    // ---- migration bridge ---------------------------------------------
    //
    // Temporary Descr↔Ty conversion. Lets a body that's still
    // Descr-typed locally route operations through the seam without
    // rewriting the carrier all at once. Removed once every consumer
    // has migrated its locals to `Ty` (the epic's pass 5+).
    fn from_descr(&mut self, d: &Descr) -> Self::Ty;
    fn to_descr(&self, a: &Self::Ty) -> Descr;

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
}

/// Day-one implementation: thin wrapper around `Descr`. Zero fields —
/// it's an oracle, not a store. Future implementations will hold
/// interning tables, memo caches, or BDD nodes.
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

    fn kind_of(&self, a: &Ty) -> Kind {
        descr_kind(a.descr())
    }

    fn kinds_overlap(&self, a: &Ty, b: &Ty) -> bool {
        a.descr().kinds_overlap(b.descr())
    }

    fn display(&self, a: &Ty) -> String {
        format!("{}", a.descr())
    }

    fn instantiate(&mut self, a: &Ty, sigma: &Sigma<Ty>) -> Ty {
        let inner: HashMap<TypeVarId, Descr> = sigma
            .iter()
            .map(|(id, t)| (*id, t.descr().clone()))
            .collect();
        Ty::from_descr(a.descr().instantiate(&inner))
    }

    fn from_descr(&mut self, d: &Descr) -> Ty {
        Ty::from_descr(d.clone())
    }
    fn to_descr(&self, a: &Ty) -> Descr {
        a.descr().clone()
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
        let narrow = t.arrow(&[i.clone()], i);
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
                #[test] fn primitives_distinct()      { smoke_primitives_distinct(&mut $ctor); }
                #[test] fn union_idempotent()         { smoke_union_idempotent(&mut $ctor); }
                #[test] fn intersect_idempotent()     { smoke_intersect_idempotent(&mut $ctor); }
                #[test] fn complement_involution()    { smoke_complement_involution(&mut $ctor); }
                #[test] fn de_morgan()                { smoke_de_morgan(&mut $ctor); }
                #[test] fn subtype_reflexive()        { smoke_subtype_reflexive(&mut $ctor); }
                #[test] fn int_lit_in_int()           { smoke_int_lit_in_int(&mut $ctor); }
                #[test] fn nil_in_atom()              { smoke_nil_in_atom(&mut $ctor); }
                #[test] fn top_bottom()               { smoke_top_bottom(&mut $ctor); }
                #[test] fn tuple_element_disjoint()   { smoke_tuple_element_disjoint(&mut $ctor); }
                #[test] fn arrow_contravariance()     { smoke_arrow_contravariance(&mut $ctor); }
                #[test] fn list_covariance()          { smoke_list_covariance(&mut $ctor); }
                #[test] fn kind_classification()      { smoke_kind_classification(&mut $ctor); }
                #[test] fn display_renders()          { smoke_display_renders(&mut $ctor); }
            }
        };
    }

    impl_smoke_suite!(concrete, ConcreteTypes);
}
