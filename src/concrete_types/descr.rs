//! The `Descr` set-theoretic type descriptor — its fields and inherent impls.

use crate::fz_ir::FnId;
use crate::types::{MapKey, Nominals, TypeVarId};

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::mem::replace;

use super::bits::{BASIC_NAMES, BasicBits, F64Bits};
use super::conj::Conj;
use super::dnf::{
    dnf_intersect, dnf_neg, dnf_union, is_dnf_top, normalize_empty_nonempty_list_unions, subsumption_dedup,
};
use super::emptiness::{
    Memo, func_clause_empty, list_clause_empty, map_clause_empty, resource_clause_empty, tuple_clause_empty,
};
use super::format::{
    format_arrow_clause, format_list_clause, format_lit_set_capped, format_map_clause, format_resource_clause,
    format_tuple_clause, render_reserved_atom_set,
};
use super::lit_set::{AtomSet, FloatSet, IntSet, LiteralSet, VarSet, closure_ret_var_id, closure_var_id};
use super::sigs::{ArrowSig, ClosureLit, ListSig, MapSig, ResourceSig, TupleSig};
use super::views::{
    AtomTypeTest, AtomView, BrandView, Component, FloatView, FuncView, IntView, ListView, MapView, OpaqueView,
    ResourceView, TupleView, VarView,
};
use super::{ty_descr, ty_from_descr};

#[derive(Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub(crate) struct Descr {
    pub(crate) basic: BasicBits,
    pub(crate) atoms: AtomSet,
    pub(crate) ints: IntSet,
    pub(crate) floats: FloatSet,
    /// Nominal opaque-type tags. A value of opaque type `T` (declared as
    /// `@type T :: opaque U`) has `opaques = {"T"}` AND the underlying `U`
    /// axes populated. Opaque types are nominal: `T ⊄ U` even when the
    /// underlying type of `T` is `U`, because the opaques axis is non-empty
    /// and distinct from the plain-`U` descriptor (which has `opaques = ∅`).
    pub(crate) opaques: LiteralSet<String>,
    /// fz-axu.2 (K1) — nominal brand tags. A value of brand `B` (declared
    /// as `@type B :: refines U`) has `brands = {"B"}` AND the underlying
    /// `U` axes populated. Unlike opaques, brands are a *proper subset* of
    /// `U`: `B ⊆ U` holds because the brand-stripped Descr (drop `brands`,
    /// keep the structural axes) is structurally `U`. The is_subtype rule
    /// that makes this work lands in K4; K1 only adds the axis to the
    /// lattice. brand_inners on Module/Program registers the underlying
    /// type for each tag (analogous to opaque_inners).
    pub(crate) brands: LiteralSet<String>,
    /// fz-try.5 — parametric type variables. Operationally identical to
    /// `opaques`: a finite-or-cofinite set of nominal names with
    /// component-wise union/intersect/neg. Semantically distinguished only
    /// by the use-site contract — vars are *substituted* at instantiation
    /// sites (fz-try.6 onward); opaques are fixed. The lattice cannot tell
    /// them apart.
    ///
    /// Vars enter the lattice via `Descr::var(id)` at fresh-var introduction
    /// sites (function-typing entry for unconstrained parameters,
    /// `closure_lit()` stubs after fz-try.7). Until C2 lands, this axis is
    /// only constructed in tests; the rest of the codebase still uses
    /// `Descr::any()` stubs.
    pub(crate) vars: VarSet,
    /// DNF over tuple shapes. Empty Vec = no tuples ("false"); a single
    /// `Conj::top()` clause = every tuple ("true").
    pub(crate) tuples: Vec<Conj<TupleSig>>,
    pub(crate) lists: Vec<Conj<ListSig>>,
    pub(crate) resources: Vec<Conj<ResourceSig>>,
    pub(crate) funcs: Vec<Conj<ArrowSig>>,
    pub(crate) maps: Vec<Conj<MapSig>>,
}

impl Descr {
    // ---- top / bottom ----

    pub(crate) fn any() -> Self {
        Descr {
            basic: BasicBits::ALL,
            atoms: AtomSet::any(),
            ints: IntSet::any(),
            floats: FloatSet::any(),
            opaques: LiteralSet::any(),
            brands: LiteralSet::any(),
            vars: VarSet::any(),
            tuples: vec![Conj::top()],
            lists: vec![Conj::top()],
            resources: vec![Conj::top()],
            funcs: vec![Conj::top()],
            maps: vec![Conj::top()],
        }
    }

    pub(crate) fn none() -> Self {
        Descr {
            basic: BasicBits::NONE,
            atoms: AtomSet::none(),
            ints: IntSet::none(),
            floats: FloatSet::none(),
            opaques: LiteralSet::none(),
            brands: LiteralSet::none(),
            vars: VarSet::none(),
            tuples: Vec::new(),
            lists: Vec::new(),
            resources: Vec::new(),
            funcs: Vec::new(),
            maps: Vec::new(),
        }
    }

    /// Create a nominal opaque type named `name`. The result is purely nominal:
    /// no structural axes are populated, so `opaque("pid") ⊄ integer` and
    /// `integer ⊄ opaque("pid")` — they are disjoint in the type lattice.
    ///
    /// At codegen, the wire type is determined separately from the declaration
    /// site (see `ExternDecl.ret_descr`), not from this Descr.
    pub(crate) fn opaque_of(name: impl Into<String>) -> Self {
        let mut d = Self::none();
        d.opaques = LiteralSet::lit(name.into());
        d
    }

    /// fz-axu.2 (K1) — construct a Descr that names exactly the brand
    /// `name`. Only the brands axis is populated. K1 does not yet thread
    /// the underlying type through; the K4 is_subtype rule consults
    /// `Module.brand_inners[name]` at use sites to recognise
    /// `brand(name) ⊆ inner`. Until K4, this Descr is treated as a pure
    /// nominal tag, like `opaque_of`.
    #[allow(dead_code)] // K2 wires it into the `refines` declaration; K3 mints values.
    pub(crate) fn brand_of(name: impl Into<String>) -> Self {
        let mut d = Self::none();
        d.brands = LiteralSet::lit(name.into());
        d
    }

    /// fz-try.5 — construct a Descr that is exactly the type variable `id`.
    /// The result has all concrete axes empty and `vars = {id}`. Lattice
    /// operations treat the result like a nominal opaque; substitution
    /// (fz-try.6) replaces it with a concrete Descr at instantiation sites.
    ///
    /// Consumed by fz-try.7 (`closure_lit()` stub replacement) and fz-try.6
    /// (planner fresh-var introduction). Tests in this module exercise the
    /// constructor; the main binary will start using it in C2.
    #[allow(dead_code)]
    pub(crate) fn var(id: TypeVarId) -> Self {
        let mut d = Self::none();
        d.vars = LiteralSet::lit(id);
        d
    }

    /// fz-try.6 — does this Descr (or any nested Descr in its structural
    /// axes) carry at least one *named* type variable id (one a substitution
    /// could bind)? Pure read; substitution can be skipped when this is false.
    ///
    /// Note: `Descr::any()` has `vars: cofinite-empty` (the *universe* of all
    /// vars). That is not a substitutable pattern — σ binds specific ids, not
    /// "every var" — so `Descr::any().has_vars() == false`.
    pub(crate) fn has_vars(&self) -> bool {
        if !self.vars.set.is_empty() {
            return true;
        }
        let dnf_any = |dnf: &[Conj<ArrowSig>]| {
            dnf.iter().any(|c| {
                c.pos
                    .iter()
                    .chain(c.neg.iter())
                    .any(|sig| sig.args.iter().any(|d| d.has_vars()) || sig.ret.has_vars())
            })
        };
        let tuple_any = self.tuples.iter().any(|c| {
            c.pos
                .iter()
                .chain(c.neg.iter())
                .any(|sig| sig.elems.iter().any(|d| d.has_vars()))
        });
        let list_any = self.lists.iter().any(|c| {
            c.pos
                .iter()
                .chain(c.neg.iter())
                .any(|sig| sig.elem.as_ref().is_some_and(|elem| elem.has_vars()))
        });
        let resource_any = self
            .resources
            .iter()
            .any(|c| c.pos.iter().chain(c.neg.iter()).any(|sig| sig.payload.has_vars()));
        let map_any = self.maps.iter().any(|c| {
            c.pos
                .iter()
                .chain(c.neg.iter())
                .any(|sig| sig.fields.values().any(|d| d.has_vars()))
        });
        tuple_any || list_any || resource_any || dnf_any(&self.funcs) || map_any
    }

    /// fz-try.6 — call-site substitution. Walks the descriptor and replaces
    /// every occurrence of `Var(id)` in `self.vars` (or any nested Descr)
    /// with `σ[id]`. Vars not in σ pass through unchanged. The walk is
    /// structural and pure — no algebra changes, no fresh-var introduction,
    /// no recursion guard needed (Descr trees terminate).
    ///
    /// This is the realization of the principle named in
    /// `docs/descr-cleanup.md`: lattice axes are uniform; substitution is
    /// operational. The lattice does not know which of its names
    /// substitute — that's a property of the caller. This walk is the
    /// caller.
    pub(crate) fn instantiate(&self, sigma: &HashMap<TypeVarId, Descr>) -> Descr {
        if !self.has_vars() {
            return self.clone();
        }
        // Split this Descr's vars axis into "covered by σ" and "passes through."
        let mut substituted = Descr::none();
        let mut passthrough_vars = self.vars.clone();
        if !self.vars.cofinite {
            // Finite set of explicit var ids — substitute each that σ covers.
            let mut new_set = BTreeSet::new();
            for id in &self.vars.set {
                match sigma.get(id) {
                    Some(replacement) => {
                        substituted = substituted.union(replacement);
                    }
                    None => {
                        new_set.insert(*id);
                    }
                }
            }
            passthrough_vars = LiteralSet {
                set: new_set,
                cofinite: false,
            };
        }
        // Build the substituted-Descr with concrete axes preserved, vars
        // partitioned, and nested Descrs in structural axes recursively
        // instantiated. Then union the substitution-produced material.
        let walked_tuples: Vec<Conj<TupleSig>> = self
            .tuples
            .iter()
            .map(|c| Conj {
                pos: c
                    .pos
                    .iter()
                    .map(|sig| TupleSig {
                        elems: sig.elems.iter().map(|d| d.instantiate(sigma)).collect(),
                    })
                    .collect(),
                neg: c
                    .neg
                    .iter()
                    .map(|sig| TupleSig {
                        elems: sig.elems.iter().map(|d| d.instantiate(sigma)).collect(),
                    })
                    .collect(),
            })
            .collect();
        let walked_lists: Vec<Conj<ListSig>> = self
            .lists
            .iter()
            .map(|c| Conj {
                pos: c
                    .pos
                    .iter()
                    .map(|sig| ListSig {
                        empty: sig.empty,
                        elem: sig.elem.as_ref().map(|elem| Box::new(elem.instantiate(sigma))),
                    })
                    .collect(),
                neg: c
                    .neg
                    .iter()
                    .map(|sig| ListSig {
                        empty: sig.empty,
                        elem: sig.elem.as_ref().map(|elem| Box::new(elem.instantiate(sigma))),
                    })
                    .collect(),
            })
            .collect();
        let walked_funcs: Vec<Conj<ArrowSig>> = self
            .funcs
            .iter()
            .map(|c| Conj {
                pos: c
                    .pos
                    .iter()
                    .map(|sig| ArrowSig {
                        args: sig.args.iter().map(|d| d.instantiate(sigma)).collect(),
                        ret: Box::new(sig.ret.instantiate(sigma)),
                        lit: sig.lit.clone(),
                    })
                    .collect(),
                neg: c
                    .neg
                    .iter()
                    .map(|sig| ArrowSig {
                        args: sig.args.iter().map(|d| d.instantiate(sigma)).collect(),
                        ret: Box::new(sig.ret.instantiate(sigma)),
                        lit: sig.lit.clone(),
                    })
                    .collect(),
            })
            .collect();
        let walked_resources: Vec<Conj<ResourceSig>> = self
            .resources
            .iter()
            .map(|c| Conj {
                pos: c
                    .pos
                    .iter()
                    .map(|sig| ResourceSig {
                        payload: Box::new(sig.payload.instantiate(sigma)),
                    })
                    .collect(),
                neg: c
                    .neg
                    .iter()
                    .map(|sig| ResourceSig {
                        payload: Box::new(sig.payload.instantiate(sigma)),
                    })
                    .collect(),
            })
            .collect();
        let walked_maps: Vec<Conj<MapSig>> = self
            .maps
            .iter()
            .map(|c| Conj {
                pos: c
                    .pos
                    .iter()
                    .map(|sig| MapSig {
                        fields: sig
                            .fields
                            .iter()
                            .map(|(k, v)| (k.clone(), v.instantiate(sigma)))
                            .collect(),
                    })
                    .collect(),
                neg: c
                    .neg
                    .iter()
                    .map(|sig| MapSig {
                        fields: sig
                            .fields
                            .iter()
                            .map(|(k, v)| (k.clone(), v.instantiate(sigma)))
                            .collect(),
                    })
                    .collect(),
            })
            .collect();
        let base = Descr {
            basic: self.basic,
            atoms: self.atoms.clone(),
            ints: self.ints.clone(),
            floats: self.floats.clone(),
            opaques: self.opaques.clone(),
            brands: self.brands.clone(),
            vars: passthrough_vars,
            tuples: walked_tuples,
            lists: walked_lists,
            resources: walked_resources,
            funcs: walked_funcs,
            maps: walked_maps,
        };
        base.union(&substituted)
    }

    /// fz-try.6 — extract a substitution σ from positionally matching
    /// `pattern` (a Descr with vars) against `witness` (a concrete Descr).
    /// For each Var(α) appearing in `pattern`'s top-level `vars` axis, bind
    /// α → witness. Vars buried inside structural axes do not contribute
    /// (call-site σ-construction is positional, not structural — the
    /// witness's shape there can't be matched without unification, which
    /// the design rejects).
    ///
    /// If σ would bind the same id to incompatible witnesses, later bindings
    /// win — call sites supplying inconsistent witnesses are caller bugs,
    /// surfaced by the planner's downstream emptiness checks.
    pub(crate) fn collect_subst_into(pattern: &Descr, witness: &Descr, sigma: &mut HashMap<TypeVarId, Descr>) {
        if pattern.vars.cofinite {
            // pattern.vars is "any var" — meaningless as a binding source;
            // skip. (This shape arises only from Descr::any() patterns.)
            return;
        }
        for id in &pattern.vars.set {
            sigma.insert(*id, witness.clone());
        }
    }

    // ---- basic types ----

    fn from_basic(b: BasicBits) -> Self {
        let mut d = Self::none();
        d.basic = b;
        d
    }
    /// fz-yan.2 — `nil` is the reserved atom literal `nil`. Pre-yan it
    /// lived in its own BasicBits axis; with the runtime split it's a
    /// plain atom, so the lattice tracks it via `AtomSet` like any other.
    pub(crate) fn nil() -> Self {
        Self::atom_lit("nil")
    }
    /// fz-yan.2 — `bool` is exactly `:true | :false`. Pre-yan this used
    /// BasicBits::BOOL; runtime-side, both are atom-tagged values, so
    /// the type narrowing matches reality now.
    pub(crate) fn bool_t() -> Self {
        Self::atom_lit("true").union(&Self::atom_lit("false"))
    }
    /// All atom literals (no other axis). Used by VR.5a (typed equality) to
    /// recognise atom-monomorphic operands and lower `==` to a single icmp
    /// without going through fz_value_eq.
    pub(crate) fn atom_top() -> Self {
        let mut d = Self::none();
        d.atoms = AtomSet::any();
        d
    }
    // ---- singletons (atoms / ints / floats / strs) ----

    pub(crate) fn atom_lit(name: impl Into<String>) -> Self {
        let mut d = Self::none();
        d.atoms = AtomSet::lit(name.into());
        d
    }

    /// "any int" — top of the int axis.
    pub(crate) fn int() -> Self {
        let mut d = Self::none();
        d.ints = IntSet::any();
        d
    }
    pub(crate) fn int_lit(n: i64) -> Self {
        let mut d = Self::none();
        d.ints = IntSet::lit(n);
        d
    }

    /// fz-zmu fz-ul4.dce.2 — If this Descr is a pure singleton int (exactly one
    /// integer value with all other type axes empty), return that integer.
    /// Used by ir_fold to detect BinOp results the planner proved to a constant.
    pub(crate) fn as_int_singleton(&self) -> Option<i64> {
        match self.single_component()? {
            Component::Ints(v) => v.singleton(),
            _ => None,
        }
    }

    /// Singleton float. None if any other axis is non-empty or the float
    /// axis isn't a singleton finite set.
    pub(crate) fn as_float_singleton(&self) -> Option<F64Bits> {
        match self.single_component()? {
            Component::Floats(v) => v.singleton(),
            _ => None,
        }
    }

    /// Singleton atom name.
    pub(crate) fn as_atom_singleton(&self) -> Option<&str> {
        match self.single_component()? {
            Component::Atoms(v) => {
                let mut it = v.finite()?;
                let first = it.next()?;
                if it.next().is_none() { Some(first) } else { None }
            }
            _ => None,
        }
    }

    /// fz-swt.6 — singleton opaque tag. Returns `Some(name)` iff this
    /// Descr's only non-empty axis is `opaques` and it names exactly one
    /// qualified opaque type. Consumers (visibility gating, future
    /// `.value` accessor in fz-swt.8) pair this with
    /// `crate::type_expr::opaque_owner_module` to find the declaring
    /// module.
    #[allow(dead_code)] // tests use it now; fz-swt.8 wires it into MapGet typing.
    pub(crate) fn as_opaque_singleton(&self) -> Option<&str> {
        match self.single_component()? {
            Component::Opaques(v) => v.singleton(),
            _ => None,
        }
    }

    /// fz-axu.2 (K1) — singleton brand tag. Returns `Some(name)` iff this
    /// Descr's only non-empty axis is `brands` and it names exactly one
    /// qualified brand. Consumers (K4 visibility gating, K5 erasure)
    /// pair this with `Module.brand_inners` to resolve the underlying
    /// type. Note: a *minted* brand value has both `brands = {name}` AND
    /// the underlying structural axes populated — `as_brand_singleton`
    /// will NOT match those. K4 brand-membership checks use a different
    /// predicate that ignores the structural axes once a brand tag is
    /// present.
    #[allow(dead_code)] // K3 mint typing wires it in.
    pub(crate) fn as_brand_singleton(&self) -> Option<&str> {
        match self.single_component()? {
            Component::Brands(v) => v.singleton(),
            _ => None,
        }
    }

    /// Single-shape tuple: exactly one positive clause with one positive sig
    /// and no negations, and no other axis populated. Returns the element
    /// Descr slice. Elements may be wide — caller decides if it cares.
    pub(crate) fn as_tuple_singleton(&self) -> Option<&[Descr]> {
        match self.single_component()? {
            Component::Tuples(_) => {
                if self.tuples.len() != 1 {
                    return None;
                }
                let conj = &self.tuples[0];
                if !conj.neg.is_empty() || conj.pos.len() != 1 {
                    return None;
                }
                Some(&conj.pos[0].elems)
            }
            _ => None,
        }
    }

    /// Returns the single present Component, or None if zero or more than
    /// one is present. Used by the `as_*_singleton` accessors to enforce
    /// "exactly one axis populated."
    fn single_component(&self) -> Option<Component<'_>> {
        let mut it = self.components();
        let first = it.next()?;
        if it.next().is_some() { None } else { Some(first) }
    }

    /// Max depth of nested Descrs reachable through structural axes. A leaf
    /// (basic, atoms, ints, floats, strs, opaques, vars) has depth 0; a
    /// tuple/list adds 1 to its element depth; a closure_lit adds 1 to its
    /// capture depths. Used by `ConcreteTypes::is_strictly_smaller`.
    pub(crate) fn recursive_spec_depth(&self) -> usize {
        let mut max_d = 0;
        for c in self.components() {
            match c {
                Component::Tuples(view) => {
                    for conj in view.inner {
                        for sig in &conj.pos {
                            for e in &sig.elems {
                                max_d = max_d.max(1 + e.recursive_spec_depth());
                            }
                        }
                    }
                }
                Component::Lists(view) => {
                    for conj in view.inner {
                        for sig in &conj.pos {
                            if let Some(elem) = &sig.elem {
                                max_d = max_d.max(1 + elem.recursive_spec_depth());
                            }
                        }
                    }
                }
                Component::Resources(view) => {
                    for conj in view.inner {
                        for sig in &conj.pos {
                            max_d = max_d.max(1 + sig.payload.recursive_spec_depth());
                        }
                    }
                }
                Component::Funcs(view) => {
                    for conj in view.inner {
                        for sig in &conj.pos {
                            if let Some(lit) = &sig.lit {
                                for cap in &lit.captures {
                                    max_d = max_d.max(1 + ty_descr(cap).recursive_spec_depth());
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        max_d
    }

    /// True iff `self` and `other` share at least one axis on which both
    /// are non-empty (basic bits overlap; literal axes both populated;
    /// structural axes both non-empty). Coarser than `intersect`: it asks
    /// "same KIND?" not "same value?", so it deliberately does NOT fire on
    /// within-axis literal-disjoint pairs (`1` vs `2`, `:ok` vs `:err`).
    /// The dead-binop lint pairs this with `value_disjoint` to flag only
    /// genuinely-cross-kind comparisons (and, post-fz-bsx, to stay quiet on
    /// brand-vs-underlying pairs, which overlap once brands are erased).
    pub(crate) fn kinds_overlap(&self, other: &Descr) -> bool {
        if !self.basic.intersect(other.basic).is_empty() {
            return true;
        }
        for c in self.components() {
            let overlap = match c {
                Component::Basic(_) => false, // handled above
                Component::Atoms(_) => other.components().any(|d| matches!(d, Component::Atoms(_))),
                Component::Ints(_) => other.components().any(|d| matches!(d, Component::Ints(_))),
                Component::Floats(_) => other.components().any(|d| matches!(d, Component::Floats(_))),
                Component::Opaques(_) => other.components().any(|d| matches!(d, Component::Opaques(_))),
                Component::Brands(_) => other.components().any(|d| matches!(d, Component::Brands(_))),
                Component::Vars(_) => other.components().any(|d| matches!(d, Component::Vars(_))),
                Component::Tuples(_) => other.components().any(|d| matches!(d, Component::Tuples(_))),
                Component::Lists(_) => other.components().any(|d| matches!(d, Component::Lists(_))),
                Component::Resources(_) => other.components().any(|d| matches!(d, Component::Resources(_))),
                Component::Funcs(_) => other.components().any(|d| matches!(d, Component::Funcs(_))),
                Component::Maps(_) => other.components().any(|d| matches!(d, Component::Maps(_))),
            };
            if overlap {
                return true;
            }
        }
        false
    }

    /// Returns the largest arity of any positive tuple clause, or 0 if
    /// there are no positive tuple clauses. Used for tuple-field projection
    /// when the field index might exceed some clauses' arities.
    pub(crate) fn max_tuple_arity(&self) -> usize {
        for c in self.components() {
            if let Component::Tuples(view) = c {
                return view.arities().max().unwrap_or(0);
            }
        }
        0
    }

    /// True iff this descriptor extracts to a singleton literal on some
    /// scalar axis (int, atom, float).
    pub(crate) fn is_singleton_literal(&self) -> bool {
        self.as_int_singleton().is_some() || self.as_atom_singleton().is_some() || self.as_float_singleton().is_some()
    }

    /// If this descriptor is a singleton scalar that can serve as a
    /// MapKey (int or atom literal), return it.
    pub(crate) fn as_map_key(&self) -> Option<MapKey> {
        if let Some(n) = self.as_int_singleton() {
            return Some(MapKey::Int(n));
        }
        if let Some(s) = self.as_atom_singleton() {
            return Some(MapKey::Atom(s.to_string()));
        }
        None
    }

    /// Refine every positive map clause so that field `key` has value type
    /// `vt`. Negations and non-map axes are unchanged. Used by the planner
    /// for narrowing under map-pattern matches.
    pub(crate) fn refine_map_field(&self, key: &MapKey, vt: &Descr) -> Descr {
        let mut out = self.clone();
        for clause in &mut out.maps {
            for sig in &mut clause.pos {
                sig.fields.insert(key.clone(), vt.clone());
            }
        }
        out
    }

    /// Widen literal-set axes (ints / floats / strs) to their cofinite top.
    /// Singleton values become their respective universes (`int_lit(42)`
    /// becomes `int()`, etc.); structural axes are untouched.
    ///
    /// Atoms intentionally are NOT widened — atom values are nominal
    /// singletons, not points in a numeric universe; widening them would
    /// erase identity that downstream consumers depend on. Likewise basic,
    /// opaques, and vars (nominal axes).
    ///
    /// For deep widening across nested Descrs inside tuples/lists/funcs/
    /// maps, compose with `map_recursive_spec_key_inputs` and a recursive callback.
    /// Closure-lit captures are intentionally preserved: they are part of
    /// the closure value identity and ABI, not just recursive input shape.
    pub(crate) fn widen_literals(&self) -> Descr {
        let mut out = self.clone();
        if !out.ints.is_none() && !out.ints.is_any() {
            out.ints = IntSet::any();
        }
        if !out.floats.is_none() && !out.floats.is_any() {
            out.floats = FloatSet::any();
        }
        out
    }

    /// Transform toward the recursive spec-key fixed point:
    /// literal-set axes widen to their cofinite tops (`int_lit(42)` ->
    /// `int()`), while structural axes preserve shape and widen nested
    /// Descrs recursively. Atoms remain nominal singletons.
    pub(crate) fn widen_for_recursive_spec_key(&self) -> Descr {
        self.widen_literals()
            .map_recursive_spec_key_inputs(&Descr::widen_for_recursive_spec_key)
    }

    pub(crate) fn refine_widen(&self, other: &Descr) -> Descr {
        fn axis_free(d: &Descr) -> bool {
            d.basic.is_empty()
                && d.atoms.is_none()
                && d.ints.is_none()
                && d.floats.is_none()
                && d.opaques.is_none()
                && d.brands.is_none()
                && d.vars.is_none()
        }

        fn single_positive<'a, T>(clauses: &'a [Conj<T>]) -> Option<&'a T> {
            let [clause] = clauses else {
                return None;
            };
            if !clause.neg.is_empty() {
                return None;
            }
            let [sig] = clause.pos.as_slice() else {
                return None;
            };
            Some(sig)
        }

        fn pure_tuple(d: &Descr) -> Option<&TupleSig> {
            axis_free(d)
                .then_some(())
                .and_then(|_| single_positive(&d.tuples))
                .filter(|_| d.lists.is_empty() && d.resources.is_empty() && d.funcs.is_empty() && d.maps.is_empty())
        }

        fn pure_list(d: &Descr) -> Option<&ListSig> {
            axis_free(d)
                .then_some(())
                .and_then(|_| single_positive(&d.lists))
                .filter(|_| d.tuples.is_empty() && d.resources.is_empty() && d.funcs.is_empty() && d.maps.is_empty())
        }

        fn pure_resource(d: &Descr) -> Option<&ResourceSig> {
            axis_free(d)
                .then_some(())
                .and_then(|_| single_positive(&d.resources))
                .filter(|_| d.tuples.is_empty() && d.lists.is_empty() && d.funcs.is_empty() && d.maps.is_empty())
        }

        fn pure_arrow(d: &Descr) -> Option<&ArrowSig> {
            axis_free(d)
                .then_some(())
                .and_then(|_| single_positive(&d.funcs))
                .filter(|_| d.tuples.is_empty() && d.lists.is_empty() && d.resources.is_empty() && d.maps.is_empty())
        }

        fn pure_map(d: &Descr) -> Option<&MapSig> {
            axis_free(d)
                .then_some(())
                .and_then(|_| single_positive(&d.maps))
                .filter(|_| d.tuples.is_empty() && d.lists.is_empty() && d.resources.is_empty() && d.funcs.is_empty())
        }

        if let (Some(lhs), Some(rhs)) = (pure_tuple(self), pure_tuple(other))
            && lhs.elems.len() == rhs.elems.len()
        {
            return Descr::tuple_of(lhs.elems.iter().zip(rhs.elems.iter()).map(|(l, r)| l.refine_widen(r)));
        }

        if let (Some(lhs), Some(rhs)) = (pure_list(self), pure_list(other)) {
            let elem = match (&lhs.elem, &rhs.elem) {
                (Some(l), Some(r)) => Some(Box::new(l.refine_widen(r))),
                (Some(l), None) => Some(l.clone()),
                (None, Some(r)) => Some(r.clone()),
                (None, None) => None,
            };
            return match elem {
                Some(elem) => Descr {
                    lists: vec![Conj::pos_of(ListSig {
                        empty: lhs.empty || rhs.empty,
                        elem: Some(elem),
                    })],
                    ..Descr::none()
                },
                None => Descr::empty_list(),
            };
        }

        if let (Some(lhs), Some(rhs)) = (pure_resource(self), pure_resource(other)) {
            return Descr::resource_of(lhs.payload.refine_widen(&rhs.payload));
        }

        if let (Some(lhs), Some(rhs)) = (pure_arrow(self), pure_arrow(other))
            && lhs.args.len() == rhs.args.len()
        {
            return Descr::arrow(
                lhs.args.iter().zip(rhs.args.iter()).map(|(l, r)| l.union(r)),
                lhs.ret.refine_widen(&rhs.ret),
            );
        }

        if let (Some(lhs), Some(rhs)) = (pure_map(self), pure_map(other)) {
            let mut fields = lhs.fields.clone();
            for (key, rv) in &rhs.fields {
                fields
                    .entry(key.clone())
                    .and_modify(|lv| *lv = lv.refine_widen(rv))
                    .or_insert_with(|| rv.clone());
            }
            return Descr {
                maps: vec![Conj::pos_of(MapSig { fields })],
                ..Descr::none()
            };
        }

        self.union(other).widen_for_recursive_spec_key()
    }

    /// Erase closure-literal identity while preserving callable surface shape.
    /// Unlike recursive-key widening, this deliberately drops `ClosureLit`
    /// tags so higher-order fixed-point slots do not fork on wrapper identity.
    pub(crate) fn erase_closure_identity(&self) -> Descr {
        let map_tuple_sig = |s: TupleSig| TupleSig {
            elems: s.elems.iter().map(Descr::erase_closure_identity).collect(),
        };
        let map_list_sig = |s: ListSig| ListSig {
            empty: s.empty,
            elem: s.elem.as_ref().map(|elem| Box::new(elem.erase_closure_identity())),
        };
        let map_resource_sig = |s: ResourceSig| ResourceSig {
            payload: Box::new(s.payload.erase_closure_identity()),
        };
        let map_arrow_sig = |s: ArrowSig| ArrowSig {
            args: s.args.iter().map(Descr::erase_closure_identity).collect(),
            ret: Box::new(s.ret.erase_closure_identity()),
            lit: None,
        };
        let map_map_sig = |s: MapSig| MapSig {
            fields: s
                .fields
                .into_iter()
                .map(|(k, v)| (k, v.erase_closure_identity()))
                .collect(),
        };
        let mut out = self.clone();
        out.tuples = out
            .tuples
            .iter()
            .cloned()
            .map(|conj| Conj {
                pos: conj.pos.into_iter().map(&map_tuple_sig).collect(),
                neg: conj.neg.into_iter().map(&map_tuple_sig).collect(),
            })
            .collect();
        out.lists = out
            .lists
            .iter()
            .cloned()
            .map(|conj| Conj {
                pos: conj.pos.into_iter().map(&map_list_sig).collect(),
                neg: conj.neg.into_iter().map(&map_list_sig).collect(),
            })
            .collect();
        out.resources = out
            .resources
            .iter()
            .cloned()
            .map(|conj| Conj {
                pos: conj.pos.into_iter().map(&map_resource_sig).collect(),
                neg: conj.neg.into_iter().map(&map_resource_sig).collect(),
            })
            .collect();
        out.funcs = out
            .funcs
            .iter()
            .cloned()
            .map(|conj| Conj {
                pos: conj.pos.into_iter().map(&map_arrow_sig).collect(),
                neg: conj.neg.into_iter().map(&map_arrow_sig).collect(),
            })
            .collect();
        out.maps = out
            .maps
            .iter()
            .cloned()
            .map(|conj| Conj {
                pos: conj.pos.into_iter().map(&map_map_sig).collect(),
                neg: conj.neg.into_iter().map(&map_map_sig).collect(),
            })
            .collect();
        out
    }

    pub(crate) fn alpha_normalize_vars(&self) -> Descr {
        fn mapped_id(old: TypeVarId, sigma: &mut BTreeMap<TypeVarId, TypeVarId>, next: &mut u32) -> TypeVarId {
            if let Some(mapped) = sigma.get(&old) {
                return *mapped;
            }
            let fresh = TypeVarId(*next);
            *next += 1;
            sigma.insert(old, fresh);
            fresh
        }

        fn map_tuple_sig(s: TupleSig, sigma: &mut BTreeMap<TypeVarId, TypeVarId>, next: &mut u32) -> TupleSig {
            TupleSig {
                elems: s.elems.iter().map(|elem| go(elem, sigma, next)).collect(),
            }
        }

        fn map_list_sig(s: ListSig, sigma: &mut BTreeMap<TypeVarId, TypeVarId>, next: &mut u32) -> ListSig {
            ListSig {
                empty: s.empty,
                elem: s.elem.as_ref().map(|elem| Box::new(go(elem, sigma, next))),
            }
        }

        fn map_resource_sig(s: ResourceSig, sigma: &mut BTreeMap<TypeVarId, TypeVarId>, next: &mut u32) -> ResourceSig {
            ResourceSig {
                payload: Box::new(go(&s.payload, sigma, next)),
            }
        }

        fn map_arrow_sig(s: ArrowSig, sigma: &mut BTreeMap<TypeVarId, TypeVarId>, next: &mut u32) -> ArrowSig {
            ArrowSig {
                args: s.args.iter().map(|arg| go(arg, sigma, next)).collect(),
                ret: Box::new(go(&s.ret, sigma, next)),
                lit: s.lit.map(|lit| ClosureLit {
                    fn_id: lit.fn_id,
                    captures: lit
                        .captures
                        .into_iter()
                        .map(|capture| ty_from_descr(go(ty_descr(&capture), sigma, next)))
                        .collect(),
                }),
            }
        }

        fn map_map_sig(s: MapSig, sigma: &mut BTreeMap<TypeVarId, TypeVarId>, next: &mut u32) -> MapSig {
            MapSig {
                fields: s.fields.into_iter().map(|(k, v)| (k, go(&v, sigma, next))).collect(),
            }
        }

        fn go(d: &Descr, sigma: &mut BTreeMap<TypeVarId, TypeVarId>, next: &mut u32) -> Descr {
            let mut out = d.clone();
            if !out.vars.is_any() {
                out.vars.set = out
                    .vars
                    .set
                    .iter()
                    .copied()
                    .map(|id| mapped_id(id, sigma, next))
                    .collect();
            }
            out.tuples = out
                .tuples
                .iter()
                .cloned()
                .map(|conj| Conj {
                    pos: conj
                        .pos
                        .into_iter()
                        .map(|sig| map_tuple_sig(sig, sigma, next))
                        .collect(),
                    neg: conj
                        .neg
                        .into_iter()
                        .map(|sig| map_tuple_sig(sig, sigma, next))
                        .collect(),
                })
                .collect();
            out.lists = out
                .lists
                .iter()
                .cloned()
                .map(|conj| Conj {
                    pos: conj.pos.into_iter().map(|sig| map_list_sig(sig, sigma, next)).collect(),
                    neg: conj.neg.into_iter().map(|sig| map_list_sig(sig, sigma, next)).collect(),
                })
                .collect();
            out.resources = out
                .resources
                .iter()
                .cloned()
                .map(|conj| Conj {
                    pos: conj
                        .pos
                        .into_iter()
                        .map(|sig| map_resource_sig(sig, sigma, next))
                        .collect(),
                    neg: conj
                        .neg
                        .into_iter()
                        .map(|sig| map_resource_sig(sig, sigma, next))
                        .collect(),
                })
                .collect();
            out.funcs = out
                .funcs
                .iter()
                .cloned()
                .map(|conj| Conj {
                    pos: conj
                        .pos
                        .into_iter()
                        .map(|sig| map_arrow_sig(sig, sigma, next))
                        .collect(),
                    neg: conj
                        .neg
                        .into_iter()
                        .map(|sig| map_arrow_sig(sig, sigma, next))
                        .collect(),
                })
                .collect();
            out.maps = out
                .maps
                .iter()
                .cloned()
                .map(|conj| Conj {
                    pos: conj.pos.into_iter().map(|sig| map_map_sig(sig, sigma, next)).collect(),
                    neg: conj.neg.into_iter().map(|sig| map_map_sig(sig, sigma, next)).collect(),
                })
                .collect();
            out
        }

        go(self, &mut BTreeMap::new(), &mut 0)
    }

    /// Apply `f` to nested `Descr`s that are recursive input shape:
    /// tuple elements, list element, arrow args/ret, and map values.
    /// Closure-lit captures are kept intact because they identify the
    /// concrete closure value.
    ///
    /// Consuming receiver to avoid an extra clone when composed with
    /// `widen_literals` (typical caller:
    /// `d.widen_literals().map_recursive_spec_key_inputs(...)`).
    pub(crate) fn map_recursive_spec_key_inputs(mut self, f: &impl Fn(&Descr) -> Descr) -> Descr {
        let map_tuple_sig = |s: TupleSig| TupleSig {
            elems: s.elems.iter().map(f).collect(),
        };
        let map_list_sig = |s: ListSig| ListSig {
            empty: s.empty,
            elem: s.elem.as_ref().map(|elem| Box::new(f(elem))),
        };
        let map_resource_sig = |s: ResourceSig| ResourceSig {
            payload: Box::new(f(&s.payload)),
        };
        let map_arrow_sig = |s: ArrowSig| ArrowSig {
            args: s.args.iter().map(f).collect(),
            ret: Box::new(f(&s.ret)),
            lit: s.lit.map(|l| ClosureLit {
                fn_id: l.fn_id,
                captures: l.captures,
            }),
        };
        let map_map_sig = |s: MapSig| MapSig {
            fields: s.fields.into_iter().map(|(k, v)| (k, f(&v))).collect(),
        };
        self.tuples = self
            .tuples
            .into_iter()
            .map(|c| Conj {
                pos: c.pos.into_iter().map(map_tuple_sig).collect(),
                neg: c.neg.into_iter().map(map_tuple_sig).collect(),
            })
            .collect();
        self.lists = self
            .lists
            .into_iter()
            .map(|c| Conj {
                pos: c.pos.into_iter().map(map_list_sig).collect(),
                neg: c.neg.into_iter().map(map_list_sig).collect(),
            })
            .collect();
        self.resources = self
            .resources
            .into_iter()
            .map(|c| Conj {
                pos: c.pos.into_iter().map(map_resource_sig).collect(),
                neg: c.neg.into_iter().map(map_resource_sig).collect(),
            })
            .collect();
        self.funcs = self
            .funcs
            .into_iter()
            .map(|c| Conj {
                pos: c.pos.into_iter().map(map_arrow_sig).collect(),
                neg: c.neg.into_iter().map(map_arrow_sig).collect(),
            })
            .collect();
        self.maps = self
            .maps
            .into_iter()
            .map(|c| Conj {
                pos: c.pos.into_iter().map(map_map_sig).collect(),
                neg: c.neg.into_iter().map(map_map_sig).collect(),
            })
            .collect();
        self
    }

    pub(crate) fn str_t() -> Self {
        Self::from_basic(BasicBits::BINARY)
    }

    pub(crate) fn resource_of(payload: Descr) -> Self {
        if payload.is_empty() {
            return Self::none();
        }
        let mut d = Self::none();
        d.resources = vec![Conj::pos_of(ResourceSig {
            payload: Box::new(payload),
        })];
        d
    }

    pub(crate) fn float() -> Self {
        let mut d = Self::none();
        d.floats = FloatSet::any();
        d
    }
    pub(crate) fn float_lit(f: f64) -> Self {
        let mut d = Self::none();
        d.floats = FloatSet::lit(F64Bits::new(f));
        d
    }

    // ---- structurals (single positive clause each — composition lands in fz-ul4.2) ----

    pub(crate) fn tuple_of(elems: impl IntoIterator<Item = Descr>) -> Self {
        let sig = TupleSig {
            elems: elems.into_iter().collect(),
        };
        let mut d = Self::none();
        d.tuples.push(Conj::pos_of(sig));
        d
    }

    pub(crate) fn list_of(elem: Descr) -> Self {
        let mut d = Self::none();
        d.lists.push(Conj::pos_of(ListSig::possibly_empty(elem)));
        d
    }

    pub(crate) fn non_empty_list_of(elem: Descr) -> Self {
        let mut d = Self::none();
        if let Some(sig) = ListSig::non_empty(elem) {
            d.lists.push(Conj::pos_of(sig));
        }
        d
    }

    pub(crate) fn empty_list() -> Self {
        let mut d = Self::none();
        d.lists.push(Conj::pos_of(ListSig::empty()));
        d
    }

    pub(crate) fn arrow(args: impl IntoIterator<Item = Descr>, ret: Descr) -> Self {
        let sig = ArrowSig {
            args: args.into_iter().collect(),
            ret: Box::new(ret),
            lit: None,
        };
        let mut d = Self::none();
        d.funcs.push(Conj::pos_of(sig));
        d
    }

    /// fz-ul4.27.22.8 — closure-literal singleton: the specific closure
    /// constructed by `MakeClosure(fn_id, [vars typed as `captures`])`.
    /// `n_args` is the post-capture apparent arity (i.e., the closure's
    /// remaining param count once captures are bound). The arrow's `args`
    /// and `ret` start as `any` placeholders; consumers refine them by
    /// looking up `fn_id`'s spec at the matching key (see 22.9's
    /// `resolve_closure_return`).
    #[allow(dead_code)] // Used by unit tests now; production callers land in fz-ul4.27.22.10.
    pub(crate) fn closure_lit(fn_id: FnId, captures: Vec<Descr>, n_args: usize) -> Self {
        // fz-try.7 — type variables at the closure's surface signature
        // instead of `Descr::any()` stubs. The arrow becomes `(α₀, …, αₙ₋₁) -> β`
        // where each αᵢ and β are *deterministic* ids derived from `fn_id`
        // and position. Determinism is load-bearing: re-typing the same
        // MakeClosure during fixpoint iteration must produce the same Descr,
        // or convergence fails. Two distinct closure-handles of the same
        // lambda (same fn_id, different captures) share their vars by
        // construction — they are parametric over the same body.
        //
        // The principle from fz-try.5 lives here: vars are nominal placeholders
        // the lattice cannot distinguish from opaques; the *substitution
        // contract* at call sites is what gives them meaning. Built by
        // closure_lit, consumed by resolve_closure_return via instantiate.
        let arg_var = |pos: usize| Descr::var(closure_var_id(fn_id, pos));
        let ret_var = Descr::var(closure_ret_var_id(fn_id));
        let sig = ArrowSig {
            args: (0..n_args).map(arg_var).collect(),
            ret: Box::new(ret_var),
            lit: Some(ClosureLit {
                fn_id,
                captures: captures.into_iter().map(ty_from_descr).collect(),
            }),
        };
        let mut d = Self::none();
        d.funcs.push(Conj::pos_of(sig));
        d
    }

    /// fz-ul4.27.22.8 — if this Descr is a single positive closure-literal
    /// arrow clause, return its `ClosureLit` tag. Returns `None` for
    /// non-singleton shapes (unions, lit-free arrows, negated arrows).
    /// Downstream consumers (22.9+) use this to decide whether per-callsite
    /// specialization can take the singleton-fast path.
    #[allow(dead_code)] // Used by unit tests now; production callers land in fz-ul4.27.22.10/11.
    pub(crate) fn as_closure_lit(&self) -> Option<&ClosureLit> {
        if self.funcs.len() != 1 {
            return None;
        }
        let c = &self.funcs[0];
        if !c.neg.is_empty() || c.pos.len() != 1 {
            return None;
        }
        c.pos[0].lit.as_ref()
    }

    /// Top of the map axis: any map.
    pub(crate) fn map_top() -> Self {
        let mut d = Self::none();
        d.maps.push(Conj::top());
        d
    }

    /// Open-shape map type with the given required (key, value-type) pairs.
    pub(crate) fn map_of(fields: impl IntoIterator<Item = (MapKey, Descr)>) -> Self {
        let sig = MapSig {
            fields: fields.into_iter().collect(),
        };
        let mut d = Self::none();
        d.maps.push(Conj::pos_of(sig));
        d
    }

    // ---- recognizers ----

    pub(crate) fn looks_empty(&self) -> bool {
        self.basic.is_empty()
            && self.atoms.is_none()
            && self.ints.is_none()
            && self.floats.is_none()
            && self.opaques.is_none()
            && self.brands.is_none()
            && self.vars.is_none()
            && self.tuples.is_empty()
            && self.lists.is_empty()
            && self.resources.is_empty()
            && self.funcs.is_empty()
            && self.maps.is_empty()
    }

    /// fz-ul4.27.22.6 — JOIN of return Descrs across all positive arrow
    /// clauses in this Descr's funcs axis. Used at the CallClosure seam:
    /// the closure's static callable Descr names the body's possible
    /// return shapes, and the cont's slot-0 Descr is the union of those.
    ///
    /// Returns `Descr::any()` when funcs contains any `Conj::top()`
    /// (saturated arrow — body could return anything), any clause with
    /// negative arrows (which can broaden what the clause accepts in
    /// ways not captured by positive returns alone), or is empty.
    pub(crate) fn arrow_join_return(&self) -> Descr {
        if self.funcs.is_empty() {
            return Descr::any();
        }
        let mut acc = Descr::none();
        for c in &self.funcs {
            if !c.neg.is_empty() || c.pos.is_empty() {
                return Descr::any();
            }
            for sig in &c.pos {
                acc = acc.union(&sig.ret);
            }
        }
        acc
    }

    pub(crate) fn looks_full(&self) -> bool {
        self.basic == BasicBits::ALL
            && self.atoms.is_any()
            && self.ints.is_any()
            && self.floats.is_any()
            && self.opaques.is_any()
            && self.brands.is_any()
            && self.vars.is_any()
            && is_dnf_top(&self.tuples)
            && is_dnf_top(&self.lists)
            && is_dnf_top(&self.resources)
            && is_dnf_top(&self.funcs)
            && is_dnf_top(&self.maps)
    }

    // ---- operations ----

    pub(crate) fn union(&self, other: &Descr) -> Descr {
        let tuples = dnf_union(&self.tuples, &other.tuples);
        let lists = normalize_empty_nonempty_list_unions(dnf_union(&self.lists, &other.lists));
        let resources = dnf_union(&self.resources, &other.resources);
        let funcs = dnf_union(&self.funcs, &other.funcs);
        let maps = dnf_union(&self.maps, &other.maps);
        // fz-et8 — drop semantically-subsumed clauses. Sound by absorption
        // (`A ⊆ B ⇒ A ∨ B = B`). Per-axis: a single-clause Descr on the
        // same axis is the witness Descr for subsumption.
        let tuples = subsumption_dedup(tuples, |c| Descr {
            tuples: vec![c.clone()],
            ..Descr::none()
        });
        let lists = subsumption_dedup(lists, |c| Descr {
            lists: vec![c.clone()],
            ..Descr::none()
        });
        let resources = subsumption_dedup(resources, |c| Descr {
            resources: vec![c.clone()],
            ..Descr::none()
        });
        let funcs = subsumption_dedup(funcs, |c| Descr {
            funcs: vec![c.clone()],
            ..Descr::none()
        });
        let maps = subsumption_dedup(maps, |c| Descr {
            maps: vec![c.clone()],
            ..Descr::none()
        });
        Descr {
            basic: self.basic.union(other.basic),
            atoms: self.atoms.union(&other.atoms),
            ints: self.ints.union(&other.ints),
            floats: self.floats.union(&other.floats),
            opaques: self.opaques.union(&other.opaques),
            brands: self.brands.union(&other.brands),
            vars: self.vars.union(&other.vars),
            tuples,
            lists,
            resources,
            funcs,
            maps,
        }
    }

    pub(crate) fn intersect(&self, other: &Descr) -> Descr {
        Descr {
            basic: self.basic.intersect(other.basic),
            atoms: self.atoms.intersect(&other.atoms),
            ints: self.ints.intersect(&other.ints),
            floats: self.floats.intersect(&other.floats),
            opaques: self.opaques.intersect(&other.opaques),
            brands: self.brands.intersect(&other.brands),
            vars: self.vars.intersect(&other.vars),
            tuples: dnf_intersect(&self.tuples, &other.tuples),
            lists: dnf_intersect(&self.lists, &other.lists),
            resources: dnf_intersect(&self.resources, &other.resources),
            funcs: dnf_intersect(&self.funcs, &other.funcs),
            maps: dnf_intersect(&self.maps, &other.maps),
        }
    }

    pub(crate) fn neg(&self) -> Descr {
        Descr {
            basic: self.basic.neg(),
            atoms: self.atoms.neg(),
            ints: self.ints.neg(),
            floats: self.floats.neg(),
            opaques: self.opaques.neg(),
            brands: self.brands.neg(),
            vars: self.vars.neg(),
            tuples: dnf_neg(&self.tuples),
            lists: dnf_neg(&self.lists),
            resources: dnf_neg(&self.resources),
            funcs: dnf_neg(&self.funcs),
            maps: dnf_neg(&self.maps),
        }
    }

    pub(crate) fn diff(&self, other: &Descr) -> Descr {
        self.intersect(&other.neg())
    }

    // ----------------------------------------------------------------
    // Semantic emptiness / subtyping
    // ----------------------------------------------------------------

    /// Is this descriptor the empty set of values?
    ///
    /// The kernel of semantic subtyping: `T <: U` iff `is_empty(T ∧ ¬U)`.
    /// Recurses through structural element types; coinductive for recursive
    /// shapes via a memoized in-flight stack (greatest fixpoint).
    pub(crate) fn is_empty(&self) -> bool {
        let mut memo = Memo::default();
        self.is_empty_memo(&mut memo)
    }

    /// `self <: other` iff `(self ∧ ¬other)` is empty.
    pub(crate) fn is_subtype(&self, other: &Descr) -> bool {
        self.diff(other).is_empty()
    }

    /// fz-axu.5 (K4) — brand-aware subtype check. Resolves every brand
    /// tag in `self.brands` against `brand_inners` to discharge those
    /// that fit structurally into `other`. Then runs the standard
    /// `is_subtype` on the discharged Descr.
    ///
    /// The rule that this ratifies: `brand_value: brands={B} ∧ T` is a
    /// subtype of `T'` whenever `brand_inners[B] <: T'` AND the
    /// structural axes of the value satisfy `<: T'`. The brand tag is a
    /// label, not a membership barrier — once the inner accepts T', the
    /// label is irrelevant for the comparison.
    ///
    /// `is_subtype` (no inners) is conservative: it treats brand tags
    /// as a hard axis, so the value-fully-tagged ⊆ untagged-type case
    /// returns false. Use `is_subtype_under` whenever a Module context
    /// is available (the planner, codegen, spec dispatch).
    pub(crate) fn is_subtype_under(&self, other: &Descr, brand_inners: &HashMap<String, Descr>) -> bool {
        // Rule (i): if `other` names specific brand tags as required,
        // `self` must already carry one. A bare-structural value
        // (`brands=none`) cannot satisfy a brand-restricted target —
        // the standard `is_subtype` misses this because the brands
        // axis collapses to "none" in the diff. K4 reinstates it.
        if other.brands.requires_tag() && self.brands.is_none() {
            return false;
        }
        if self.brands.is_none() || self.brands.cofinite {
            // No finite brand tags to discharge (none / "any brand").
            return self.is_subtype(other);
        }
        // Rule (ii): for each finite tag whose inner ⊆ other, discharge
        // it. If every tag is dischargeable, drop the brands axis
        // entirely for the comparison so the standard lattice no
        // longer trips on the brand-axis mismatch.
        let mut remaining = self.brands.clone();
        let tags: Vec<String> = remaining.set.iter().cloned().collect();
        for tag in &tags {
            if let Some(inner) = brand_inners.get(tag)
                && inner.is_subtype(other)
            {
                remaining.set.remove(tag);
            }
        }
        let mut adjusted = self.clone();
        adjusted.brands = remaining;
        adjusted.is_subtype(other)
    }

    /// fz-axu.5 (K4) — brand-aware equivalence: mutual `is_subtype_under`.
    #[allow(dead_code)] // wiring lands in downstream tickets that use it.
    pub(crate) fn is_equiv_under(&self, other: &Descr, brand_inners: &HashMap<String, Descr>) -> bool {
        self == other || (self.is_subtype_under(other, brand_inners) && other.is_subtype_under(self, brand_inners))
    }

    /// Mutual subtyping.
    ///
    /// Structural equality is a sufficient (not necessary) condition for
    /// semantic equivalence — two `Descr` values with identical fields
    /// denote the same set, so `self == other` short-circuits the
    /// set-theoretic kernel. Misses fall through to the slow path.
    pub(crate) fn is_equiv(&self, other: &Descr) -> bool {
        self == other || (self.is_subtype(other) && other.is_subtype(self))
    }

    /// fz-bsx.1 — discharge every brand and opaque tag to its underlying
    /// representation type, recursively through nested structural positions.
    /// The result is the *runtime representation* of `self`: what the machine
    /// actually sees once `ir_brand_erase` has stripped the zero-cost brand /
    /// opaque wrappers and `fz_value_eq` compares by structure / bytes.
    ///
    /// This is the model in which runtime equality and pattern matching are
    /// decided — both are brand-blind. It is the deliberate counterpart of
    /// `is_subtype` / `intersect` (brand-AWARE), which answer typing /
    /// dispatch / boundary questions where brands must still count.
    ///
    /// A minted brand value is a *pure tag* (`brands = {B}`, all structural
    /// axes empty — see `brand_of`), so a tag must be *replaced* by its inner
    /// (`brand_inners[B]`), not merely cleared — clearing would collapse it to
    /// `none`. Unknown tags and cofinite ("any brand") axes over-approximate
    /// to `any()`, so the erased set is never too small; `value_disjoint`
    /// then errs toward "not disjoint" and never folds a comparison unsoundly.
    pub(crate) fn erase_nominal(&self, nominals: Nominals<'_, Descr>) -> Descr {
        let mut d = self.clone();
        let brands = replace(&mut d.brands, LiteralSet::none());
        let opaques = replace(&mut d.opaques, LiteralSet::none());
        for (tags, inners) in [(&brands, nominals.brand_inners), (&opaques, nominals.opaque_inners)] {
            if tags.is_none() {
                continue;
            }
            if tags.cofinite {
                // "Any brand" (or a cofinite exclusion): the represented set
                // spans every underlying type. Over-approximate to `any()`.
                d = d.union(&Descr::any());
                continue;
            }
            for tag in &tags.set {
                match inners.get(tag) {
                    Some(inner) => {
                        d = d.union(&inner.erase_nominal(nominals));
                    }
                    // Unknown tag: be conservative rather than collapse to none.
                    None => d = d.union(&Descr::any()),
                }
            }
        }
        // Recurse into nested input positions (tuple elems, list elem, arrow
        // args/ret, map values, resource payload) so a brand nested inside a
        // tuple — the original fz-bsx failure — is discharged too.
        d.map_recursive_spec_key_inputs(&|x| x.erase_nominal(nominals))
    }

    /// fz-bsx.1 — true iff no two runtime values of these types can ever be
    /// equal / match: disjointness in the brand-erased (representation) model.
    /// This is the ONLY disjointness that may authorize folding `==`/`!=` to a
    /// constant or pruning a pattern arm. Contrast `intersect(..).is_empty()`
    /// (brand-aware) used for typing decisions.
    pub(crate) fn value_disjoint(&self, other: &Descr, nominals: Nominals<'_, Descr>) -> bool {
        self.erase_nominal(nominals)
            .intersect(&other.erase_nominal(nominals))
            .is_empty()
    }

    pub(super) fn is_empty_memo(&self, memo: &mut Memo) -> bool {
        if memo.in_flight.contains(self) {
            // Coinductive assumption: re-entering the same query along this
            // recursive descent. Greatest-fixpoint reading says "yes, empty"
            // is consistent until proven otherwise.
            return true;
        }
        memo.in_flight.insert(self.clone());

        let result = self.basic.is_empty()
            && self.atoms.is_none()
            && self.ints.is_none()
            && self.floats.is_none()
            && self.opaques.is_none()
            && self.brands.is_none()
            && self.vars.is_none()
            && self.tuples.iter().all(|c| tuple_clause_empty(c, memo))
            && self.lists.iter().all(|c| list_clause_empty(c, memo))
            && self.resources.iter().all(|c| resource_clause_empty(c, memo))
            && self.funcs.iter().all(|c| func_clause_empty(c, memo))
            && self.maps.iter().all(|c| map_clause_empty(c, memo));

        memo.in_flight.remove(self);
        result
    }
}

// ---- diagnostic + capped display (was a separate impl block in the
// original file; kept distinct here too so callers can still find it
// by sight) ----

impl Descr {
    /// Render this type for user-facing diagnostic prose. Caps each
    /// literal-set axis at 5 members + an ellipsis so a huge int-literal
    /// union doesn't crowd a `= note:` line. The canonical `Display`
    /// impl above stays exact (tests rely on it).
    pub(crate) fn display_for_diag(&self) -> String {
        const CAP: usize = 5;
        if self.looks_full() {
            return "any".into();
        }
        if self.looks_empty() {
            return "none".into();
        }

        let mut parts: Vec<String> = Vec::new();

        for (bit, name) in BASIC_NAMES {
            if self.basic.contains_all(*bit) {
                parts.push((*name).to_string());
            }
        }

        format_lit_set_capped(&mut parts, &self.ints, "int", CAP, |n| format!("{}", n));
        format_lit_set_capped(&mut parts, &self.floats, "float", CAP, |f| format!("{}", f.get()));
        if let Some(s) = render_reserved_atom_set(&self.atoms) {
            parts.push(s);
        } else {
            format_lit_set_capped(&mut parts, &self.atoms, "atom", CAP, |a| format!(":{}", a));
        }
        format_lit_set_capped(&mut parts, &self.opaques, "opaque", CAP, |n| n.clone());
        format_lit_set_capped(&mut parts, &self.brands, "brand", CAP, |n| n.clone());
        format_lit_set_capped(&mut parts, &self.vars, "var", CAP, |v| format!("{}", v));

        for c in &self.tuples {
            parts.push(format_tuple_clause(c));
        }
        for c in &self.lists {
            parts.push(format_list_clause(c));
        }
        for c in &self.resources {
            parts.push(format_resource_clause(c));
        }
        for c in &self.funcs {
            parts.push(format_arrow_clause(c));
        }
        for c in &self.maps {
            parts.push(format_map_clause(c));
        }

        parts.join(" | ")
    }
}

// ---- Component iterator + type_test helpers (was at end of original
// file; lives with Descr so its inherent methods stay grouped). ----

impl Descr {
    /// Iterate the present components of this descriptor. An axis is
    /// "present" iff it is non-empty (matches Elixir's sparse-map
    /// convention). `Descr::any()` yields one component per axis;
    /// `Descr::none()` yields none.
    ///
    /// The order is canonical (basic, atoms, ints, floats, strs,
    /// opaques, vars, tuples, lists, resources, funcs, maps) but consumers should
    /// `match` rather than rely on order.
    pub(crate) fn components(&self) -> impl Iterator<Item = Component<'_>> + '_ {
        let basic = (!self.basic.is_empty()).then_some(Component::Basic(self.basic));
        let atoms = (!self.atoms.is_none()).then_some(Component::Atoms(AtomView { inner: &self.atoms }));
        let ints = (!self.ints.is_none()).then_some(Component::Ints(IntView { inner: &self.ints }));
        let floats = (!self.floats.is_none()).then_some(Component::Floats(FloatView { inner: &self.floats }));
        let opaques = (!self.opaques.is_none()).then_some(Component::Opaques(OpaqueView { inner: &self.opaques }));
        let brands = (!self.brands.is_none()).then_some(Component::Brands(BrandView { inner: &self.brands }));
        let vars = (!self.vars.is_none()).then_some(Component::Vars(VarView { inner: &self.vars }));
        let tuples = (!self.tuples.is_empty()).then_some(Component::Tuples(TupleView { inner: &self.tuples }));
        let lists = (!self.lists.is_empty()).then_some(Component::Lists(ListView { inner: &self.lists }));
        let resources =
            (!self.resources.is_empty()).then_some(Component::Resources(ResourceView { inner: &self.resources }));
        let funcs = (!self.funcs.is_empty()).then_some(Component::Funcs(FuncView { inner: &self.funcs }));
        let maps = (!self.maps.is_empty()).then_some(Component::Maps(MapView { inner: &self.maps }));
        [
            basic, atoms, ints, floats, opaques, brands, vars, tuples, lists, resources, funcs, maps,
        ]
        .into_iter()
        .flatten()
    }

    pub(crate) fn type_test_has_ints(&self) -> bool {
        self.components()
            .any(|component| matches!(component, Component::Ints(_)))
    }

    pub(crate) fn type_test_atoms(&self) -> AtomTypeTest {
        self.components()
            .find_map(|component| match component {
                Component::Atoms(view) => Some(if view.is_any() {
                    AtomTypeTest::Any
                } else if view.cofinite() {
                    AtomTypeTest::Cofinite
                } else {
                    AtomTypeTest::Finite(
                        view.finite()
                            .expect("finite (non-cofinite)")
                            .map(String::from)
                            .collect(),
                    )
                }),
                _ => None,
            })
            .unwrap_or(AtomTypeTest::None)
    }

    pub(crate) fn type_test_atom_is_any(&self) -> bool {
        matches!(self.type_test_atoms(), AtomTypeTest::Any)
    }

    pub(crate) fn type_test_atom_is_cofinite(&self) -> bool {
        matches!(self.type_test_atoms(), AtomTypeTest::Cofinite)
    }

    pub(crate) fn type_test_atom_literals(&self) -> Vec<String> {
        match self.type_test_atoms() {
            AtomTypeTest::Finite(names) => names,
            AtomTypeTest::None | AtomTypeTest::Any | AtomTypeTest::Cofinite => Vec::new(),
        }
    }

    pub(crate) fn type_test_has_floats(&self) -> bool {
        self.components()
            .any(|component| matches!(component, Component::Floats(_)))
    }

    /// True iff this type includes some list. Kind-level (matches Elixir's
    /// `is_list`): the list element type is not tested at runtime, so a
    /// `list(int)` descriptor matches any list value. Protocol-dispatch arms
    /// always test `list(any)`, so this is exactly the right granularity.
    pub(crate) fn type_test_has_lists(&self) -> bool {
        self.components()
            .any(|component| matches!(component, Component::Lists(_)))
    }

    /// True iff this type includes some map. Kind-level, like
    /// [`Self::type_test_has_lists`].
    pub(crate) fn type_test_has_maps(&self) -> bool {
        self.components()
            .any(|component| matches!(component, Component::Maps(_)))
    }

    /// True iff this type includes a binary. The binary kind lives on the
    /// `basic` axis, so a non-empty basic component is a binary.
    pub(crate) fn type_test_has_binaries(&self) -> bool {
        self.components()
            .any(|component| matches!(component, Component::Basic(_)))
    }

    pub(crate) fn type_test_tuple_has_negations(&self) -> bool {
        self.components()
            .find_map(|component| match component {
                Component::Tuples(view) => Some(view.has_negations()),
                _ => None,
            })
            .unwrap_or(false)
    }

    pub(crate) fn type_test_tuple_arities(&self) -> Vec<usize> {
        let mut arities = self
            .components()
            .find_map(|component| match component {
                Component::Tuples(view) => Some(view.arities().collect::<Vec<_>>()),
                _ => None,
            })
            .unwrap_or_default();
        arities.sort_unstable();
        arities.dedup();
        arities
    }

    pub(crate) fn type_test_struct_names(&self) -> Vec<String> {
        const PREFIX: &str = "impl-target::";
        if self.opaques.cofinite {
            return Vec::new();
        }
        self.opaques
            .set
            .iter()
            .filter_map(|name| name.strip_prefix(PREFIX).map(String::from))
            .collect()
    }
}
