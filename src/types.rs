//! Set-theoretic type descriptors.
//!
//! A `Descr` represents a set of values. The lattice has top (`any` — every
//! value) and bottom (`none` — no value), and is closed under union,
//! intersection, and complement.
//!
//! Representation follows Castagna 2024 / Frisch-Castagna-Benzaken 2008 and
//! mirrors the shape of Elixir's `Module.Types.Descr`:
//!
//!   Descr = bitmap of basic types
//!         ∪ set of atom literals (finite OR cofinite)
//!         ∪ DNF over tuple shapes
//!         ∪ DNF over list-of-T shapes
//!         ∪ DNF over function arrows
//!
//! "Basic" types are scalars with no internal structure to vary over (`int`,
//! `float`, `nil`, `bool`, `str`, and the four vector kinds). Atoms get their
//! own field because we want literal atom types (`:ok`, `:error`) — a
//! BasicBits flag for "atom" alone wouldn't let us express that.
//!
//! Operations (union/intersect/diff/neg) work componentwise: bitwise on the
//! basic bitmap, finite/cofinite arithmetic on the atom set, DNF
//! manipulation (concat / cross-product / De Morgan) on the structurals.
//! Semantic subtyping — `T <: U` iff `T ∧ ¬U` is empty — lands in fz-ul4.3.

use std::collections::{BTreeSet, HashSet};
use std::fmt;

use crate::type_vocab::{MapKey, TypeVarId};

// ----------------------------------------------------------------------
// Basic-type bitmap
// ----------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
pub(crate) struct BasicBits(u32);

impl BasicBits {
    // Kinds without value-level distinctions (or where we choose not to track
    // them). int/float/str/atom moved into their own LiteralSet axes.
    // fz-yan.2 — NIL/BOOL bits removed; both live in the atoms axis now.
    pub const VEC_I64: BasicBits = BasicBits(1 << 0);
    pub const VEC_F64: BasicBits = BasicBits(1 << 1);
    pub const VEC_U8: BasicBits = BasicBits(1 << 2);
    pub const VEC_BIT: BasicBits = BasicBits(1 << 3);

    pub const NONE: BasicBits = BasicBits(0);
    pub const ALL: BasicBits = BasicBits((1 << 4) - 1);
    pub const fn contains_all(self, o: BasicBits) -> bool {
        (self.0 & o.0) == o.0
    }
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }
}

impl fmt::Debug for BasicBits {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "BasicBits(0b{:b})", self.0)
    }
}

const BASIC_NAMES: &[(BasicBits, &str)] = &[
    (BasicBits::VEC_I64, "vec(i64)"),
    (BasicBits::VEC_F64, "vec(f64)"),
    (BasicBits::VEC_U8, "vec(u8)"),
    (BasicBits::VEC_BIT, "vec(bit)"),
];

// ----------------------------------------------------------------------
// Literal sets (finite or cofinite over a primitive value type)
// ----------------------------------------------------------------------

/// A finite-or-cofinite set over `T`. `cofinite=false` means "exactly these";
/// `cofinite=true` means "every value of T EXCEPT these". `(false, {})` is
/// empty; `(true, {})` is the full universe of T.
///
/// Used to track singleton-type precision for atoms, ints, strs, and floats
/// (the latter via the `F64Bits` wrapper for sane equality/ordering).
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct LiteralSet<T: Ord + Clone> {
    pub set: BTreeSet<T>,
    pub cofinite: bool,
}

impl<T: Ord + Clone> LiteralSet<T> {
    pub(crate) fn none() -> Self {
        Self {
            set: BTreeSet::new(),
            cofinite: false,
        }
    }
    pub(crate) fn any() -> Self {
        Self {
            set: BTreeSet::new(),
            cofinite: true,
        }
    }
    pub(crate) fn lit(v: T) -> Self {
        let mut s = BTreeSet::new();
        s.insert(v);
        Self {
            set: s,
            cofinite: false,
        }
    }
    pub(crate) fn is_none(&self) -> bool {
        !self.cofinite && self.set.is_empty()
    }
    pub(crate) fn is_any(&self) -> bool {
        self.cofinite && self.set.is_empty()
    }
    /// fz-axu.24 (M3) — true iff this set names a specific, finite,
    /// non-empty collection of tags (i.e. a target type that
    /// *requires* a brand membership). Used by `is_subtype_under`'s
    /// rule (i): a bare-structural value can't satisfy a target that
    /// names specific brands. Encapsulates the previous inline reach
    /// into `cofinite` / `set` from outside the type.
    pub(crate) fn requires_tag(&self) -> bool {
        !self.cofinite && !self.set.is_empty()
    }

    pub(crate) fn union(&self, o: &Self) -> Self {
        let (a, b) = (&self.set, &o.set);
        match (self.cofinite, o.cofinite) {
            (false, false) => Self {
                set: a | b,
                cofinite: false,
            },
            (false, true) => Self {
                set: b - a,
                cofinite: true,
            },
            (true, false) => Self {
                set: a - b,
                cofinite: true,
            },
            (true, true) => Self {
                set: a & b,
                cofinite: true,
            },
        }
    }
    pub(crate) fn intersect(&self, o: &Self) -> Self {
        let (a, b) = (&self.set, &o.set);
        match (self.cofinite, o.cofinite) {
            (false, false) => Self {
                set: a & b,
                cofinite: false,
            },
            (false, true) => Self {
                set: a - b,
                cofinite: false,
            },
            (true, false) => Self {
                set: b - a,
                cofinite: false,
            },
            (true, true) => Self {
                set: a | b,
                cofinite: true,
            },
        }
    }
    pub(crate) fn neg(&self) -> Self {
        Self {
            set: self.set.clone(),
            cofinite: !self.cofinite,
        }
    }
}

pub(crate) type AtomSet = LiteralSet<String>;
pub(crate) type IntSet = LiteralSet<i64>;
pub(crate) type FloatSet = LiteralSet<F64Bits>;

/// fz-try.5 — parametric type-variable identifier. Vars are nominal placeholders
/// distinguished only by id; the lattice cannot tell them apart from opaques.
/// The difference is at use sites: opaques are fixed (the name *is* the type);
/// vars are substituted at instantiation sites (fz-try.6 onward).
///
/// Fresh ids are allocated by `TypeVarId::fresh()` from a process-global atomic
/// counter. This is intentionally simple — per-function scoping is handled by
/// the typer (which renames at function-typing entry to ensure α-equivalence
/// across signatures); the id itself carries no scope.
pub(crate) type VarSet = LiteralSet<TypeVarId>;

/// fz-try.7 — deterministic var-id allocation for a closure's surface arrow.
/// Vars in a closure's `(α₀, …, αₙ₋₁) -> β` signature are keyed by `(fn_id,
/// position)`. Arg positions occupy `0..MAX_CLOSURE_ARG_VAR`; ret occupies
/// the dedicated slot at `MAX_CLOSURE_ARG_VAR`.
///
/// Determinism is required for typer fixpoint convergence: re-typing the
/// same MakeClosure during iteration must produce the same Descr. Distinct
/// closure-handles of the same lambda share their vars by construction —
/// they are parametric over the same body.
///
/// The ret slot is dedicated (not just "one past the last arg") so that a
/// closure rendered at multiple apparent arities produces a consistent ret
/// var — e.g., the value-form `&fn14:() -> ret` and the called-form
/// `&fn14:(α₀) -> ret` share the same `ret` id rather than aliasing across
/// arg positions.
const MAX_CLOSURE_ARG_VAR: u32 = 63;
const VAR_STRIDE_PER_FN: u32 = MAX_CLOSURE_ARG_VAR + 1;
pub(crate) fn closure_var_id(fn_id: crate::fz_ir::FnId, position: usize) -> TypeVarId {
    let pos = position as u32;
    assert!(
        pos < VAR_STRIDE_PER_FN,
        "closure_var_id: position {} exceeds stride ({})",
        pos,
        VAR_STRIDE_PER_FN,
    );
    TypeVarId(fn_id.0 * VAR_STRIDE_PER_FN + pos)
}

/// fz-try.7 — the dedicated return-var slot for a closure's surface arrow.
/// Reserved at position `MAX_CLOSURE_ARG_VAR` so it does not alias arg
/// positions when the same closure is rendered at different apparent
/// arities (value-form vs called-form).
pub(crate) fn closure_ret_var_id(fn_id: crate::fz_ir::FnId) -> TypeVarId {
    TypeVarId(fn_id.0 * VAR_STRIDE_PER_FN + MAX_CLOSURE_ARG_VAR)
}

/// Bit-pattern wrapper around a non-NaN `f64` so we can put floats in
/// ordered/hashed sets. Two distinct bit patterns are considered distinct
/// values. `+0.0` and `-0.0` are distinct (matches IEEE bit equality but not
/// IEEE value equality — fine here, where the type system tracks values).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct F64Bits(u64);

impl F64Bits {
    pub(crate) fn new(f: f64) -> Self {
        assert!(!f.is_nan(), "F64Bits literal types do not support NaN");
        Self(f.to_bits())
    }
    pub(crate) fn get(self) -> f64 {
        f64::from_bits(self.0)
    }
}
impl fmt::Debug for F64Bits {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.get())
    }
}

// ----------------------------------------------------------------------
// Structural signatures
// ----------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct TupleSig {
    pub elems: Vec<Descr>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct ListSig {
    pub elem: Box<Descr>,
}

/// fz-ul4.27.22.8 — closure-literal tag attached to an arrow clause.
/// When `ArrowSig::lit = Some(ClosureLit { fn_id, captures })`, the clause
/// represents the *specific* closure produced by `MakeClosure(fn_id,
/// vars_typed_as_captures)` rather than the saturated arrow `(args)→ret`.
///
/// Captures are stored as a vector aligned with the first N entry params of
/// `fn_id`'s body (N = `captures.len()`). The arrow's `args` field carries
/// the apparent post-capture arity (vector of `Descr::any()` until 22.9's
/// `resolve_closure_return` refines per spec lookup).
///
/// Two `ClosureLit`s are equal iff `fn_id` and elementwise `captures`
/// match. Lit-bearing clauses do not collapse with lit-free clauses under
/// union — `closure_lit(F, K) ⊆ arrow(any..., any)` semantically, but
/// the union keeps both to preserve singleton precision downstream.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct ClosureLit {
    pub fn_id: crate::fz_ir::FnId,
    pub captures: Vec<crate::types_seam::Ty>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct ArrowSig {
    pub args: Vec<Descr>,
    pub ret: Box<Descr>,
    /// `None` for ordinary arrows; `Some` for closure literals (fz-ul4.27.22.8).
    pub lit: Option<ClosureLit>,
}

/// Open-shape map type: "any map containing AT LEAST these literal keys with
/// values of the corresponding types." Keys are concrete singleton values
/// (atoms, ints, strs); arbitrary-keyed maps fall back to `map_top`.
///
/// Subtyping (open record): `s <: t` iff every field in `t` is in `s` with
/// subtype value. More required keys = smaller set.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct MapSig {
    pub fields: std::collections::BTreeMap<MapKey, Descr>,
}

/// One conjunctive clause inside a DNF: `⋀ pos  ∧  ⋀ (¬neg)`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct Conj<T> {
    pub(crate) pos: Vec<T>,
    pub(crate) neg: Vec<T>,
}

impl<T> Conj<T> {
    /// The "true" clause — empty conjunction. As a singleton DNF it represents
    /// the saturated kind (every tuple, every list, every function).
    pub const fn top() -> Self {
        Self {
            pos: Vec::new(),
            neg: Vec::new(),
        }
    }
}
impl<T: Clone> Conj<T> {
    pub(crate) fn pos_of(t: T) -> Self {
        Self {
            pos: vec![t],
            neg: vec![],
        }
    }
}

// ----------------------------------------------------------------------
// The descriptor
// ----------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Hash)]
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
    /// (typer fresh-var introduction). Tests in this module exercise the
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
                .any(|sig| sig.elem.has_vars())
        });
        let map_any = self.maps.iter().any(|c| {
            c.pos
                .iter()
                .chain(c.neg.iter())
                .any(|sig| sig.fields.values().any(|d| d.has_vars()))
        });
        tuple_any || list_any || dnf_any(&self.funcs) || map_any
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
    pub(crate) fn instantiate(&self, sigma: &std::collections::HashMap<TypeVarId, Descr>) -> Descr {
        if !self.has_vars() {
            return self.clone();
        }
        // Split this Descr's vars axis into "covered by σ" and "passes through."
        let mut substituted = Descr::none();
        let mut passthrough_vars = self.vars.clone();
        if !self.vars.cofinite {
            // Finite set of explicit var ids — substitute each that σ covers.
            let mut new_set = std::collections::BTreeSet::new();
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
                        elem: Box::new(sig.elem.instantiate(sigma)),
                    })
                    .collect(),
                neg: c
                    .neg
                    .iter()
                    .map(|sig| ListSig {
                        elem: Box::new(sig.elem.instantiate(sigma)),
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
    /// surfaced by the typer's downstream emptiness checks.
    pub(crate) fn collect_subst_into(
        pattern: &Descr,
        witness: &Descr,
        sigma: &mut std::collections::HashMap<TypeVarId, Descr>,
    ) {
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
    pub(crate) fn vec_i64() -> Self {
        Self::from_basic(BasicBits::VEC_I64)
    }
    pub(crate) fn vec_f64() -> Self {
        Self::from_basic(BasicBits::VEC_F64)
    }
    pub(crate) fn vec_u8() -> Self {
        Self::from_basic(BasicBits::VEC_U8)
    }
    pub(crate) fn vec_bit() -> Self {
        Self::from_basic(BasicBits::VEC_BIT)
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
    /// Used by ir_fold to detect BinOp results the typer proved to a constant.
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
                if it.next().is_none() {
                    Some(first)
                } else {
                    None
                }
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
        if it.next().is_some() {
            None
        } else {
            Some(first)
        }
    }

    /// Max depth of nested Descrs reachable through structural axes. A leaf
    /// (basic, atoms, ints, floats, strs, opaques, vars) has depth 0; a
    /// tuple/list adds 1 to its element depth; a closure_lit adds 1 to its
    /// capture depths. Used by ir_reducer for materialization-depth checks.
    pub(crate) fn depth(&self) -> usize {
        let mut max_d = 0;
        for c in self.components() {
            match c {
                Component::Tuples(view) => {
                    for conj in view.inner {
                        for sig in &conj.pos {
                            for e in &sig.elems {
                                max_d = max_d.max(1 + e.depth());
                            }
                        }
                    }
                }
                Component::Lists(view) => {
                    for conj in view.inner {
                        for sig in &conj.pos {
                            max_d = max_d.max(1 + sig.elem.depth());
                        }
                    }
                }
                Component::Funcs(view) => {
                    for conj in view.inner {
                        for sig in &conj.pos {
                            if let Some(lit) = &sig.lit {
                                for cap in &lit.captures {
                                    max_d = max_d.max(1 + cap.descr().depth());
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
    /// structural axes both non-empty). Used by ir_typer's VR.5a lint to
    /// distinguish "different kinds" from "same kind, narrowed to disjoint
    /// literals." Cheaper than full `intersect`.
    pub(crate) fn kinds_overlap(&self, other: &Descr) -> bool {
        if !self.basic.intersect(other.basic).is_empty() {
            return true;
        }
        for c in self.components() {
            let overlap = match c {
                Component::Basic(_) => false, // handled above
                Component::Atoms(_) => other.components().any(|d| matches!(d, Component::Atoms(_))),
                Component::Ints(_) => other.components().any(|d| matches!(d, Component::Ints(_))),
                Component::Floats(_) => other
                    .components()
                    .any(|d| matches!(d, Component::Floats(_))),
                Component::Opaques(_) => other
                    .components()
                    .any(|d| matches!(d, Component::Opaques(_))),
                Component::Brands(_) => other
                    .components()
                    .any(|d| matches!(d, Component::Brands(_))),
                Component::Vars(_) => other.components().any(|d| matches!(d, Component::Vars(_))),
                Component::Tuples(_) => other
                    .components()
                    .any(|d| matches!(d, Component::Tuples(_))),
                Component::Lists(_) => other.components().any(|d| matches!(d, Component::Lists(_))),
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
        self.as_int_singleton().is_some()
            || self.as_atom_singleton().is_some()
            || self.as_float_singleton().is_some()
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
    /// `vt`. Negations and non-map axes are unchanged. Used by the typer
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
    /// maps, compose with `map_nested_descrs` and a recursive callback.
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

    /// Widen toward the fixed point: literal-set axes widen to their
    /// cofinite tops (`int_lit(42)` -> `int()`), while structural axes
    /// preserve shape and widen nested Descrs recursively. Atoms remain
    /// nominal singletons.
    pub(crate) fn widen(&self) -> Descr {
        self.widen_literals().map_nested_descrs(&Descr::widen)
    }

    /// Apply `f` to every nested `Descr` reachable through this Descr's
    /// structural axes (tuple elements, list element, arrow args/ret,
    /// closure captures, map values). The structural shape itself is
    /// preserved; only the contained Descrs are transformed.
    ///
    /// Consuming receiver to avoid an extra clone when composed with
    /// `widen_literals` (typical caller: `d.widen_literals().map_nested_descrs(...)`).
    pub(crate) fn map_nested_descrs(mut self, f: &impl Fn(&Descr) -> Descr) -> Descr {
        let map_tuple_sig = |s: TupleSig| TupleSig {
            elems: s.elems.iter().map(f).collect(),
        };
        let map_list_sig = |s: ListSig| ListSig {
            elem: Box::new(f(&s.elem)),
        };
        let map_arrow_sig = |s: ArrowSig| ArrowSig {
            args: s.args.iter().map(f).collect(),
            ret: Box::new(f(&s.ret)),
            lit: s.lit.map(|l| ClosureLit {
                fn_id: l.fn_id,
                captures: l
                    .captures
                    .iter()
                    .map(|t| crate::types_seam::Ty::from_descr(f(t.descr())))
                    .collect(),
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

    /// fz-axu.22 (M1) — binary top. `binary` in type-expression syntax
    /// lowers to this. Pre-M1 this Descr lived on a separate `strs`
    /// axis; M1 collapses it onto the structural binary kinds the
    /// runtime already uses (byte-aligned and bit-granular bitstrings),
    /// which is what every consumer actually meant. The name is kept
    /// to avoid churning ~30 test sites.
    pub(crate) fn str_t() -> Self {
        Self::vec_u8().union(&Self::vec_bit())
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
        let sig = ListSig {
            elem: Box::new(elem),
        };
        let mut d = Self::none();
        d.lists.push(Conj::pos_of(sig));
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
    pub(crate) fn closure_lit(
        fn_id: crate::fz_ir::FnId,
        captures: Vec<Descr>,
        n_args: usize,
    ) -> Self {
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
                captures: captures
                    .into_iter()
                    .map(crate::types_seam::Ty::from_descr)
                    .collect(),
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
            && is_dnf_top(&self.funcs)
            && is_dnf_top(&self.maps)
    }

    // ---- operations ----

    pub(crate) fn union(&self, other: &Descr) -> Descr {
        let tuples = dnf_union(&self.tuples, &other.tuples);
        let lists = dnf_union(&self.lists, &other.lists);
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
    /// is available (the typer, codegen, spec dispatch).
    pub(crate) fn is_subtype_under(
        &self,
        other: &Descr,
        brand_inners: &std::collections::HashMap<String, Descr>,
    ) -> bool {
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
    pub(crate) fn is_equiv_under(
        &self,
        other: &Descr,
        brand_inners: &std::collections::HashMap<String, Descr>,
    ) -> bool {
        self == other
            || (self.is_subtype_under(other, brand_inners)
                && other.is_subtype_under(self, brand_inners))
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

    fn is_empty_memo(&self, memo: &mut Memo) -> bool {
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
            && self.funcs.iter().all(|c| func_clause_empty(c, memo))
            && self.maps.iter().all(|c| map_clause_empty(c, memo));

        memo.in_flight.remove(self);
        result
    }
}

#[derive(Default)]
struct Memo {
    in_flight: HashSet<Descr>,
}

// ----------------------------------------------------------------------
// Tuple emptiness — Φ algorithm
// ----------------------------------------------------------------------
//
// A clause `⋀ pos ∧ ⋀ ¬neg` over n-tuples is empty iff it describes the
// empty set. We split on arity:
//
//   * Empty positives: the clause matches "any tuple of any arity not in
//     ⋃neg". Tuple arity is unbounded in fz, so a finite set of negatives
//     can never cover all arities — hence this is always non-empty.
//
//   * Non-empty positives: every positive must agree on arity (else the
//     positive intersection is empty). With shared arity n, intersect
//     positives componentwise to get a "rectangle" (t1, ..., tn). Filter
//     negatives down to those of arity n (others can't intersect this
//     rectangle, so they're vacuously satisfied). Run Φ.
//
// Φ(t, N): is the rectangle t covered by the union of negative rectangles
// in N? Pick a negative s, split t by "first index where the value falls
// outside s_i":
//
//   slab_i = (t_1 ∩ s_1, ..., t_{i-1} ∩ s_{i-1}, t_i \ s_i, t_{i+1}, ..., t_n)
//
// Each slab must be covered by N \ {s}. Base case: an empty rectangle
// (some component empty) is trivially covered.

fn tuple_clause_empty(c: &Conj<TupleSig>, memo: &mut Memo) -> bool {
    if c.pos.is_empty() {
        // Tuple universe is unbounded in arity; a finite set of negative
        // tuple shapes can never cover it.
        return false;
    }
    let arity = c.pos[0].elems.len();
    if c.pos.iter().any(|p| p.elems.len() != arity) {
        // Distinct arities in positives → intersection is empty.
        return true;
    }
    // Componentwise intersection of positives.
    let mut t: Vec<Descr> = c.pos[0].elems.clone();
    for p in &c.pos[1..] {
        for (i, e) in p.elems.iter().enumerate() {
            t[i] = t[i].intersect(e);
        }
    }
    // Negatives at this arity contribute; other arities don't intersect the
    // rectangle and are vacuously satisfied.
    let negs: Vec<Vec<Descr>> = c
        .neg
        .iter()
        .filter(|n| n.elems.len() == arity)
        .map(|n| n.elems.clone())
        .collect();
    phi_tuple(&t, &negs, memo)
}

fn phi_tuple(t: &[Descr], n: &[Vec<Descr>], memo: &mut Memo) -> bool {
    if n.is_empty() {
        return t.iter().any(|d| d.is_empty_memo(memo));
    }
    let head = &n[0];
    let rest = &n[1..];
    for i in 0..t.len() {
        let mut t_split = t.to_vec();
        for j in 0..i {
            t_split[j] = t_split[j].intersect(&head[j]);
        }
        t_split[i] = t_split[i].diff(&head[i]);
        if !phi_tuple(&t_split, rest, memo) {
            return false;
        }
    }
    true
}

// ----------------------------------------------------------------------
// List emptiness — homogeneous-list rule
// ----------------------------------------------------------------------
//
// Every `list(T)` contains nil, so the positive part is always inhabited.
// A clause `pos ∧ ⋀ ¬neg` is empty iff `list(t) ⊆ ⋃ list(N_j)` where
// `t` is the intersection of positive element types.
//
// Standard rule: `list(t) ⊆ ⋃ list(N_j)` iff there's a single j with
// `t ⊆ N_j` — because lists are homogeneous, every value of a single
// list must use the same N_j. The empty list trivially fits any list type.
//
// `is_subtype` here recurses through `is_empty`, which is what makes the
// memo necessary for recursive list types.

fn list_clause_empty(c: &Conj<ListSig>, memo: &mut Memo) -> bool {
    let t = if c.pos.is_empty() {
        Descr::any() // implicit positive: list(any)
    } else {
        let mut t = (*c.pos[0].elem).clone();
        for p in &c.pos[1..] {
            t = t.intersect(&p.elem);
        }
        t
    };
    if c.neg.is_empty() {
        // list(t) is non-empty: it always contains the empty list,
        // structurally encoded as list_of(none()) — a list whose
        // element type is uninhabited, so only the empty list itself
        // is in that set. Distinct from `Descr::nil()` (the nil
        // atom-like value); see fz-s9y.
        return false;
    }
    // exists j: t ⊆ N_j
    c.neg.iter().any(|n| t.diff(&n.elem).is_empty_memo(memo))
}

// ----------------------------------------------------------------------
// Arrow emptiness — contravariant subsumption
// ----------------------------------------------------------------------
//
// Standard semantic-subtyping result for arrows:
//   ⋀_i (t_i → u_i)  ⊆  (s → v)
//   iff  for every P' ⊆ P:  s ⊆ ⋃_{i ∈ P'} t_i  OR  ⋂_{i ∉ P'} u_i ⊆ v
//
// A clause is empty iff some negative `(s, v)` is subsumed by the
// positives — meaning every function satisfying the positives is forced
// into `(s → v)`, contradicting `¬(s → v)`. We try each negative; if any
// passes the for-all-subsets test, the clause is empty.
//
// For multi-arg arrows, the "input domain" is the n-tuple of args.

fn arrow_input(sig: &ArrowSig) -> Descr {
    Descr::tuple_of(sig.args.clone())
}

fn func_clause_empty(c: &Conj<ArrowSig>, memo: &mut Memo) -> bool {
    let p = &c.pos;
    let n = &c.neg;

    // fz-ul4.27.22.8 — closure-literal aware pre-checks.
    //
    // (a) Two positive lits in the same clause with disagreeing FnId (or
    //     different arity) describe disjoint singletons — their ∧ is
    //     bottom. Captures must intersect elementwise; any empty
    //     intersection drives the clause to bottom.
    {
        let pos_lits: Vec<&ClosureLit> = p.iter().filter_map(|s| s.lit.as_ref()).collect();
        for i in 0..pos_lits.len() {
            for j in (i + 1)..pos_lits.len() {
                if pos_lits[i].fn_id != pos_lits[j].fn_id {
                    return true;
                }
                if pos_lits[i].captures.len() != pos_lits[j].captures.len() {
                    return true;
                }
                for (a, b) in pos_lits[i].captures.iter().zip(&pos_lits[j].captures) {
                    if a.descr().intersect(b.descr()).is_empty_memo(memo) {
                        return true;
                    }
                }
            }
        }
    }

    // (b) Lit-aware negative subsumption. If a neg sig has a lit tag:
    //       - it constrains the clause only via pos sigs with matching
    //         FnId (other-FnId pos sigs don't overlap the neg's singleton
    //         set, so the negation is automatically satisfied there);
    //       - the neg is subsumed iff some matching-FnId pos sig has
    //         captures elementwise ⊇ the neg's captures.
    //     If a matching pos sig subsumes the neg → clause is bottom.
    //     If no matching pos sig exists → this neg cannot empty the
    //     clause via lit reasoning; defer to the structural check on
    //     the lit-free part below.
    'next_neg_lit: for negj in n {
        let Some(neg_lit) = &negj.lit else {
            continue;
        };
        let mut found_matching_pos = false;
        for posi in p {
            let Some(pos_lit) = &posi.lit else {
                continue;
            };
            if pos_lit.fn_id != neg_lit.fn_id {
                continue;
            }
            if pos_lit.captures.len() != neg_lit.captures.len() {
                continue;
            }
            found_matching_pos = true;
            // pos captures must elementwise ⊇ neg captures (i.e., neg
            // ⊆ pos in capture space). diff(neg, pos) empty per axis.
            let all_subset = pos_lit
                .captures
                .iter()
                .zip(&neg_lit.captures)
                .all(|(pc, nc)| nc.descr().diff(pc.descr()).is_empty_memo(memo));
            if all_subset {
                return true;
            }
        }
        if found_matching_pos {
            // We had a matching-FnId pos but it didn't fully subsume —
            // the neg cuts a hole the pos sigs don't cover. Clause is
            // not bottom via this neg. Continue to next neg.
            continue 'next_neg_lit;
        }
        // No matching-FnId pos — neg is irrelevant for lit reasoning;
        // structural check below would falsely subsume on `any`
        // placeholders. Skip negj from the structural check by
        // recording its index... simplest: short-circuit here, since
        // a lit-tagged neg unrelated to any pos lit cannot make the
        // clause empty (it negates a set disjoint from the pos).
        // Falling through to the structural check would incorrectly
        // consider this neg's any-args / any-ret coverage. So we
        // simply continue and do NOT consult negj in the structural
        // loop. To enforce that, filter negs before the loop.
    }

    // Lit-tagged negs are fully handled by the pre-pass above. If we got
    // here without returning, none of them subsumes via lit reasoning;
    // drop them all from the structural check so any-args / any-ret
    // placeholders on lit clauses can't falsely subsume.
    let filtered_negs: Vec<ArrowSig> = n
        .iter()
        .filter(|negj| negj.lit.is_none())
        .cloned()
        .collect();
    let n = &filtered_negs;

    if n.is_empty() {
        // ⋀ positives is non-empty: at least one function (e.g., the constant
        // function) satisfies any consistent set of positive arrows.
        return false;
    }
    let n_pos = p.len();
    if n_pos > 24 {
        // 2^n subsets becomes painful; we don't expect this in practice.
        // Fall through and let it run; users can split clauses if needed.
    }
    'next_neg: for negj in n {
        let s = arrow_input(negj);
        let v = (*negj.ret).clone();
        for mask in 0u32..(1u32 << n_pos) {
            let mut union_in = Descr::none();
            let mut inter_out = Descr::any();
            for (i, pi) in p.iter().enumerate().take(n_pos) {
                if (mask >> i) & 1 == 1 {
                    union_in = union_in.union(&arrow_input(pi));
                } else {
                    inter_out = inter_out.intersect(&pi.ret);
                }
            }
            // Either inputs of P' cover s, OR outputs of P\P' refine v.
            if s.diff(&union_in).is_empty_memo(memo) {
                continue;
            }
            if inter_out.diff(&v).is_empty_memo(memo) {
                continue;
            }
            // Neither side held — this subset breaks subsumption for negj.
            continue 'next_neg;
        }
        // Every subset passed → negj is subsumed → clause is empty.
        return true;
    }
    false
}

// ----------------------------------------------------------------------
// Map emptiness — open-shape rule
// ----------------------------------------------------------------------
//
// An open-shape map type `MapSig{F: T}` represents the set of all maps
// containing AT LEAST the listed keys with values of the listed types
// (more keys with arbitrary values are allowed).
//
// A clause `⋀ pos ∧ ⋀ ¬neg`:
//
//   * Empty positives: any map. Negatives covering "any map" requires the
//     union of negs to span the full map universe — impossible for any
//     finite collection of open shapes (extra keys give wiggle room).
//
//   * Non-empty positives: merge into a single open shape `P` (union of
//     required keys; intersect overlapping value types). `P` is empty if
//     any required field has empty value type. Negative `Nj` subsumes `P`
//     iff `Nj.fields ⊆ P.fields` (open subtype) AND for each shared key,
//     `P.value(k) ⊆ Nj.value(k)`. Clause is empty iff some negative
//     subsumes the merged positive.
//
//   * This is sound for the open-shape fragment we use; negatives that
//     reference "this exact key set" semantics aren't expressible here
//     (we'd need closed shapes for that).

fn map_clause_empty(c: &Conj<MapSig>, memo: &mut Memo) -> bool {
    if c.pos.is_empty() {
        // Any-map universe ⊄ finite union of open shapes (extras always escape).
        return false;
    }
    // Merge positives.
    let mut merged: std::collections::BTreeMap<MapKey, Descr> = c.pos[0].fields.clone();
    for p in &c.pos[1..] {
        for (k, v) in &p.fields {
            merged
                .entry(k.clone())
                .and_modify(|e| *e = e.intersect(v))
                .or_insert_with(|| v.clone());
        }
    }
    // Empty if any required field is empty.
    if merged.values().any(|v| v.is_empty_memo(memo)) {
        return true;
    }
    // Negative subsumption.
    for n in &c.neg {
        let n_keys_subset = n.fields.keys().all(|k| merged.contains_key(k));
        if !n_keys_subset {
            continue;
        }
        let value_refines = n.fields.iter().all(|(k, nv)| {
            merged
                .get(k)
                .map(|pv| pv.diff(nv).is_empty_memo(memo))
                .unwrap_or(false)
        });
        if value_refines {
            return true;
        }
    }
    false
}

// ----------------------------------------------------------------------
// BasicBits operations
// ----------------------------------------------------------------------

impl BasicBits {
    pub const fn union(self, o: BasicBits) -> BasicBits {
        BasicBits(self.0 | o.0)
    }
    pub const fn intersect(self, o: BasicBits) -> BasicBits {
        BasicBits(self.0 & o.0)
    }
    pub const fn neg(self) -> BasicBits {
        BasicBits(BasicBits::ALL.0 & !self.0)
    }
}

// ----------------------------------------------------------------------
// DNF operations
// ----------------------------------------------------------------------

fn dnf_union<T: Clone + PartialEq>(a: &[Conj<T>], b: &[Conj<T>]) -> Vec<Conj<T>> {
    // fz-sj6.1 — ∨ is idempotent. Dedup exact-duplicate clauses at
    // union to keep the DNF in a canonical-enough form for diagnostic
    // output and downstream consumers. Without this, repeated unions
    // of equal Descrs pile up clauses (`/tmp/sum.fz` showed 15 copies
    // of `list(1|2|3|4|5)` from recursive narrowing).
    //
    // Soundness: `A ∨ A = A` is unconditionally true. We compare
    // clauses via derived PartialEq (structural equality through
    // `Conj.pos / .neg`).
    //
    // We do NOT merge same-shape clauses (`list(A) ∨ list(B) →
    // list(A∨B)`) — that's unsound for heterogeneous lists
    // (`[1, 2.0]` lives in `list(int∨float)` but not `list(int) ∨
    // list(float)`). Subsumption-based dedup (`A ⊆ B ⇒ A ∨ B = B`,
    // fz-et8) runs as a post-pass at `Descr::union`.
    let mut out: Vec<Conj<T>> = Vec::with_capacity(a.len() + b.len());
    for c in a {
        if !out.contains(c) {
            out.push(c.clone());
        }
    }
    for c in b {
        if !out.contains(c) {
            out.push(c.clone());
        }
    }
    out
}

/// fz-et8 — drop clauses that are semantic subsets of another clause.
///
/// For each pair (Cᵢ, Cⱼ) in `clauses`, if `single(Cᵢ) <: single(Cⱼ)`
/// (and j is still kept), drop Cᵢ. Sound by absorption: `A ⊆ B ⇒ A ∨ B = B`.
///
/// `single` constructs the witness Descr for one clause on its axis;
/// only that axis is non-empty, so the subtype check decides the
/// inclusion question for this axis alone.
///
/// Exact-equal clauses do not appear (dnf_union already dedups them
/// structurally), but mutual subtypes are handled: the later index
/// is dropped because the earlier survives in `keep[j]`.
fn subsumption_dedup<T: Clone, F: Fn(&Conj<T>) -> Descr>(
    clauses: Vec<Conj<T>>,
    single: F,
) -> Vec<Conj<T>> {
    let n = clauses.len();
    if n < 2 {
        return clauses;
    }
    let descrs: Vec<Descr> = clauses.iter().map(&single).collect();
    let mut keep = vec![true; n];
    for i in 0..n {
        for j in 0..n {
            if i == j || !keep[j] {
                continue;
            }
            if descrs[i].is_subtype(&descrs[j]) {
                keep[i] = false;
                break;
            }
        }
    }
    clauses
        .into_iter()
        .zip(keep)
        .filter_map(|(c, k)| k.then_some(c))
        .collect()
}

/// fz-jvo — sig types that support semantic merging at the
/// intersection point. When two positive sigs of compatible shape
/// occur in the same Conj clause (e.g. `list(A) & list(B)` produced
/// by branch narrowing), they should collapse to a single sig with
/// elements intersected (`list(A ∩ B)`) — both for representation
/// minimality and so that downstream consumers (list_element_type,
/// tuple_projections, ...) don't see structurally-multi-sig clauses
/// they then have to reason about specially.
///
/// `intersect_pos` returns `Some(merged)` when two sigs can be
/// merged via intersection; `None` when they're incompatible (e.g.
/// tuples of different arities) and must remain as separate pos
/// sigs.
pub(crate) trait MergeSig: Clone + PartialEq {
    fn intersect_pos(a: &Self, b: &Self) -> Option<Self>;
}

impl MergeSig for ListSig {
    fn intersect_pos(a: &Self, b: &Self) -> Option<Self> {
        Some(ListSig {
            elem: Box::new(a.elem.intersect(&b.elem)),
        })
    }
}

impl MergeSig for TupleSig {
    fn intersect_pos(a: &Self, b: &Self) -> Option<Self> {
        if a.elems.len() != b.elems.len() {
            return None;
        }
        let elems = a
            .elems
            .iter()
            .zip(b.elems.iter())
            .map(|(x, y)| x.intersect(y))
            .collect();
        Some(TupleSig { elems })
    }
}

impl MergeSig for ArrowSig {
    fn intersect_pos(a: &Self, b: &Self) -> Option<Self> {
        if a.args.len() != b.args.len() {
            return None;
        }
        // fz-ul4.27.22.8 — closure-literal lit handling at ∧:
        //   lit(F,K) ∧ lit(F,K')  → lit(F, K∩K' elementwise) — same closure,
        //                          captures must satisfy both → narrow.
        //   lit(F,K) ∧ lit(F',K') with F≠F' → no function is both; return
        //                          None so the caller keeps them as separate
        //                          pos sigs (clause becomes empty under
        //                          func_clause_empty's structural check
        //                          when extended; safe representation today).
        //   lit(F,K) ∧ plain_arrow → lit(F,K) wins (singleton ⊆ arrow), but
        //                          take args/ret from the plain arrow side
        //                          if narrower.
        //   plain ∧ plain → existing behavior, lit stays None.
        let lit = match (&a.lit, &b.lit) {
            (Some(la), Some(lb)) => {
                if la.fn_id != lb.fn_id {
                    return None;
                }
                if la.captures.len() != lb.captures.len() {
                    return None;
                }
                let caps: Vec<crate::types_seam::Ty> = la
                    .captures
                    .iter()
                    .zip(lb.captures.iter())
                    .map(|(x, y)| crate::types_seam::Ty::from_descr(x.descr().intersect(y.descr())))
                    .collect();
                Some(ClosureLit {
                    fn_id: la.fn_id,
                    captures: caps,
                })
            }
            (Some(la), None) => Some(la.clone()),
            (None, Some(lb)) => Some(lb.clone()),
            (None, None) => None,
        };
        // Arrow contravariant on args (union to widen accepted input),
        // covariant on return (intersect to narrow accepted output).
        let args = a
            .args
            .iter()
            .zip(b.args.iter())
            .map(|(x, y)| x.union(y))
            .collect();
        let ret = a.ret.intersect(&b.ret);
        Some(ArrowSig {
            args,
            ret: Box::new(ret),
            lit,
        })
    }
}

impl MergeSig for MapSig {
    fn intersect_pos(a: &Self, b: &Self) -> Option<Self> {
        // Map intersection: shared keys' values get intersected;
        // keys present in only one side stay as-is (both maps must
        // have at least that field, possibly with a more permissive
        // type on the missing side).
        let mut fields = a.fields.clone();
        for (k, v) in &b.fields {
            fields
                .entry(k.clone())
                .and_modify(|prev| *prev = prev.intersect(v))
                .or_insert_with(|| v.clone());
        }
        Some(MapSig { fields })
    }
}

fn dnf_intersect<T: MergeSig>(a: &[Conj<T>], b: &[Conj<T>]) -> Vec<Conj<T>> {
    let mut out = Vec::with_capacity(a.len() * b.len());
    for c1 in a {
        for c2 in b {
            out.push(merge_clauses(c1, c2));
        }
    }
    out
}

/// ¬(⋁ Cᵢ) = ⋀ ¬Cᵢ. Each ¬Cᵢ is a DNF (disjunction of single-literal
/// clauses); we intersect them all together.
fn dnf_neg<T: MergeSig>(d: &[Conj<T>]) -> Vec<Conj<T>> {
    let mut acc: Vec<Conj<T>> = vec![Conj::top()]; // start with "true"
    for c in d {
        let neg_c = neg_clause(c);
        acc = dnf_intersect(&acc, &neg_c);
    }
    acc
}

fn merge_clauses<T: MergeSig>(a: &Conj<T>, b: &Conj<T>) -> Conj<T> {
    let mut pos = a.pos.clone();
    for new_sig in &b.pos {
        // fz-jvo — try to merge `new_sig` with an existing pos sig
        // via intersection. If compatible-shape, replace; otherwise
        // append (preserving the old dedup semantics). This keeps
        // `pos.len()` bounded for axes whose sigs always merge
        // (lists collapse to length 1; tuples merge per arity).
        let mut merged = false;
        for slot in pos.iter_mut() {
            if let Some(m) = T::intersect_pos(slot, new_sig) {
                *slot = m;
                merged = true;
                break;
            }
        }
        if !merged && !pos.contains(new_sig) {
            pos.push(new_sig.clone());
        }
    }
    let mut neg = a.neg.clone();
    for x in &b.neg {
        if !neg.contains(x) {
            neg.push(x.clone());
        }
    }
    Conj { pos, neg }
}

/// ¬(⋀ pos ∧ ⋀ ¬neg) = ⋁ (¬p) ∨ ⋁ n  — one single-literal clause per element.
fn neg_clause<T: Clone>(c: &Conj<T>) -> Vec<Conj<T>> {
    let mut out: Vec<Conj<T>> = Vec::with_capacity(c.pos.len() + c.neg.len());
    for p in &c.pos {
        out.push(Conj {
            pos: vec![],
            neg: vec![p.clone()],
        });
    }
    for n in &c.neg {
        out.push(Conj {
            pos: vec![n.clone()],
            neg: vec![],
        });
    }
    out
}

fn is_dnf_top<T>(d: &[Conj<T>]) -> bool {
    d.len() == 1 && d[0].pos.is_empty() && d[0].neg.is_empty()
}

// ----------------------------------------------------------------------
// Display
// ----------------------------------------------------------------------

impl fmt::Display for Descr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.looks_full() {
            return write!(f, "any");
        }
        if self.looks_empty() {
            return write!(f, "none");
        }

        let mut parts: Vec<String> = Vec::new();

        // fz-axu.22 (M1) — the VEC_U8 ∪ VEC_BIT combo is the binary
        // top (`@type … :: binary`). Render it as the user-facing
        // name rather than the structural "vec(u8) | vec(bit)" pair.
        let binary_mask = BasicBits::VEC_U8.union(BasicBits::VEC_BIT);
        let render_binary = self.basic.contains_all(binary_mask);
        let mut basic_for_loop = self.basic;
        if render_binary {
            parts.push("binary".to_string());
            basic_for_loop = BasicBits(basic_for_loop.0 & !binary_mask.0);
        }
        for (bit, name) in BASIC_NAMES {
            if basic_for_loop.contains_all(*bit) {
                parts.push((*name).to_string());
            }
        }

        format_lit_set(&mut parts, &self.ints, "int", |n| format!("{}", n));
        format_lit_set(&mut parts, &self.floats, "float", |f| {
            let v = f.get();
            if v.fract() == 0.0 {
                format!("{:.1}", v)
            } else {
                format!("{}", v)
            }
        });
        // fz-yan.3 — the reserved atoms render without the `:` sigil to
        // preserve the conventional `nil`/`true`/`false` rendering and
        // collapse `:true | :false` to `bool` for `Descr::bool_t()`.
        if let Some(s) = render_reserved_atom_set(&self.atoms) {
            parts.push(s);
        } else {
            format_lit_set(&mut parts, &self.atoms, "atom", |a| format!(":{}", a));
        }
        format_lit_set(&mut parts, &self.opaques, "opaque", |n| n.clone());
        // fz-axu.2 (K1) — brands render as `brand <name>` (singular) or
        // `brand <name1> | brand <name2>` (multi). Matches the user-facing
        // `refines` declaration syntax conceptually; tests rely on it.
        format_lit_set(&mut parts, &self.brands, "brand", |n| n.clone());
        // fz-try.5 — render type variables as `α<id>`. A per-signature
        // greek-letter remap (α, β, γ, …) lands in fz-try.11 (formatter).
        format_lit_set(&mut parts, &self.vars, "var", |v| format!("{}", v));

        for c in &self.tuples {
            parts.push(format_tuple_clause(c));
        }
        for c in &self.lists {
            parts.push(format_list_clause(c));
        }
        for c in &self.funcs {
            parts.push(format_arrow_clause(c));
        }
        for c in &self.maps {
            parts.push(format_map_clause(c));
        }

        write!(f, "{}", parts.join(" | "))
    }
}

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

        // fz-axu.22 (M1) — same binary-combo rendering as Display.
        let binary_mask = BasicBits::VEC_U8.union(BasicBits::VEC_BIT);
        let mut basic_for_loop = self.basic;
        if self.basic.contains_all(binary_mask) {
            parts.push("binary".to_string());
            basic_for_loop = BasicBits(basic_for_loop.0 & !binary_mask.0);
        }
        for (bit, name) in BASIC_NAMES {
            if basic_for_loop.contains_all(*bit) {
                parts.push((*name).to_string());
            }
        }

        format_lit_set_capped(&mut parts, &self.ints, "int", CAP, |n| format!("{}", n));
        format_lit_set_capped(&mut parts, &self.floats, "float", CAP, |f| {
            format!("{}", f.get())
        });
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
        for c in &self.funcs {
            parts.push(format_arrow_clause(c));
        }
        for c in &self.maps {
            parts.push(format_map_clause(c));
        }

        parts.join(" | ")
    }
}

fn format_lit_set_capped<T: Ord + Clone>(
    parts: &mut Vec<String>,
    s: &LiteralSet<T>,
    top_name: &str,
    cap: usize,
    fmt_one: impl Fn(&T) -> String,
) {
    if s.is_none() {
        return;
    }
    if s.cofinite {
        if s.set.is_empty() {
            parts.push(top_name.into());
        } else {
            let mut exc: Vec<String> = s.set.iter().take(cap).map(&fmt_one).collect();
            if s.set.len() > cap {
                exc.push(format!("… (+{} more)", s.set.len() - cap));
            }
            parts.push(format!("{} \\ {{{}}}", top_name, exc.join(", ")));
        }
    } else {
        let mut iter = s.set.iter();
        for v in iter.by_ref().take(cap) {
            parts.push(fmt_one(v));
        }
        let rest = iter.count();
        if rest > 0 {
            parts.push(format!("… (+{} more)", rest));
        }
    }
}

impl fmt::Debug for Descr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

/// fz-yan.3 — render `AtomSet`s containing only reserved atom literals
/// (`nil`, `true`, `false`) with bareword/`bool` forms instead of the
/// generic `:atom` syntax. Returns `None` if the set contains any other
/// atom name (or is `cofinite`); the caller falls back to the generic
/// renderer.
fn render_reserved_atom_set(s: &AtomSet) -> Option<String> {
    if s.is_none() || s.is_any() || s.cofinite {
        return None;
    }
    let mut has_nil = false;
    let mut has_true = false;
    let mut has_false = false;
    let mut other = false;
    for name in &s.set {
        match name.as_str() {
            "nil" => has_nil = true,
            "true" => has_true = true,
            "false" => has_false = true,
            _ => other = true,
        }
    }
    if other {
        return None;
    }
    let mut parts: Vec<&str> = Vec::new();
    if has_nil {
        parts.push("nil");
    }
    if has_true && has_false {
        parts.push("bool");
    } else if has_true {
        parts.push("true");
    } else if has_false {
        parts.push("false");
    }
    Some(parts.join(" | "))
}

fn format_lit_set<T: Ord + Clone>(
    parts: &mut Vec<String>,
    s: &LiteralSet<T>,
    top_name: &str,
    fmt_one: impl Fn(&T) -> String,
) {
    if s.is_none() {
        return;
    }
    if s.cofinite {
        if s.set.is_empty() {
            parts.push(top_name.into());
        } else {
            let exc: Vec<String> = s.set.iter().map(&fmt_one).collect();
            parts.push(format!("{} \\ {{{}}}", top_name, exc.join(", ")));
        }
    } else {
        for v in &s.set {
            parts.push(fmt_one(v));
        }
    }
}

fn format_tuple_clause(c: &Conj<TupleSig>) -> String {
    let pos: Vec<String> = c.pos.iter().map(format_tuple).collect();
    let neg: Vec<String> = c
        .neg
        .iter()
        .map(|t| format!("¬{}", format_tuple(t)))
        .collect();
    join_clause(&pos, &neg, "tuple")
}
fn format_list_clause(c: &Conj<ListSig>) -> String {
    let pos: Vec<String> = c.pos.iter().map(format_list).collect();
    let neg: Vec<String> = c
        .neg
        .iter()
        .map(|t| format!("¬{}", format_list(t)))
        .collect();
    join_clause(&pos, &neg, "list")
}
fn format_arrow_clause(c: &Conj<ArrowSig>) -> String {
    let pos: Vec<String> = c.pos.iter().map(format_arrow).collect();
    let neg: Vec<String> = c
        .neg
        .iter()
        .map(|t| format!("¬{}", format_arrow(t)))
        .collect();
    join_clause(&pos, &neg, "fn")
}
fn format_tuple(t: &TupleSig) -> String {
    let inner: Vec<String> = t.elems.iter().map(|d| format!("{}", d)).collect();
    format!("{{{}}}", inner.join(", "))
}
fn format_list(t: &ListSig) -> String {
    format!("list({})", t.elem)
}
fn format_arrow(t: &ArrowSig) -> String {
    let args: Vec<String> = t.args.iter().map(|d| format!("{}", d)).collect();
    let body = format!("({}) -> {}", args.join(", "), t.ret);
    match &t.lit {
        None => body,
        Some(l) => {
            let caps: Vec<String> = l
                .captures
                .iter()
                .map(|d| format!("{}", d.descr()))
                .collect();
            format!("&fn{}[{}]:{}", l.fn_id.0, caps.join(", "), body)
        }
    }
}
fn format_map_clause(c: &Conj<MapSig>) -> String {
    let pos: Vec<String> = c.pos.iter().map(format_map).collect();
    let neg: Vec<String> = c
        .neg
        .iter()
        .map(|m| format!("¬{}", format_map(m)))
        .collect();
    join_clause(&pos, &neg, "map")
}
fn format_map(m: &MapSig) -> String {
    let inner: Vec<String> = m
        .fields
        .iter()
        .map(|(k, v)| format!("{}: {}", format_map_key(k), v))
        .collect();
    format!("%{{{}}}", inner.join(", "))
}
fn format_map_key(k: &MapKey) -> String {
    match k {
        MapKey::Atom(a) => format!(":{}", a),
        MapKey::Int(n) => format!("{}", n),
    }
}
fn join_clause(pos: &[String], neg: &[String], top: &str) -> String {
    let all: Vec<String> = pos.iter().cloned().chain(neg.iter().cloned()).collect();
    if all.is_empty() {
        top.to_string()
    } else {
        all.join(" & ")
    }
}

// ----------------------------------------------------------------------
// Component view API (fz-68x)
// ----------------------------------------------------------------------
//
// The consumer-facing surface for code that needs to *destructure* a
// `Descr` axis-by-axis (interp TypeTest, codegen repr selection, typer
// projections, reducer literal extraction). Today the consumers reach
// into the public axis fields directly; this is the API they migrate
// to in fz-68x.{3..7}, after which the axis fields seal (fz-68x.8).
//
// The boundary lets the internal representation evolve — Elixir's
// `Module.Types.Descr` is migrating DNF → BDD with hash-consing, and
// fz can follow without rippling through every consumer.
//
// `Descr::components()` yields only *present* components, mirroring
// Elixir's sparse-map representation. Consumers `match` on the
// `Component` variant; the compiler enforces exhaustiveness, which
// turns the three-path-parity promise of `docs/descr-cleanup.md`
// into a load-bearing invariant rather than an aspiration.

// API-in-waiting: the Component types and most View methods are
// unused until fz-68x.{3..7} migrate consumers. Allow dead_code only
// on this section; do not propagate the allow upward.

/// The kinds of value-sets a `Descr` admits, one per axis. Yielded by
/// `Descr::components()`. Only present (non-empty) axes appear.
#[allow(dead_code)]
#[derive(Clone, Copy)]
pub(crate) enum Component<'a> {
    Basic(BasicBits),
    Atoms(AtomView<'a>),
    Ints(IntView<'a>),
    Floats(FloatView<'a>),
    Opaques(OpaqueView<'a>),
    Brands(BrandView<'a>),
    Vars(VarView<'a>),
    Tuples(TupleView<'a>),
    Lists(ListView<'a>),
    Funcs(FuncView<'a>),
    Maps(MapView<'a>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum AtomTypeTest {
    None,
    Any,
    Finite(Vec<String>),
    Cofinite,
}

// ---- literal-set views ----

#[derive(Clone, Copy)]
pub(crate) struct AtomView<'a> {
    inner: &'a AtomSet,
}

impl<'a> AtomView<'a> {
    pub(crate) fn is_any(&self) -> bool {
        self.inner.is_any()
    }
    pub(crate) fn cofinite(&self) -> bool {
        self.inner.cofinite
    }
    /// Iterator over finite members; `None` if the set is cofinite ("any
    /// atom except these"). Callers that handle cofinite check
    /// `cofinite()` first.
    pub(crate) fn finite(&self) -> Option<impl Iterator<Item = &'a str> + 'a> {
        if self.inner.cofinite {
            None
        } else {
            Some(self.inner.set.iter().map(String::as_str))
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) struct IntView<'a> {
    inner: &'a IntSet,
}

impl<'a> IntView<'a> {
    /// Returns the single integer if this view is exactly `{n}`; `None`
    /// otherwise (any, cofinite, multi-element, or empty).
    pub(crate) fn singleton(&self) -> Option<i64> {
        if !self.inner.cofinite && self.inner.set.len() == 1 {
            self.inner.set.iter().next().copied()
        } else {
            None
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) struct FloatView<'a> {
    inner: &'a FloatSet,
}

impl<'a> FloatView<'a> {
    /// Returns the single F64Bits if this view is exactly `{b}`; `None`
    /// otherwise. Bit-level precision — callers wanting `f64` call `.get()`.
    pub(crate) fn singleton(&self) -> Option<F64Bits> {
        if !self.inner.cofinite && self.inner.set.len() == 1 {
            self.inner.set.iter().next().copied()
        } else {
            None
        }
    }
}

#[derive(Clone, Copy)]
#[allow(dead_code)]
pub(crate) struct OpaqueView<'a> {
    inner: &'a LiteralSet<String>,
}

impl<'a> OpaqueView<'a> {
    /// fz-swt.6 — if this view names exactly one opaque type (the common
    /// case for an opaque-alias value), return its qualified tag.
    /// Returns `None` for cofinite sets (`Descr::any()`'s opaques axis is
    /// "every opaque", not a substitutable pattern) and for empty / many-
    /// tag sets. Consumers pair this with
    /// `crate::type_expr::opaque_owner_module` to discover the declaring
    /// module for visibility gating.
    #[allow(dead_code)] // exercised via Descr::as_opaque_singleton in tests; .8 wires it into typing.
    pub(crate) fn singleton(&self) -> Option<&'a str> {
        if !self.inner.cofinite && self.inner.set.len() == 1 {
            self.inner.set.iter().next().map(String::as_str)
        } else {
            None
        }
    }
}

#[derive(Clone, Copy)]
#[allow(dead_code)]
pub(crate) struct BrandView<'a> {
    inner: &'a LiteralSet<String>,
}

impl<'a> BrandView<'a> {
    /// fz-axu.2 (K1) — if this view names exactly one brand tag (the
    /// common case for a freshly minted brand value), return its
    /// qualified name. Returns `None` for cofinite sets and for empty
    /// or many-tag sets. Consumers (K4 visibility gating, K5 erasure)
    /// pair this with brand_inners to resolve the underlying Descr.
    #[allow(dead_code)] // K3 wires this into brand-mint typing.
    pub(crate) fn singleton(&self) -> Option<&'a str> {
        if !self.inner.cofinite && self.inner.set.len() == 1 {
            self.inner.set.iter().next().map(String::as_str)
        } else {
            None
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) struct VarView<'a> {
    inner: &'a VarSet,
}

impl<'a> VarView<'a> {
    /// Named finite var ids; None if cofinite (e.g. `Descr::any()`'s vars
    /// axis is "every var" — not a substitutable pattern).
    pub(crate) fn finite(&self) -> Option<impl Iterator<Item = TypeVarId> + 'a> {
        if self.inner.cofinite {
            None
        } else {
            Some(self.inner.set.iter().copied())
        }
    }
    /// Count of named finite var ids; None if cofinite. Used by the
    /// most-specific-wins ordering in spec dispatch.
    pub(crate) fn finite_len(&self) -> Option<usize> {
        if self.inner.cofinite {
            None
        } else {
            Some(self.inner.set.len())
        }
    }
}

// ---- structural views ----
//
// Each wraps a `&[Conj<Sig>]` slice but exposes only View methods. The
// DNF / clause representation is private to types.rs; consumers ask
// "what arities does this admit?", "project element i of arity-n
// tuples", "what's the joined element type?", etc.

#[derive(Clone, Copy)]
pub(crate) struct TupleView<'a> {
    inner: &'a [Conj<TupleSig>],
}

impl<'a> TupleView<'a> {
    /// True iff this view admits every tuple (single `Conj::top()` clause).
    /// True iff any clause contains a negation. Consumers that don't yet
    /// support DNF with negations check this to preserve invariants.
    pub(crate) fn has_negations(&self) -> bool {
        self.inner.iter().any(|c| !c.neg.is_empty())
    }
    /// Distinct arities admitted by any positive clause. Empty iterator
    /// if the only clauses are negations-of-top.
    pub(crate) fn arities(&self) -> impl Iterator<Item = usize> {
        let mut seen = std::collections::BTreeSet::new();
        for conj in self.inner {
            for sig in &conj.pos {
                seen.insert(sig.elems.len());
            }
        }
        seen.into_iter()
    }
    /// Project the full element-Descr vector at the given arity, following
    /// Castagna DNF semantics (fz-dhd): positive sigs within a Conj are
    /// intersected per-position; results union across Conjs. Returns None
    /// if no Conj has the requested arity. Vector length equals `arity`.
    pub(crate) fn project_all(&self, arity: usize) -> Option<Vec<Descr>> {
        let mut comps = vec![Descr::none(); arity];
        let mut found = false;
        for conj in self.inner {
            let mut clause_comps: Option<Vec<Descr>> = None;
            for sig in &conj.pos {
                if sig.elems.len() != arity {
                    continue;
                }
                clause_comps = Some(match clause_comps {
                    None => sig.elems.clone(),
                    Some(prev) => prev
                        .iter()
                        .zip(sig.elems.iter())
                        .map(|(p, s)| p.intersect(s))
                        .collect(),
                });
            }
            if let Some(cs) = clause_comps {
                for i in 0..arity {
                    comps[i] = comps[i].union(&cs[i]);
                }
                found = true;
            }
        }
        if found { Some(comps) } else { None }
    }
}

#[derive(Clone, Copy)]
pub(crate) struct ListView<'a> {
    inner: &'a [Conj<ListSig>],
}

impl<'a> ListView<'a> {
    /// Element type across all positive list clauses, following fz-dhd
    /// DNF semantics: sigs within a Conj are intersected; results union
    /// across Conjs. For `list(int) & list(any)` (one Conj, two sigs),
    /// the element is `int ∩ any = int`, not `int ∪ any = any`. Returns
    /// `Descr::any()` when the view admits no concrete lists (matches
    /// typer's prior fallback).
    pub(crate) fn element_type(&self) -> Descr {
        let mut elem = Descr::none();
        let mut found = false;
        for conj in self.inner {
            let mut clause_elem: Option<Descr> = None;
            for sig in &conj.pos {
                clause_elem = Some(match clause_elem {
                    None => sig.elem.as_ref().clone(),
                    Some(prev) => prev.intersect(&sig.elem),
                });
            }
            if let Some(e) = clause_elem {
                elem = elem.union(&e);
                found = true;
            }
        }
        if found { elem } else { Descr::any() }
    }
}

#[derive(Clone, Copy)]
pub(crate) struct FuncView<'a> {
    inner: &'a [Conj<ArrowSig>],
}

impl<'a> FuncView<'a> {
    /// True iff any clause carries negations. Consumers that don't yet
    /// support DNF with negations check this to preserve invariants
    /// (ir_typer closure dispatch falls back to `any` when this is true).
    pub(crate) fn has_negations(&self) -> bool {
        self.inner.iter().any(|c| !c.neg.is_empty())
    }
    /// True iff every clause has at least one positive arrow signature.
    /// When false, some clause is purely negative (e.g. `not arrow(...)`),
    /// which ir_typer treats as "give up; fall through to `any`."
    pub(crate) fn all_clauses_have_pos(&self) -> bool {
        self.inner.iter().all(|c| !c.pos.is_empty())
    }
    /// Arrows admitted by positive clauses. Each arrow exposes args/ret
    /// via `ArrowView`. Negations are not yielded — consumers reasoning
    /// about full DNF use the algebra (intersect/diff), not this view.
    pub(crate) fn arrows(&self) -> impl Iterator<Item = ArrowView<'a>> {
        self.inner
            .iter()
            .flat_map(|conj| conj.pos.iter().map(|sig| ArrowView { inner: sig }))
    }
    /// Arrows from clauses that have NO negations. Used by sites that
    /// want to enumerate dispatch targets safely: a clause `arrow1 ∧
    /// ¬arrow2` is too complex to flatten without losing the negation,
    /// so the consumer skips it entirely.
    #[allow(dead_code)]
    pub(crate) fn arrows_from_pure_clauses(&self) -> impl Iterator<Item = ArrowView<'a>> {
        self.inner
            .iter()
            .filter(|c| c.neg.is_empty())
            .flat_map(|conj| conj.pos.iter().map(|sig| ArrowView { inner: sig }))
    }
    /// Distinct arities admitted by positive clauses.
    #[allow(dead_code)]
    pub(crate) fn arities(&self) -> impl Iterator<Item = usize> {
        let mut seen = std::collections::BTreeSet::new();
        for conj in self.inner {
            for sig in &conj.pos {
                seen.insert(sig.args.len());
            }
        }
        seen.into_iter()
    }
}

#[derive(Clone, Copy)]
pub(crate) struct ArrowView<'a> {
    inner: &'a ArrowSig,
}

impl<'a> ArrowView<'a> {
    pub(crate) fn args(&self) -> &'a [Descr] {
        &self.inner.args
    }
    pub(crate) fn ret(&self) -> &'a Descr {
        &self.inner.ret
    }
    pub(crate) fn closure_lit(&self) -> Option<&'a ClosureLit> {
        self.inner.lit.as_ref()
    }
}

#[derive(Clone, Copy)]
pub(crate) struct MapView<'a> {
    inner: &'a [Conj<MapSig>],
}

impl<'a> MapView<'a> {
    /// Look up the value type for `key` across all positive map clauses,
    /// following Castagna open-map semantics (fz-dhd): pos sigs within a
    /// Conj are intersected (a missing field in a sig contributes
    /// `any | nil` because open maps don't constrain unmentioned keys);
    /// results union across Conjs. A Conj with `pos.is_empty()` (e.g. a
    /// pure negation of map-top) contributes `any | nil`. Returns None
    /// if the view has no clauses.
    pub(crate) fn lookup(&self, key: &MapKey) -> Option<Descr> {
        if self.inner.is_empty() {
            return None;
        }
        let mut found = false;
        let mut acc = Descr::none();
        for conj in self.inner {
            if conj.pos.is_empty() {
                acc = acc.union(&Descr::any()).union(&Descr::nil());
                found = true;
                continue;
            }
            let mut clause_v: Option<Descr> = None;
            for sig in &conj.pos {
                let sig_v = match sig.fields.get(key) {
                    Some(t) => t.clone(),
                    None => Descr::any().union(&Descr::nil()),
                };
                clause_v = Some(match clause_v {
                    None => sig_v,
                    Some(prev) => prev.intersect(&sig_v),
                });
            }
            if let Some(v) = clause_v {
                acc = acc.union(&v);
                found = true;
            }
        }
        if found { Some(acc) } else { None }
    }
}

// ---- iterator ----

impl Descr {
    /// Iterate the present components of this descriptor. An axis is
    /// "present" iff it is non-empty (matches Elixir's sparse-map
    /// convention). `Descr::any()` yields one component per axis;
    /// `Descr::none()` yields none.
    ///
    /// The order is canonical (basic, atoms, ints, floats, strs,
    /// opaques, vars, tuples, lists, funcs, maps) but consumers should
    /// `match` rather than rely on order.
    pub(crate) fn components(&self) -> impl Iterator<Item = Component<'_>> + '_ {
        let basic = (!self.basic.is_empty()).then_some(Component::Basic(self.basic));
        let atoms =
            (!self.atoms.is_none()).then_some(Component::Atoms(AtomView { inner: &self.atoms }));
        let ints = (!self.ints.is_none()).then_some(Component::Ints(IntView { inner: &self.ints }));
        let floats = (!self.floats.is_none()).then_some(Component::Floats(FloatView {
            inner: &self.floats,
        }));
        let opaques = (!self.opaques.is_none()).then_some(Component::Opaques(OpaqueView {
            inner: &self.opaques,
        }));
        let brands = (!self.brands.is_none()).then_some(Component::Brands(BrandView {
            inner: &self.brands,
        }));
        let vars = (!self.vars.is_none()).then_some(Component::Vars(VarView { inner: &self.vars }));
        let tuples = (!self.tuples.is_empty()).then_some(Component::Tuples(TupleView {
            inner: &self.tuples,
        }));
        let lists =
            (!self.lists.is_empty()).then_some(Component::Lists(ListView { inner: &self.lists }));
        let funcs =
            (!self.funcs.is_empty()).then_some(Component::Funcs(FuncView { inner: &self.funcs }));
        let maps =
            (!self.maps.is_empty()).then_some(Component::Maps(MapView { inner: &self.maps }));
        [
            basic, atoms, ints, floats, opaques, brands, vars, tuples, lists, funcs, maps,
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

    pub(crate) fn type_test_basic_bits(&self) -> BasicBits {
        self.components()
            .find_map(|component| match component {
                Component::Basic(bits) => Some(bits),
                _ => None,
            })
            .unwrap_or(BasicBits::NONE)
    }

    pub(crate) fn type_test_has_vec_i64(&self) -> bool {
        self.type_test_basic_bits().contains_all(BasicBits::VEC_I64)
    }

    pub(crate) fn type_test_has_vec_f64(&self) -> bool {
        self.type_test_basic_bits().contains_all(BasicBits::VEC_F64)
    }

    pub(crate) fn type_test_has_vec_u8(&self) -> bool {
        self.type_test_basic_bits().contains_all(BasicBits::VEC_U8)
    }

    pub(crate) fn type_test_has_vec_bit(&self) -> bool {
        self.type_test_basic_bits().contains_all(BasicBits::VEC_BIT)
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
}

// ----------------------------------------------------------------------
// Tests
// ----------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // (`str_t` was promoted to a public Descr constructor by fz-ul4.31.1.)
    impl BasicBits {
        pub(super) const fn raw(self) -> u32 {
            self.0
        }
    }

    #[test]
    fn top_and_bottom_render() {
        assert_eq!(Descr::any().to_string(), "any");
        assert_eq!(Descr::none().to_string(), "none");
    }

    #[test]
    fn each_basic_constructor_renders_its_name() {
        assert_eq!(Descr::nil().to_string(), "nil");
        assert_eq!(Descr::bool_t().to_string(), "bool");
        assert_eq!(Descr::int().to_string(), "int");
        assert_eq!(Descr::float().to_string(), "float");
        assert_eq!(Descr::str_t().to_string(), "binary");
        assert_eq!(Descr::vec_i64().to_string(), "vec(i64)");
        assert_eq!(Descr::vec_f64().to_string(), "vec(f64)");
        assert_eq!(Descr::vec_u8().to_string(), "vec(u8)");
        assert_eq!(Descr::vec_bit().to_string(), "vec(bit)");
    }

    #[test]
    fn atom_top_and_lit() {
        assert_eq!(Descr::atom_top().to_string(), "atom");
        assert_eq!(Descr::atom_lit("ok").to_string(), ":ok");
        assert_eq!(Descr::atom_lit("error").to_string(), ":error");
    }

    #[test]
    fn type_test_atom_helpers_report_shape() {
        let finite = Descr::atom_lit("ok").union(&Descr::atom_lit("error"));
        assert_eq!(
            finite.type_test_atom_literals(),
            vec!["error".to_string(), "ok".to_string()]
        );
        assert!(!finite.type_test_atom_is_any());
        assert!(!finite.type_test_atom_is_cofinite());

        let any = Descr::atom_top();
        assert!(any.type_test_atom_is_any());
        assert!(any.type_test_atom_literals().is_empty());
    }

    #[test]
    fn type_test_vector_helpers_report_basic_axes() {
        let d = Descr::vec_i64().union(&Descr::vec_u8());
        assert!(d.type_test_has_vec_i64());
        assert!(!d.type_test_has_vec_f64());
        assert!(d.type_test_has_vec_u8());
        assert!(!d.type_test_has_vec_bit());
    }

    #[test]
    fn tuple_constructor() {
        let t = Descr::tuple_of([Descr::int(), Descr::str_t()]);
        assert_eq!(t.to_string(), "{int, binary}");
    }

    #[test]
    fn list_constructor() {
        let l = Descr::list_of(Descr::int());
        assert_eq!(l.to_string(), "list(int)");
    }

    #[test]
    fn arrow_constructor() {
        let f = Descr::arrow([Descr::int(), Descr::int()], Descr::int());
        assert_eq!(f.to_string(), "(int, int) -> int");
    }

    #[test]
    fn nested_descriptors_render() {
        // list of {atom :ok, int} OR {atom :error, str}
        // (we don't have union yet, so just check one is well-formed)
        let ok = Descr::tuple_of([Descr::atom_lit("ok"), Descr::int()]);
        assert_eq!(ok.to_string(), "{:ok, int}");
        let nested = Descr::list_of(ok);
        assert_eq!(nested.to_string(), "list({:ok, int})");
    }

    #[test]
    fn equality_is_structural() {
        assert_eq!(Descr::int(), Descr::int());
        assert_ne!(Descr::int(), Descr::float());
        let a = Descr::tuple_of([Descr::int(), Descr::str_t()]);
        let b = Descr::tuple_of([Descr::int(), Descr::str_t()]);
        assert_eq!(a, b);
    }

    #[test]
    fn looks_empty_distinguishes_none_from_others() {
        assert!(Descr::none().looks_empty());
        assert!(!Descr::any().looks_empty());
        assert!(!Descr::int().looks_empty());
        assert!(!Descr::atom_lit("ok").looks_empty());
        assert!(!Descr::tuple_of([Descr::int()]).looks_empty());
    }

    // ---- operations: identities ----

    #[test]
    fn union_identity_with_none() {
        let a = Descr::int();
        assert_eq!(a.union(&Descr::none()), a);
        assert_eq!(Descr::none().union(&a), a);
    }

    /// fz-sj6.1 — ∨ is idempotent. Unioning a list-typed Descr with
    /// itself N times must keep exactly one clause, not N.
    #[test]
    fn union_idempotent_on_repeated_list_descrs() {
        let lst = Descr::list_of(Descr::int_lit(1).union(&Descr::int_lit(2)));
        let mut acc = lst.clone();
        for _ in 0..15 {
            acc = acc.union(&lst);
        }
        assert_eq!(
            acc.lists.len(),
            1,
            "expected 1 clause after 15 self-unions, got {}: {:?}",
            acc.lists.len(),
            acc
        );
        assert!(
            acc.is_equiv(&lst),
            "self-union must equal original: {} vs {}",
            acc,
            lst
        );
    }

    /// Distinct list-element types must remain distinct under dedup
    /// (only EXACT-equal clauses collapse, not merge-by-shape).
    #[test]
    fn union_keeps_distinct_list_clauses() {
        let a = Descr::list_of(Descr::int());
        let b = Descr::list_of(Descr::float());
        let u = a.union(&b);
        assert_eq!(
            u.lists.len(),
            2,
            "list(int) ∨ list(float) must keep 2 clauses, got {}: {:?}",
            u.lists.len(),
            u
        );
    }

    /// fz-et8 — subsumption-based dedup at union. `list(int)` is a
    /// strict subtype of `list(int|float)`, so their union must
    /// collapse to the superset clause alone.
    #[test]
    fn union_drops_subsumed_list_clause() {
        let narrow = Descr::list_of(Descr::int());
        let wide = Descr::list_of(Descr::int().union(&Descr::float()));
        let u = narrow.union(&wide);
        assert_eq!(
            u.lists.len(),
            1,
            "list(int) ∨ list(int|float) must collapse to 1 clause, got {}: {:?}",
            u.lists.len(),
            u
        );
        assert!(
            u.is_equiv(&wide),
            "subsumed-union result must equal the superset: {} vs {}",
            u,
            wide
        );
        // Order-independence.
        let v = wide.union(&narrow);
        assert_eq!(
            v.lists.len(),
            1,
            "list(int|float) ∨ list(int) must also collapse, got {}: {:?}",
            v.lists.len(),
            v
        );
        assert!(v.is_equiv(&wide));
    }

    #[test]
    fn intersect_identity_with_any() {
        // a ∩ any = a — every component shrinks to itself.
        for a in [Descr::int(), Descr::atom_lit("ok"), Descr::str_t()] {
            assert_eq!(a.intersect(&Descr::any()), a);
            assert_eq!(Descr::any().intersect(&a), a);
        }
    }

    #[test]
    fn intersect_with_none_is_none() {
        let a = Descr::int().union(&Descr::atom_lit("ok"));
        assert!(a.intersect(&Descr::none()).looks_empty());
    }

    #[test]
    fn neg_top_bottom() {
        assert!(Descr::any().neg().looks_empty());
        assert!(Descr::none().neg().looks_full());
    }

    // ---- basic bits ----

    #[test]
    fn basics_union_and_intersect() {
        let i = Descr::int();
        let f = Descr::float();
        let u = i.union(&f);
        assert!(u.ints.is_any());
        assert!(u.floats.is_any());
        assert_eq!(u.to_string(), "int | float");

        let inter = i.intersect(&f);
        assert!(inter.looks_empty());
    }

    #[test]
    fn neg_int_top_saturates_other_kinds() {
        let n = Descr::int().neg();
        assert!(n.ints.is_none(), "ints axis flipped to empty");
        assert!(n.floats.is_any());
        assert!(n.atoms.is_any());
        assert!(is_dnf_top(&n.tuples));
    }

    #[test]
    fn diff_self_is_empty_basic() {
        assert!(Descr::int().diff(&Descr::int()).looks_empty());
    }

    // ---- atom set ----

    #[test]
    fn atom_lits_union() {
        let a = Descr::atom_lit("ok").union(&Descr::atom_lit("error"));
        // BTreeSet ordering -> :error comes before :ok
        assert_eq!(a.to_string(), ":error | :ok");
    }

    #[test]
    fn atom_lit_subsumed_by_atom_top() {
        let big = Descr::atom_lit("ok").union(&Descr::atom_top());
        assert!(big.atoms.is_any());
    }

    #[test]
    fn atom_lits_intersect_disjoint_is_empty() {
        let inter = Descr::atom_lit("ok").intersect(&Descr::atom_lit("error"));
        assert!(inter.looks_empty());
    }

    #[test]
    fn atom_lit_intersect_atom_top_is_lit() {
        let a = Descr::atom_lit("ok");
        assert_eq!(a.intersect(&Descr::atom_top()), a);
    }

    #[test]
    fn neg_atom_lit_excludes_only_that_atom() {
        let n = Descr::atom_lit("ok").neg();
        assert!(n.atoms.cofinite);
        assert_eq!(n.atoms.set.len(), 1);
        assert!(n.atoms.set.contains("ok"));
    }

    // ---- DNF mechanics ----

    #[test]
    fn tuple_union_keeps_both_clauses() {
        let a = Descr::tuple_of([Descr::atom_lit("ok"), Descr::int()]);
        let b = Descr::tuple_of([Descr::atom_lit("error"), Descr::str_t()]);
        let u = a.union(&b);
        assert_eq!(u.tuples.len(), 2, "union concatenates DNF clauses");
        assert_eq!(u.to_string(), "{:ok, int} | {:error, binary}");
    }

    #[test]
    fn tuple_intersect_cross_products_clauses() {
        let a = Descr::tuple_of([Descr::int()]);
        let b = Descr::tuple_of([Descr::str_t()]);
        let inter = a.intersect(&b);
        // fz-jvo — same-arity tuple pos sigs now merge via
        // per-element intersection (TupleSig::intersect_pos),
        // collapsing to a single sig with elem-wise intersected
        // components. Semantically the result is empty (int ∩ str
        // is empty, so tuple-of-empty is empty), and structurally
        // it lives as one pos sig of length 1.
        assert_eq!(inter.tuples.len(), 1);
        assert_eq!(inter.tuples[0].pos.len(), 1);
        assert!(inter.tuples[0].neg.is_empty());
        assert!(inter.is_empty(), "tuple(int) ∩ tuple(str) is uninhabited");
    }

    #[test]
    fn dnf_neg_empty_is_top_clause() {
        // The lists DNF on `Descr::int()` is empty (no lists in this descr).
        // ¬(empty DNF) = ¬false = true = saturated DNF.
        let n = Descr::int().neg();
        assert!(is_dnf_top(&n.lists));
        assert!(is_dnf_top(&n.tuples));
        assert!(is_dnf_top(&n.funcs));
    }

    #[test]
    fn dnf_neg_top_is_empty() {
        // Negating Descr::any() makes every kind go from saturated to empty.
        let n = Descr::any().neg();
        assert!(n.tuples.is_empty());
        assert!(n.lists.is_empty());
        assert!(n.funcs.is_empty());
    }

    #[test]
    fn neg_tuple_clause_produces_de_morgan_expansion() {
        // ¬{int, str} as a DNF should have two single-literal negative clauses.
        let t = Descr::tuple_of([Descr::int(), Descr::str_t()]);
        let n = t.neg();
        // n.tuples = ¬ [Conj { pos: [{int,str}], neg: [] }]
        //          = [Conj { pos: [], neg: [{int,str}] }]
        assert_eq!(n.tuples.len(), 1);
        assert_eq!(n.tuples[0].pos.len(), 0);
        assert_eq!(n.tuples[0].neg.len(), 1);
    }

    // ---- combined ----

    #[test]
    fn union_int_and_atom_lit() {
        let d = Descr::int().union(&Descr::atom_lit("ok"));
        assert_eq!(d.to_string(), "int | :ok");
    }

    #[test]
    fn diff_int_or_float_minus_int_is_float() {
        let either = Descr::int().union(&Descr::float());
        let only_float = either.diff(&Descr::int());
        assert_eq!(only_float, Descr::float());
    }

    // ---- emptiness / subtyping ----

    #[test]
    fn empty_basics() {
        assert!(Descr::none().is_empty());
        assert!(!Descr::any().is_empty());
        assert!(!Descr::int().is_empty());
        assert!(!Descr::atom_lit("ok").is_empty());
        assert!(Descr::int().diff(&Descr::int()).is_empty());
        assert!(Descr::int().intersect(&Descr::float()).is_empty());
    }

    #[test]
    fn subtype_basics() {
        assert!(Descr::int().is_subtype(&Descr::int()));
        assert!(Descr::int().is_subtype(&Descr::int().union(&Descr::float())));
        assert!(
            !Descr::int()
                .union(&Descr::float())
                .is_subtype(&Descr::int())
        );
        assert!(!Descr::int().is_subtype(&Descr::atom_top()));
        assert!(Descr::none().is_subtype(&Descr::int()));
        assert!(Descr::int().is_subtype(&Descr::any()));
    }

    #[test]
    fn subtype_atoms() {
        assert!(Descr::atom_lit("ok").is_subtype(&Descr::atom_top()));
        assert!(!Descr::atom_top().is_subtype(&Descr::atom_lit("ok")));
        let either = Descr::atom_lit("ok").union(&Descr::atom_lit("error"));
        assert!(Descr::atom_lit("ok").is_subtype(&either));
        assert!(!either.is_subtype(&Descr::atom_lit("ok")));
        assert!(!Descr::atom_lit("ok").is_subtype(&Descr::atom_lit("error")));
    }

    #[test]
    fn equiv_after_double_neg() {
        let a = Descr::int().union(&Descr::atom_lit("ok"));
        assert!(a.is_equiv(&a.neg().neg()));
    }

    #[test]
    fn equiv_de_morgan() {
        let a = Descr::int();
        let b = Descr::atom_lit("ok");
        // ¬(a ∪ b) ≡ ¬a ∩ ¬b
        let lhs = a.union(&b).neg();
        let rhs = a.neg().intersect(&b.neg());
        assert!(lhs.is_equiv(&rhs));
        // ¬(a ∩ b) ≡ ¬a ∪ ¬b
        let lhs = a.intersect(&b).neg();
        let rhs = a.neg().union(&b.neg());
        assert!(lhs.is_equiv(&rhs));
    }

    // ---- tuples ----

    #[test]
    fn tuple_subtype_same_arity() {
        let t1 = Descr::tuple_of([Descr::int(), Descr::str_t()]);
        let t2 = Descr::tuple_of([Descr::int(), Descr::str_t()]);
        assert!(t1.is_subtype(&t2));
    }

    #[test]
    fn tuple_subtype_arity_mismatch() {
        let t1 = Descr::tuple_of([Descr::int()]);
        let t2 = Descr::tuple_of([Descr::int(), Descr::str_t()]);
        assert!(!t1.is_subtype(&t2));
        assert!(!t2.is_subtype(&t1));
    }

    #[test]
    fn tuple_covariance_in_components() {
        // {int, str} <: {int|float, str}
        let narrow = Descr::tuple_of([Descr::int(), Descr::str_t()]);
        let wide = Descr::tuple_of([Descr::int().union(&Descr::float()), Descr::str_t()]);
        assert!(narrow.is_subtype(&wide));
        assert!(!wide.is_subtype(&narrow));
    }

    #[test]
    fn tuple_union_distributes_over_components() {
        // {int|float, str} <: {int, str} ∪ {float, str}
        let lhs = Descr::tuple_of([Descr::int().union(&Descr::float()), Descr::str_t()]);
        let rhs = Descr::tuple_of([Descr::int(), Descr::str_t()])
            .union(&Descr::tuple_of([Descr::float(), Descr::str_t()]));
        assert!(lhs.is_subtype(&rhs));
        assert!(rhs.is_subtype(&lhs));
        assert!(lhs.is_equiv(&rhs));
    }

    // ---- lists ----

    #[test]
    fn list_subtype_in_element_type() {
        // list(int) <: list(int|float)
        let narrow = Descr::list_of(Descr::int());
        let wide = Descr::list_of(Descr::int().union(&Descr::float()));
        assert!(narrow.is_subtype(&wide));
        assert!(!wide.is_subtype(&narrow));
    }

    #[test]
    fn list_of_none_is_subtype_of_any_list() {
        // list(none) is the empty list — a list whose element type is
        // uninhabited, so only the empty list itself is in that set.
        // It's a subtype of every list type. Distinct from `Descr::nil()`
        // (the nil atom-like value), which has its own runtime bit
        // pattern after fz-s9y.
        let empty_list = Descr::list_of(Descr::none());
        assert!(empty_list.is_subtype(&Descr::list_of(Descr::int())));
        assert!(empty_list.is_subtype(&Descr::list_of(Descr::atom_top())));
    }

    #[test]
    fn list_union_does_not_distribute_homogeneously() {
        // Heterogeneous list types are NOT a union of homogeneous lists.
        // list({:a, :b}) ⊄ list(:a) ∪ list(:b)  — the list [:a, :b] would
        // have to live in one of the homogeneous types, but it doesn't.
        let mixed = Descr::list_of(Descr::atom_lit("a").union(&Descr::atom_lit("b")));
        let parts =
            Descr::list_of(Descr::atom_lit("a")).union(&Descr::list_of(Descr::atom_lit("b")));
        assert!(
            !mixed.is_subtype(&parts),
            "homogeneous lists do not cover mixed"
        );
        // But the reverse holds:
        assert!(parts.is_subtype(&mixed));
    }

    // ---- arrows ----

    #[test]
    fn arrow_contravariance_in_input() {
        // (int|float) -> int   <:   int -> int   (wider input is subtype)
        let wider_in = Descr::arrow([Descr::int().union(&Descr::float())], Descr::int());
        let narrow_in = Descr::arrow([Descr::int()], Descr::int());
        assert!(wider_in.is_subtype(&narrow_in));
        assert!(!narrow_in.is_subtype(&wider_in));
    }

    #[test]
    fn arrow_covariance_in_output() {
        // int -> int   <:   int -> (int|float)
        let narrow_out = Descr::arrow([Descr::int()], Descr::int());
        let wide_out = Descr::arrow([Descr::int()], Descr::int().union(&Descr::float()));
        assert!(narrow_out.is_subtype(&wide_out));
        assert!(!wide_out.is_subtype(&narrow_out));
    }

    #[test]
    fn arrow_join_return_union_of_clauses() {
        // (int -> int) ∪ (str -> bool) joins return to int|bool.
        let a = Descr::arrow([Descr::int()], Descr::int());
        let b = Descr::arrow([Descr::str_t()], Descr::bool_t());
        let u = a.union(&b);
        let got = u.arrow_join_return();
        let want = Descr::int().union(&Descr::bool_t());
        assert!(
            got.is_subtype(&want) && want.is_subtype(&got),
            "got = {}, want = {}",
            got,
            want
        );
    }

    #[test]
    fn arrow_join_return_top_is_any() {
        // Saturated funcs axis (Conj::top) ⇒ any.
        assert!(Descr::any().arrow_join_return().is_subtype(&Descr::any()));
        assert!(Descr::any().is_subtype(&Descr::any().arrow_join_return()));
    }

    #[test]
    fn arrow_join_return_empty_is_any() {
        // No arrow clauses (e.g., int-only Descr) ⇒ any (no info).
        assert!(Descr::int().arrow_join_return().is_subtype(&Descr::any()));
        assert!(Descr::any().is_subtype(&Descr::int().arrow_join_return()));
    }

    #[test]
    fn arrow_intersection_is_multiclause() {
        // (int -> int) ∩ (str -> str)  <:  (int|str) -> (int|str)
        // — the multi-clause function semantics. NOT equivalent because the
        // intersection knows which return type matches which input.
        let multi = Descr::arrow([Descr::int()], Descr::int())
            .intersect(&Descr::arrow([Descr::str_t()], Descr::str_t()));
        let combined = Descr::arrow(
            [Descr::int().union(&Descr::str_t())],
            Descr::int().union(&Descr::str_t()),
        );
        assert!(multi.is_subtype(&combined));
        assert!(
            !combined.is_subtype(&multi),
            "combined arrow loses the per-clause return refinement"
        );
    }

    // ---- mixed kinds ----

    #[test]
    fn disjoint_kinds_dont_subtype() {
        assert!(!Descr::int().is_subtype(&Descr::atom_top()));
        assert!(!Descr::atom_top().is_subtype(&Descr::int()));
        assert!(!Descr::int().is_subtype(&Descr::tuple_of([Descr::int()])));
        assert!(!Descr::list_of(Descr::int()).is_subtype(&Descr::tuple_of([Descr::int()])));
    }

    #[test]
    fn intersection_with_disjoint_is_empty() {
        assert!(Descr::int().intersect(&Descr::atom_top()).is_empty());
        assert!(
            Descr::list_of(Descr::int())
                .intersect(&Descr::tuple_of([Descr::int()]))
                .is_empty()
        );
    }

    #[test]
    fn ok_or_error_result_subtype() {
        // Result(int, atom) = {:ok, int} ∪ {:error, atom}
        // {:ok, int} <: Result(int, atom)
        let result_t =
            Descr::tuple_of([Descr::atom_lit("ok"), Descr::int()]).union(&Descr::tuple_of([
                Descr::atom_lit("error"),
                Descr::atom_top(),
            ]));
        let an_ok = Descr::tuple_of([Descr::atom_lit("ok"), Descr::int()]);
        assert!(an_ok.is_subtype(&result_t));
        // {:ok, str} </: Result(int, atom)
        let bad = Descr::tuple_of([Descr::atom_lit("ok"), Descr::str_t()]);
        assert!(!bad.is_subtype(&result_t));
    }

    // ---- singleton types (int / float / str) ----

    #[test]
    fn int_lit_subtype_of_int_top() {
        assert!(Descr::int_lit(0).is_subtype(&Descr::int()));
        assert!(Descr::int_lit(42).is_subtype(&Descr::int()));
        assert!(!Descr::int().is_subtype(&Descr::int_lit(0)));
    }

    #[test]
    fn int_lit_distinct_singletons() {
        assert!(!Descr::int_lit(0).is_subtype(&Descr::int_lit(1)));
        assert!(Descr::int_lit(0).intersect(&Descr::int_lit(1)).is_empty());
        let zero_or_one = Descr::int_lit(0).union(&Descr::int_lit(1));
        assert!(Descr::int_lit(0).is_subtype(&zero_or_one));
        assert!(zero_or_one.is_subtype(&Descr::int()));
    }

    #[test]
    fn int_lit_diff_excludes_value() {
        // int \ {0} keeps every int except 0
        let nonzero = Descr::int().diff(&Descr::int_lit(0));
        assert!(!Descr::int_lit(0).is_subtype(&nonzero));
        assert!(Descr::int_lit(1).is_subtype(&nonzero));
    }

    #[test]
    fn float_lit_singletons() {
        assert!(Descr::float_lit(1.5).is_subtype(&Descr::float()));
        assert!(!Descr::float_lit(1.5).is_subtype(&Descr::float_lit(2.5)));
        let pair = Descr::float_lit(1.5).union(&Descr::float_lit(2.5));
        assert_eq!(pair.to_string(), "1.5 | 2.5");
    }

    #[test]
    fn singleton_in_tuple() {
        // {:ok, 0} <: {:ok, int} but {:ok, 0} </: {:ok, 1}
        let one = Descr::tuple_of([Descr::atom_lit("ok"), Descr::int_lit(0)]);
        let any_ok = Descr::tuple_of([Descr::atom_lit("ok"), Descr::int()]);
        let ok_one = Descr::tuple_of([Descr::atom_lit("ok"), Descr::int_lit(1)]);
        assert!(one.is_subtype(&any_ok));
        assert!(!one.is_subtype(&ok_one));
    }

    #[test]
    fn display_int_singleton() {
        assert_eq!(Descr::int_lit(42).to_string(), "42");
        assert_eq!(
            Descr::int_lit(0).union(&Descr::int_lit(1)).to_string(),
            "0 | 1"
        );
    }

    // ---- maps ----

    fn ak(s: &str) -> MapKey {
        MapKey::Atom(s.into())
    }

    #[test]
    fn map_top_and_constructor() {
        assert_eq!(Descr::map_top().to_string(), "map");
        let m = Descr::map_of([(ak("name"), Descr::str_t()), (ak("age"), Descr::int())]);
        // BTreeMap orders by key, so :age comes before :name
        assert_eq!(m.to_string(), "%{:age: int, :name: binary}");
    }

    #[test]
    fn map_subtype_open_record() {
        // %{a: int, b: str} <: %{a: int}  (more required keys = smaller set)
        let big = Descr::map_of([(ak("a"), Descr::int()), (ak("b"), Descr::str_t())]);
        let small = Descr::map_of([(ak("a"), Descr::int())]);
        assert!(big.is_subtype(&small));
        assert!(!small.is_subtype(&big));
    }

    #[test]
    fn map_subtype_value_covariance() {
        // %{a: 0} <: %{a: int}
        let narrow = Descr::map_of([(ak("a"), Descr::int_lit(0))]);
        let wide = Descr::map_of([(ak("a"), Descr::int())]);
        assert!(narrow.is_subtype(&wide));
        assert!(!wide.is_subtype(&narrow));
    }

    #[test]
    fn map_with_empty_value_is_empty() {
        let bad = Descr::map_of([(ak("k"), Descr::int().intersect(&Descr::str_t()))]);
        assert!(bad.is_empty());
    }

    #[test]
    fn map_top_is_subtype_of_itself_only() {
        let top = Descr::map_top();
        assert!(top.is_subtype(&top));
        let m = Descr::map_of([(ak("a"), Descr::int())]);
        assert!(m.is_subtype(&top));
        assert!(!top.is_subtype(&m), "map ⊄ %{{a: int}}");
    }

    #[test]
    fn basic_bits_flags_are_disjoint() {
        let bits = [
            BasicBits::VEC_I64,
            BasicBits::VEC_F64,
            BasicBits::VEC_U8,
            BasicBits::VEC_BIT,
        ];
        for (i, a) in bits.iter().enumerate() {
            for b in &bits[i + 1..] {
                assert_eq!(
                    a.raw() & b.raw(),
                    0,
                    "bits should be disjoint: {:?} vs {:?}",
                    a,
                    b
                );
            }
        }
        // ALL covers exactly those bits and nothing else.
        let or_all = bits.iter().fold(0u32, |acc, b| acc | b.raw());
        assert_eq!(BasicBits::ALL.raw(), or_all);
    }

    // ----- .20.8: display_for_diag -----

    #[test]
    fn display_for_diag_caps_finite_literal_sets() {
        // A literal-set with 10 distinct ints should render the first
        // 5 plus an ellipsis "+5 more".
        let mut d = Descr::none();
        for i in 1..=10 {
            d = d.union(&Descr::int_lit(i));
        }
        let s = d.display_for_diag();
        // Exactly five comma-separated int values + an ellipsis.
        let pipe_parts: Vec<&str> = s.split(" | ").collect();
        assert!(
            pipe_parts.len() == 6,
            "expected 5 ints + ellipsis, got: {}",
            s
        );
        assert!(s.contains("(+5 more)"), "expected ellipsis, got: {}", s);
    }

    #[test]
    fn display_for_diag_handles_top_and_bottom() {
        assert_eq!(Descr::any().display_for_diag(), "any");
        assert_eq!(Descr::none().display_for_diag(), "none");
    }

    #[test]
    fn display_for_diag_renders_union_of_basic_kinds() {
        // int union atom — both are top kinds.
        let d = Descr::int().union(&Descr::atom_top());
        let s = d.display_for_diag();
        assert!(s.contains("int"), "got {}", s);
        assert!(s.contains("atom"), "got {}", s);
        assert!(s.contains(" | "), "got {}", s);
    }

    #[test]
    fn display_for_diag_short_set_renders_untruncated() {
        // 3 atoms — under the cap, no ellipsis.
        let d = Descr::atom_lit("a".to_string())
            .union(&Descr::atom_lit("b".to_string()))
            .union(&Descr::atom_lit("c".to_string()));
        let s = d.display_for_diag();
        assert!(!s.contains("more"), "should not truncate: {}", s);
        assert!(s.contains(":a"));
        assert!(s.contains(":b"));
        assert!(s.contains(":c"));
    }

    // ---- fz-ul4.27.22.8 closure_lit tests ----

    fn fid(n: u32) -> crate::fz_ir::FnId {
        crate::fz_ir::FnId(n)
    }

    #[test]
    fn closure_lit_round_trips_through_accessor() {
        let cl = Descr::closure_lit(fid(7), vec![Descr::int_lit(10), Descr::int_lit(20)], 1);
        let tag = cl.as_closure_lit().expect("expected closure_lit");
        assert_eq!(tag.fn_id, fid(7));
        assert_eq!(tag.captures.len(), 2);
        assert_eq!(tag.captures[0].descr(), &Descr::int_lit(10));
        assert_eq!(tag.captures[1].descr(), &Descr::int_lit(20));
    }

    #[test]
    fn plain_arrow_has_no_closure_lit() {
        let a = Descr::arrow([Descr::any()], Descr::any());
        assert!(a.as_closure_lit().is_none());
    }

    #[test]
    fn closure_lit_renders_with_fn_id_and_captures() {
        let cl = Descr::closure_lit(fid(3), vec![Descr::int_lit(10), Descr::int_lit(20)], 1);
        let s = format!("{}", cl);
        assert!(s.starts_with("&fn3["), "got {}", s);
        assert!(s.contains("10"), "got {}", s);
        assert!(s.contains("20"), "got {}", s);
        assert!(s.contains(" -> "), "got {}", s);
    }

    #[test]
    fn closure_lit_equality_is_by_fn_id_and_captures() {
        let a = Descr::closure_lit(fid(3), vec![Descr::int_lit(10)], 1);
        let b = Descr::closure_lit(fid(3), vec![Descr::int_lit(10)], 1);
        let c = Descr::closure_lit(fid(3), vec![Descr::int_lit(99)], 1);
        let d = Descr::closure_lit(fid(4), vec![Descr::int_lit(10)], 1);
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_ne!(a, d);
    }

    #[test]
    fn closure_lit_union_exact_dedups() {
        // Identical singletons unioned → single clause, identity preserved.
        let a = Descr::closure_lit(fid(3), vec![Descr::int_lit(10)], 1);
        let b = Descr::closure_lit(fid(3), vec![Descr::int_lit(10)], 1);
        let u = a.union(&b);
        assert_eq!(u, a, "exact dup union should idempote");
        assert!(u.as_closure_lit().is_some(), "still a singleton");
    }

    #[test]
    fn closure_lit_union_different_captures_keeps_both_clauses() {
        // Different captures with same FnId → two clauses today (precision
        // collapse is the responsibility of 22.9's resolve_closure_return).
        let a = Descr::closure_lit(fid(3), vec![Descr::int_lit(10)], 1);
        let b = Descr::closure_lit(fid(3), vec![Descr::int_lit(20)], 1);
        let u = a.union(&b);
        assert_eq!(u.funcs.len(), 2, "expected two clauses: {}", u);
        // No longer a single-clause singleton — accessor returns None.
        assert!(u.as_closure_lit().is_none());
    }

    #[test]
    fn closure_lit_union_different_fn_ids_keeps_both_clauses() {
        let a = Descr::closure_lit(fid(3), vec![], 1);
        let b = Descr::closure_lit(fid(4), vec![], 1);
        let u = a.union(&b);
        assert_eq!(u.funcs.len(), 2, "expected two clauses: {}", u);
        assert!(u.as_closure_lit().is_none());
    }

    #[test]
    fn closure_lit_intersect_same_fn_narrows_captures() {
        // Same FnId, captures intersect elementwise.
        // int ∩ int_lit(10) = int_lit(10).
        let a = Descr::closure_lit(fid(3), vec![Descr::int()], 1);
        let b = Descr::closure_lit(fid(3), vec![Descr::int_lit(10)], 1);
        let i = a.intersect(&b);
        let tag = i
            .as_closure_lit()
            .expect("expected singleton after intersect");
        assert_eq!(tag.fn_id, fid(3));
        assert_eq!(tag.captures[0].descr(), &Descr::int_lit(10));
    }

    #[test]
    fn closure_lit_intersect_different_fn_ids_is_empty() {
        let a = Descr::closure_lit(fid(3), vec![], 1);
        let b = Descr::closure_lit(fid(4), vec![], 1);
        let i = a.intersect(&b);
        assert!(
            i.is_empty(),
            "different-FnId closure_lits ∧ should be bottom: got {}",
            i
        );
    }

    #[test]
    fn closure_lit_widens_captures_via_typer() {
        // Descr::widen on int_lit(N) -> int. Lit FnId preserved.
        let a = Descr::closure_lit(fid(3), vec![Descr::int_lit(10)], 1);
        let w = a.widen();
        let tag = w.as_closure_lit().expect("widen should preserve singleton");
        assert_eq!(tag.fn_id, fid(3));
        assert_eq!(
            tag.captures[0].descr(),
            &Descr::int(),
            "widen should drop int literals to int"
        );
    }

    // ---- opaque type tests ----

    #[test]
    fn opaque_renders_name() {
        let pid = Descr::opaque_of("pid");
        assert_eq!(pid.to_string(), "pid");
    }

    #[test]
    fn opaque_is_not_subtype_of_underlying() {
        let pid = Descr::opaque_of("pid");
        let int = Descr::int();
        assert!(
            !pid.is_subtype(&int),
            "pid should NOT be a subtype of integer"
        );
    }

    #[test]
    fn underlying_is_not_subtype_of_opaque() {
        let pid = Descr::opaque_of("pid");
        let int = Descr::int();
        assert!(
            !int.is_subtype(&pid),
            "integer should NOT be a subtype of pid"
        );
    }

    #[test]
    fn opaque_is_subtype_of_itself() {
        let pid = Descr::opaque_of("pid");
        assert!(pid.is_subtype(&pid), "pid should be a subtype of itself");
    }

    // ------------------------------------------------------------------
    // fz-axu.2 (K1) — brands axis
    // ------------------------------------------------------------------

    #[test]
    fn brand_of_is_non_empty_and_distinguishable() {
        let utf8 = Descr::brand_of("utf8");
        assert!(!utf8.is_empty(), "brand_of must not be empty");
        assert!(!utf8.looks_full(), "brand_of must not look full");
        // Only the brands axis is populated.
        assert!(utf8.basic.is_empty());
        assert!(utf8.atoms.is_none());
        assert!(utf8.ints.is_none());
        assert!(
            utf8.opaques.is_none(),
            "brands and opaques are distinct axes"
        );
        assert!(utf8.vars.is_none());
        assert!(!utf8.brands.is_none(), "brands axis must carry the tag");
    }

    #[test]
    fn brand_is_subtype_of_itself() {
        let utf8 = Descr::brand_of("utf8");
        assert!(utf8.is_subtype(&utf8), "utf8 ⊆ utf8");
    }

    #[test]
    fn two_distinct_brands_do_not_overlap() {
        let a = Descr::brand_of("utf8");
        let b = Descr::brand_of("ascii");
        let i = a.intersect(&b);
        assert!(i.is_empty(), "utf8 ∩ ascii must be empty: got {}", i);
    }

    #[test]
    fn brand_union_with_any_becomes_any() {
        let utf8 = Descr::brand_of("utf8");
        let u = utf8.union(&Descr::any());
        assert!(u.looks_full(), "utf8 ∪ any must be any: got {}", u);
    }

    #[test]
    fn brand_is_disjoint_from_same_name_opaque() {
        // Brands and opaques live in different axes — even if the tag
        // text matches, they don't overlap. K4's is_subtype rule reads
        // the inner; K1 only proves the lattice keeps them separate.
        let b = Descr::brand_of("X");
        let o = Descr::opaque_of("X");
        let i = b.intersect(&o);
        assert!(i.is_empty(), "brand(X) ∩ opaque(X) must be empty");
    }

    #[test]
    fn brand_renders_finite_as_bare_name() {
        // Matches the opaque-display convention: finite singletons render
        // just the tag; the "brand" keyword shows up only in cofinite
        // forms (e.g. `brand \ {utf8}`).
        let utf8 = Descr::brand_of("utf8");
        assert_eq!(format!("{}", utf8), "utf8");
        // Cofinite case: ¬utf8 still belongs to the brands axis at top.
        let cofinite = utf8.neg();
        let s = format!("{}", cofinite);
        assert!(s.contains("brand \\ {utf8}"), "cofinite rendering: {}", s);
    }

    #[test]
    fn any_contains_all_brands() {
        let any = Descr::any();
        assert!(any.brands.is_any(), "Descr::any().brands must be universe");
        let utf8 = Descr::brand_of("utf8");
        assert!(utf8.is_subtype(&any), "brand(utf8) ⊆ any");
    }

    #[test]
    fn brand_singleton_extracts_the_tag() {
        let utf8 = Descr::brand_of("utf8");
        assert_eq!(utf8.as_brand_singleton(), Some("utf8"));
        let two = utf8.union(&Descr::brand_of("ascii"));
        assert_eq!(
            two.as_brand_singleton(),
            None,
            "multi-tag set has no singleton"
        );
        assert_eq!(
            Descr::any().as_brand_singleton(),
            None,
            "cofinite has no singleton"
        );
        assert_eq!(
            Descr::int().as_brand_singleton(),
            None,
            "non-brand axes don't yield a brand singleton"
        );
    }

    // fz-axu.5 (K4) — brand-aware subtype rule. A minted brand value
    // (brands={B} ∧ structural T) is a subtype of T when brand_inners
    // ratifies that B's inner is structurally T.

    fn brand_inners(items: &[(&str, Descr)]) -> std::collections::HashMap<String, Descr> {
        items
            .iter()
            .map(|(n, d)| (n.to_string(), d.clone()))
            .collect()
    }

    #[test]
    fn is_subtype_under_discharges_brand_when_inner_fits() {
        // utf8 :: refines binary. A value typed `brands={utf8} ∧ str_t`
        // is a subtype of str_t under brand_inners[utf8 → str_t].
        let inners = brand_inners(&[("utf8", Descr::str_t())]);
        let mut minted = Descr::str_t();
        minted.brands = LiteralSet::lit("utf8".to_string());
        assert!(
            !minted.is_subtype(&Descr::str_t()),
            "strict lattice keeps the brand tag — minted is NOT a subtype without K4",
        );
        assert!(
            minted.is_subtype_under(&Descr::str_t(), &inners),
            "K4 rule: brand-tagged binary IS a subtype of binary",
        );
    }

    #[test]
    fn is_subtype_under_keeps_brand_when_inner_does_not_fit() {
        // utf8 :: refines binary. A utf8 value is NOT a subtype of int,
        // because the inner is binary, not int.
        let inners = brand_inners(&[("utf8", Descr::str_t())]);
        let mut minted = Descr::str_t();
        minted.brands = LiteralSet::lit("utf8".to_string());
        assert!(
            !minted.is_subtype_under(&Descr::int(), &inners),
            "K4 rule must not discharge the brand when the inner doesn't fit",
        );
    }

    #[test]
    fn is_subtype_under_no_brand_inners_falls_back_to_strict() {
        // Empty brand_inners → no tag can be discharged. Behavior is
        // identical to the strict lattice.
        let inners = brand_inners(&[]);
        let mut minted = Descr::str_t();
        minted.brands = LiteralSet::lit("utf8".to_string());
        assert_eq!(
            minted.is_subtype(&Descr::str_t()),
            minted.is_subtype_under(&Descr::str_t(), &inners),
            "with no brand_inners the helper degenerates to is_subtype",
        );
    }

    #[test]
    fn is_subtype_under_target_with_brand_restriction_still_works() {
        // utf8 ⊆ utf8: brand-aware lookup leaves the tag in place when
        // the target also restricts to that brand. Verifies the K4 rule
        // doesn't drop tags that the target still wants.
        let inners = brand_inners(&[("utf8", Descr::str_t())]);
        let mut minted = Descr::str_t();
        minted.brands = LiteralSet::lit("utf8".to_string());
        let mut target = Descr::str_t();
        target.brands = LiteralSet::lit("utf8".to_string());
        assert!(minted.is_subtype_under(&target, &inners));
        // And the inverse: a plain binary (brands=none) is NOT a utf8.
        assert!(!Descr::str_t().is_subtype_under(&target, &inners));
    }

    #[test]
    fn brand_neg_excludes_only_that_brand() {
        let a = Descr::brand_of("utf8");
        let b = Descr::brand_of("ascii");
        let not_a = a.neg();
        assert!(!a.is_subtype(&not_a), "utf8 ⊄ ¬utf8");
        assert!(b.is_subtype(&not_a), "ascii ⊆ ¬utf8");
    }

    #[test]
    fn two_distinct_opaques_do_not_overlap() {
        let pid = Descr::opaque_of("pid");
        let ts = Descr::opaque_of("timestamp");
        let i = pid.intersect(&ts);
        assert!(i.is_empty(), "pid ∩ timestamp should be empty: got {}", i);
    }

    #[test]
    fn opaque_union_with_any_becomes_any() {
        let pid = Descr::opaque_of("pid");
        let u = pid.union(&Descr::any());
        assert!(u.looks_full(), "pid | any should be any: got {}", u);
    }

    // ------------------------------------------------------------------
    // fz-try.5 — type-variable axis
    // ------------------------------------------------------------------

    #[test]
    fn type_var_id_displays_as_alpha_indexed() {
        assert_eq!(format!("{}", TypeVarId(0)), "α0");
        assert_eq!(format!("{}", TypeVarId(7)), "α7");
        assert_eq!(format!("{:?}", TypeVarId(0)), "α0");
    }

    #[test]
    fn type_var_id_fresh_yields_distinct_ids() {
        let a = TypeVarId::fresh();
        let b = TypeVarId::fresh();
        assert_ne!(a, b, "TypeVarId::fresh() must produce distinct ids");
    }

    #[test]
    fn descr_var_round_trips_via_axis() {
        let v = Descr::var(TypeVarId(0));
        assert!(!v.is_empty(), "var(α0) should not be empty");
        assert!(!v.looks_full(), "var(α0) should not look full");
        // The only non-default axis is `vars` itself.
        assert!(v.basic.is_empty());
        assert!(v.atoms.is_none());
        assert!(v.ints.is_none());
        assert!(v.opaques.is_none());
        assert!(!v.vars.is_none(), "vars axis must carry the id");
    }

    #[test]
    fn descr_var_renders_as_alpha_id() {
        let v = Descr::var(TypeVarId(3));
        assert_eq!(format!("{}", v), "α3");
    }

    #[test]
    fn var_is_subtype_of_itself() {
        let a = Descr::var(TypeVarId(0));
        assert!(a.is_subtype(&a), "α should be a subtype of itself");
    }

    #[test]
    fn distinct_vars_do_not_overlap() {
        let a = Descr::var(TypeVarId(0));
        let b = Descr::var(TypeVarId(1));
        let i = a.intersect(&b);
        assert!(i.is_empty(), "α0 ∩ α1 must be empty: got {}", i);
    }

    #[test]
    fn same_var_intersection_preserves_var() {
        let a = Descr::var(TypeVarId(0));
        let i = a.intersect(&a);
        assert!(i.is_equiv(&a), "α0 ∩ α0 must equal α0: got {}", i);
    }

    #[test]
    fn var_union_with_int_keeps_both() {
        let a = Descr::var(TypeVarId(0));
        let i = Descr::int();
        let u = a.union(&i);
        assert!(!u.is_empty());
        assert!(!u.vars.is_none(), "union must retain the type variable");
        assert!(u.ints.is_any(), "and the int axis must be saturated");
        // The union is the sum: members of α OR members of int.
        assert!(a.is_subtype(&u), "α ⊆ (α ∪ int)");
        assert!(i.is_subtype(&u), "int ⊆ (α ∪ int)");
    }

    #[test]
    fn var_union_with_any_becomes_any() {
        let a = Descr::var(TypeVarId(0));
        let u = a.union(&Descr::any());
        assert!(u.looks_full(), "α ∪ any should be any: got {}", u);
    }

    #[test]
    fn any_contains_all_vars() {
        // Descr::any() includes the entire vars axis (cofinite empty).
        let any = Descr::any();
        assert!(
            any.vars.is_any(),
            "Descr::any().vars must be the full universe"
        );
        let a = Descr::var(TypeVarId(0));
        assert!(a.is_subtype(&any), "α ⊆ any");
    }

    #[test]
    fn none_excludes_all_vars() {
        let none = Descr::none();
        assert!(none.vars.is_none(), "Descr::none().vars must be empty");
    }

    #[test]
    fn var_neg_excludes_only_that_var() {
        // ¬α0 covers everything except α0. So α0 ⊄ ¬α0, but α1 ⊆ ¬α0.
        let a = Descr::var(TypeVarId(0));
        let b = Descr::var(TypeVarId(1));
        let not_a = a.neg();
        assert!(!a.is_subtype(&not_a), "α0 must not be a subtype of ¬α0");
        assert!(b.is_subtype(&not_a), "α1 ⊆ ¬α0 (different name)");
    }

    #[test]
    fn var_is_not_opaque() {
        // Vars and opaques live in distinct axes — the lattice distinguishes
        // them structurally even though they share operational shape.
        let a = Descr::var(TypeVarId(0));
        let o = Descr::opaque_of("alpha");
        let i = a.intersect(&o);
        assert!(i.is_empty(), "α and opaque(\"alpha\") must not overlap");
    }

    // ------------------------------------------------------------------
    // fz-try.6 — instantiation and σ-collection
    // ------------------------------------------------------------------

    fn sigma_of(bindings: &[(u32, Descr)]) -> std::collections::HashMap<TypeVarId, Descr> {
        bindings
            .iter()
            .map(|(id, d)| (TypeVarId(*id), d.clone()))
            .collect()
    }

    #[test]
    fn has_vars_distinguishes_concrete_from_polymorphic() {
        assert!(!Descr::int().has_vars(), "int has no vars");
        assert!(
            !Descr::any().has_vars(),
            "any (cofinite-empty vars) has no specific vars"
        );
        assert!(Descr::var(TypeVarId(0)).has_vars(), "var(α0) has vars");
    }

    #[test]
    fn instantiate_replaces_top_level_var() {
        let pattern = Descr::var(TypeVarId(0));
        let result = pattern.instantiate(&sigma_of(&[(0, Descr::int())]));
        assert!(
            result.is_equiv(&Descr::int()),
            "α[α→int] = int, got {}",
            result
        );
    }

    #[test]
    fn instantiate_is_identity_when_no_vars_match() {
        let pattern = Descr::var(TypeVarId(0));
        let result = pattern.instantiate(&sigma_of(&[(1, Descr::int())]));
        // α0 not in σ; passes through unchanged.
        assert!(result.is_equiv(&pattern), "α0[α1→int] = α0, got {}", result);
    }

    #[test]
    fn instantiate_walks_into_lists() {
        // list of α → list of int under σ.
        let list_of_var = Descr::list_of(Descr::var(TypeVarId(0)));
        let result = list_of_var.instantiate(&sigma_of(&[(0, Descr::int())]));
        let list_of_int = Descr::list_of(Descr::int());
        assert!(
            result.is_equiv(&list_of_int),
            "list(α)[α→int] = list(int), got {}",
            result
        );
    }

    #[test]
    fn instantiate_walks_into_tuples() {
        // tuple(α, β) → tuple(int, str) under σ.
        let t = Descr::tuple_of(vec![Descr::var(TypeVarId(0)), Descr::var(TypeVarId(1))]);
        let result = t.instantiate(&sigma_of(&[(0, Descr::int()), (1, Descr::str_t())]));
        let expected = Descr::tuple_of(vec![Descr::int(), Descr::str_t()]);
        assert!(
            result.is_equiv(&expected),
            "tuple(α,β)[α→int,β→str] = tuple(int,str), got {}",
            result
        );
    }

    #[test]
    fn instantiate_walks_into_arrow_args_and_ret() {
        // (α) -> β under σ = {α→int, β→bool} becomes (int) -> bool.
        let arrow = Descr {
            funcs: vec![Conj::pos_of(ArrowSig {
                args: vec![Descr::var(TypeVarId(0))],
                ret: Box::new(Descr::var(TypeVarId(1))),
                lit: None,
            })],
            ..Descr::none()
        };
        let result = arrow.instantiate(&sigma_of(&[(0, Descr::int()), (1, Descr::bool_t())]));
        // Pull the (single) clause and check its shape.
        assert_eq!(result.funcs.len(), 1);
        let clause = &result.funcs[0];
        assert_eq!(clause.pos.len(), 1);
        let sig = &clause.pos[0];
        assert!(sig.args[0].is_equiv(&Descr::int()), "arg should be int");
        assert!(sig.ret.is_equiv(&Descr::bool_t()), "ret should be bool");
    }

    #[test]
    fn instantiate_preserves_lit_tag_on_arrow() {
        let lit = ClosureLit {
            fn_id: crate::fz_ir::FnId(42),
            captures: vec![],
        };
        let arrow = Descr {
            funcs: vec![Conj::pos_of(ArrowSig {
                args: vec![Descr::var(TypeVarId(0))],
                ret: Box::new(Descr::int()),
                lit: Some(lit.clone()),
            })],
            ..Descr::none()
        };
        let result = arrow.instantiate(&sigma_of(&[(0, Descr::int())]));
        // The lit tag must survive the walk so closure-identity tracking
        // downstream still resolves to the same closure value.
        assert!(result.funcs[0].pos[0].lit.is_some());
        let preserved = result.funcs[0].pos[0].lit.as_ref().unwrap();
        assert_eq!(preserved.fn_id, lit.fn_id);
        assert_eq!(preserved.captures, lit.captures);
    }

    #[test]
    fn collect_subst_binds_top_level_var_to_witness() {
        let mut sigma = std::collections::HashMap::new();
        Descr::collect_subst_into(&Descr::var(TypeVarId(0)), &Descr::int(), &mut sigma);
        assert_eq!(sigma.len(), 1);
        assert!(sigma[&TypeVarId(0)].is_equiv(&Descr::int()));
    }

    #[test]
    fn collect_subst_is_noop_on_concrete_pattern() {
        let mut sigma = std::collections::HashMap::new();
        Descr::collect_subst_into(&Descr::int(), &Descr::int(), &mut sigma);
        assert!(sigma.is_empty(), "no vars in pattern means no bindings");
    }

    #[test]
    fn collect_subst_then_instantiate_is_identity_on_concrete_args() {
        // The canonical call-site flow: pattern (Var α) ⇄ witness (int)
        // produces σ = {α→int}; instantiating the *return* pattern Var(α)
        // with σ yields the witness back.
        let pat_arg = Descr::var(TypeVarId(0));
        let pat_ret = Descr::var(TypeVarId(0));
        let witness = Descr::int();
        let mut sigma = std::collections::HashMap::new();
        Descr::collect_subst_into(&pat_arg, &witness, &mut sigma);
        let resolved_ret = pat_ret.instantiate(&sigma);
        assert!(resolved_ret.is_equiv(&Descr::int()));
    }

    #[test]
    fn collect_subst_distinct_vars_bind_independently() {
        // (α, β) ⇄ (int, bool) ⇒ σ = {α→int, β→bool}.
        let mut sigma = std::collections::HashMap::new();
        Descr::collect_subst_into(&Descr::var(TypeVarId(0)), &Descr::int(), &mut sigma);
        Descr::collect_subst_into(&Descr::var(TypeVarId(1)), &Descr::bool_t(), &mut sigma);
        assert_eq!(sigma.len(), 2);
        assert!(sigma[&TypeVarId(0)].is_equiv(&Descr::int()));
        assert!(sigma[&TypeVarId(1)].is_equiv(&Descr::bool_t()));
    }

    // ------------------------------------------------------------------
    // fz-try.9 — algebra audit: type variables in every lattice operation
    //
    // Verifies that the structural lattice algebra (union, intersect, neg,
    // diff, is_subtype) handles the `vars` axis correctly and composes
    // with the other axes. The semantic "join law" from the design doc
    // (Var ⊔ Var = Any, Var ⊔ Concrete = Concrete via substitution) is a
    // distinct operation realized at substitution sites (instantiate),
    // not in the structural union — see docs/descr-cleanup.md §Join law.
    // ------------------------------------------------------------------

    #[test]
    fn algebra_audit_union_with_var_is_componentwise() {
        // Structural union: var ∪ int produces a Descr with both axes set.
        // (The design's "join with substitution" is operational and lives
        // at instantiate() — not here.)
        let a = Descr::var(TypeVarId(0));
        let u = a.union(&Descr::int());
        assert!(!u.vars.is_none(), "var axis must survive union");
        assert!(
            u.ints.is_any() || !u.ints.is_none(),
            "int axis must survive union"
        );
        // Subtypes both witnesses.
        assert!(a.is_subtype(&u));
        assert!(Descr::int().is_subtype(&u));
    }

    #[test]
    fn algebra_audit_union_distinct_vars_keeps_both() {
        let a = Descr::var(TypeVarId(0));
        let b = Descr::var(TypeVarId(1));
        let u = a.union(&b);
        // Both var ids are members of the union's `vars` axis.
        assert!(a.is_subtype(&u));
        assert!(b.is_subtype(&u));
    }

    #[test]
    fn algebra_audit_intersect_preserves_var_disjointness() {
        // var(α) ∩ int = none — vars are nominally disjoint from concrete.
        let a = Descr::var(TypeVarId(0));
        let i = a.intersect(&Descr::int());
        assert!(i.is_empty(), "var ∩ int must be empty, got {}", i);
        // var(α) ∩ var(α) = var(α).
        let i2 = a.intersect(&a);
        assert!(i2.is_equiv(&a));
        // var(α) ∩ var(β) = none.
        let b = Descr::var(TypeVarId(1));
        let i3 = a.intersect(&b);
        assert!(i3.is_empty());
    }

    #[test]
    fn algebra_audit_neg_complement_correct() {
        // ¬var(α) is the universe minus α. Its union with α is the universe.
        let a = Descr::var(TypeVarId(0));
        let nota = a.neg();
        let universe = a.union(&nota);
        assert!(
            universe.looks_full() || universe.is_equiv(&Descr::any()),
            "α ∪ ¬α must be the universe, got {}",
            universe
        );
        // α ∩ ¬α = none.
        let mt = a.intersect(&nota);
        assert!(mt.is_empty(), "α ∩ ¬α must be empty, got {}", mt);
    }

    #[test]
    fn algebra_audit_diff_extracts_var_correctly() {
        // (α ∪ int) \ int = α (var portion remains; int portion removed).
        let mixed = Descr::var(TypeVarId(0)).union(&Descr::int());
        let just_var = mixed.diff(&Descr::int());
        assert!(
            just_var.is_equiv(&Descr::var(TypeVarId(0))),
            "(α ∪ int) \\ int should be α, got {}",
            just_var
        );
    }

    #[test]
    fn algebra_audit_subtype_var_relationships() {
        let a = Descr::var(TypeVarId(0));
        let b = Descr::var(TypeVarId(1));
        // α ⊆ α
        assert!(a.is_subtype(&a));
        // α ⊆ any
        assert!(a.is_subtype(&Descr::any()));
        // none ⊆ α
        assert!(Descr::none().is_subtype(&a));
        // α ⊄ int (vars and ints are disjoint)
        assert!(!a.is_subtype(&Descr::int()));
        // int ⊄ α (same reason)
        assert!(!Descr::int().is_subtype(&a));
        // α ⊄ β (distinct vars, both nominal)
        assert!(!a.is_subtype(&b));
    }

    #[test]
    fn algebra_audit_var_in_list_element() {
        // list(α) ⊆ list(any); list(α) ⊄ list(int).
        let la = Descr::list_of(Descr::var(TypeVarId(0)));
        let la_any = Descr::list_of(Descr::any());
        let la_int = Descr::list_of(Descr::int());
        assert!(la.is_subtype(&la_any), "list(α) ⊆ list(any)");
        assert!(!la.is_subtype(&la_int), "list(α) ⊄ list(int)");
    }

    #[test]
    fn algebra_audit_instantiate_then_union_distributes() {
        // For any σ, instantiate(d1 ∪ d2, σ) ≡ instantiate(d1, σ) ∪
        // instantiate(d2, σ). Verified on a representative case.
        let d1 = Descr::var(TypeVarId(0));
        let d2 = Descr::var(TypeVarId(1));
        let sigma: std::collections::HashMap<TypeVarId, Descr> = [
            (TypeVarId(0), Descr::int()),
            (TypeVarId(1), Descr::bool_t()),
        ]
        .into_iter()
        .collect();
        let lhs = d1.union(&d2).instantiate(&sigma);
        let rhs = d1.instantiate(&sigma).union(&d2.instantiate(&sigma));
        assert!(lhs.is_equiv(&rhs), "{} ≢ {}", lhs, rhs);
    }

    #[test]
    fn algebra_audit_no_var_axis_pollution_in_concrete_round_trip() {
        // A Descr constructed without any var-axis manipulation must NOT
        // gain vars through any algebraic operation that doesn't introduce
        // them. Regression guard for accidental cross-axis bleed.
        let i = Descr::int();
        let s = Descr::str_t();
        let u = i.union(&s);
        assert!(u.vars.is_none(), "union of concrete descrs has no vars");
        let int_ = i.intersect(&s);
        assert!(
            int_.vars.is_none(),
            "intersect of concrete descrs has no vars"
        );
        let n = i.neg();
        // ¬int has saturated vars (cofinite) — that's correct; "not int"
        // includes vars in the universe. But has_vars() reports false
        // because there are no NAMED ids.
        assert!(!n.has_vars(), "¬int has no named vars to substitute");
    }

    // ------------------------------------------------------------------
    // fz-68x.2 — Component view API
    // ------------------------------------------------------------------

    fn count_components(d: &Descr) -> usize {
        d.components().count()
    }

    #[test]
    fn components_none_yields_nothing() {
        assert_eq!(count_components(&Descr::none()), 0);
    }

    #[test]
    fn components_any_yields_one_per_axis() {
        // 11 axes (fz-axu.22 deleted `strs`): basic, atoms, ints,
        // floats, opaques, brands, vars, tuples, lists, funcs, maps.
        assert_eq!(count_components(&Descr::any()), 11);
    }

    #[test]
    fn components_int_lit_yields_only_ints() {
        let d = Descr::int_lit(42);
        let mut found = None;
        for c in d.components() {
            match c {
                Component::Ints(v) => {
                    assert!(found.is_none(), "multiple Ints components");
                    found = v.singleton();
                }
                _ => panic!("unexpected component for int_lit(42)"),
            }
        }
        assert_eq!(found, Some(42));
    }

    #[test]
    fn components_atom_lit_yields_only_atoms() {
        let d = Descr::atom_lit("ok");
        let mut seen_atom = false;
        for c in d.components() {
            match c {
                Component::Atoms(v) => {
                    seen_atom = true;
                    let names: Vec<&str> = v.finite().unwrap().collect();
                    assert_eq!(names, vec!["ok"]);
                }
                _ => panic!("unexpected component for atom_lit"),
            }
        }
        assert!(seen_atom);
    }

    #[test]
    fn components_tuple_of_yields_only_tuples_with_correct_arity_and_projection() {
        let d = Descr::tuple_of(vec![Descr::int_lit(1), Descr::int_lit(2)]);
        let mut seen = false;
        for c in d.components() {
            match c {
                Component::Tuples(v) => {
                    seen = true;
                    let arities: Vec<usize> = v.arities().collect();
                    assert_eq!(arities, vec![2]);
                    let elems = v.project_all(2).unwrap();
                    assert_eq!(elems[0].as_int_singleton(), Some(1));
                    assert_eq!(elems[1].as_int_singleton(), Some(2));
                    // Out-of-band projections return None.
                    assert!(v.project_all(3).is_none());
                }
                _ => panic!("unexpected component for tuple_of"),
            }
        }
        assert!(seen);
    }

    #[test]
    fn components_list_of_yields_only_lists_with_joined_element_type() {
        let d = Descr::list_of(Descr::int());
        let mut seen = false;
        for c in d.components() {
            match c {
                Component::Lists(v) => {
                    seen = true;
                    let et = v.element_type();
                    assert!(et.is_equiv(&Descr::int()));
                }
                _ => panic!("unexpected component for list_of"),
            }
        }
        assert!(seen);
    }

    #[test]
    fn components_arrow_yields_funcs_and_exposes_args_ret() {
        let d = Descr::arrow(vec![Descr::int()], Descr::str_t());
        let mut seen = false;
        for c in d.components() {
            match c {
                Component::Funcs(v) => {
                    seen = true;
                    let arrows: Vec<_> = v.arrows().collect();
                    assert_eq!(arrows.len(), 1);
                    let a = arrows[0];
                    assert_eq!(a.args().len(), 1);
                    assert!(a.args()[0].is_equiv(&Descr::int()));
                    assert!(a.ret().is_equiv(&Descr::str_t()));
                    assert!(a.closure_lit().is_none());
                }
                _ => panic!("unexpected component for arrow"),
            }
        }
        assert!(seen);
    }

    #[test]
    fn components_var_yields_only_vars_axis() {
        let d = Descr::var(TypeVarId(7));
        let mut seen = false;
        for c in d.components() {
            match c {
                Component::Vars(v) => {
                    seen = true;
                    let ids: Vec<TypeVarId> = v.finite().unwrap().collect();
                    assert_eq!(ids, vec![TypeVarId(7)]);
                }
                _ => panic!("unexpected component for var"),
            }
        }
        assert!(seen);
    }

    #[test]
    fn components_var_union_int_yields_both_axes() {
        // Pins the trajectory: vars and concrete coexist in a single Descr
        // (matches algebra_audit_union_int_var_keeps_both); both components
        // must surface independently.
        let d = Descr::var(TypeVarId(0)).union(&Descr::int());
        let mut saw_vars = false;
        let mut saw_ints = false;
        for c in d.components() {
            match c {
                Component::Vars(_) => saw_vars = true,
                Component::Ints(_) => saw_ints = true,
                _ => panic!("unexpected component for var ∪ int"),
            }
        }
        assert!(saw_vars && saw_ints);
    }

    #[test]
    fn components_distinct_vars_collapse_to_one_vars_component() {
        // α ∪ β lives in a single vars-axis (finite set {α, β}). The
        // iterator yields ONE Component::Vars containing both ids — not
        // two separate var components.
        let d = Descr::var(TypeVarId(0)).union(&Descr::var(TypeVarId(1)));
        let mut count = 0;
        for c in d.components() {
            match c {
                Component::Vars(v) => {
                    count += 1;
                    let ids: Vec<TypeVarId> = v.finite().unwrap().collect();
                    assert_eq!(ids, vec![TypeVarId(0), TypeVarId(1)]);
                }
                _ => panic!("unexpected component for var ∪ var"),
            }
        }
        assert_eq!(count, 1, "vars axis surfaces as exactly one component");
    }

    #[test]
    fn components_basic_vec_kinds_surface_as_basic_with_bits() {
        let d = Descr::vec_i64();
        let mut seen = false;
        for c in d.components() {
            match c {
                Component::Basic(bits) => {
                    seen = true;
                    assert!(bits.contains_all(BasicBits::VEC_I64));
                    assert!(!bits.contains_all(BasicBits::VEC_F64));
                }
                _ => panic!("unexpected component for vec(i64)"),
            }
        }
        assert!(seen);
    }

    #[test]
    fn components_map_field_lookup_joins_across_clauses() {
        // Single-clause map: open_map with one field. field() returns the value.
        let mut fields = std::collections::BTreeMap::new();
        fields.insert(MapKey::Atom("k".into()), Descr::int_lit(1));
        let m = Descr::map_of(fields);
        for c in m.components() {
            if let Component::Maps(v) = c {
                let got = v.lookup(&MapKey::Atom("k".into()));
                assert_eq!(got.and_then(|d| d.as_int_singleton()), Some(1));
                // "missing" on an open_map is `any | nil`, not None.
                let missing = v.lookup(&MapKey::Atom("missing".into())).unwrap();
                assert!(Descr::nil().is_subtype(&missing));
            }
        }
    }

    #[test]
    fn components_int_singleton_extraction_works() {
        // For wide int, singleton returns None.
        for c in Descr::int().components() {
            if let Component::Ints(v) = c {
                assert!(v.singleton().is_none());
            }
        }
        // For int_lit(42), singleton returns Some(42).
        for c in Descr::int_lit(42).components() {
            if let Component::Ints(v) = c {
                assert_eq!(v.singleton(), Some(42));
            }
        }
    }
}
