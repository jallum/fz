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

// ----------------------------------------------------------------------
// Basic-type bitmap
// ----------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct BasicBits(u32);

impl BasicBits {
    // Kinds without value-level distinctions (or where we choose not to track
    // them). int/float/str/atom moved into their own LiteralSet axes.
    pub const NIL: BasicBits = BasicBits(1 << 0);
    pub const BOOL: BasicBits = BasicBits(1 << 1);
    pub const VEC_I64: BasicBits = BasicBits(1 << 2);
    pub const VEC_F64: BasicBits = BasicBits(1 << 3);
    pub const VEC_U8: BasicBits = BasicBits(1 << 4);
    pub const VEC_BIT: BasicBits = BasicBits(1 << 5);

    pub const NONE: BasicBits = BasicBits(0);
    pub const ALL: BasicBits = BasicBits((1 << 6) - 1);
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
    (BasicBits::NIL, "nil"),
    (BasicBits::BOOL, "bool"),
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
pub struct LiteralSet<T: Ord + Clone> {
    pub set: BTreeSet<T>,
    pub cofinite: bool,
}

impl<T: Ord + Clone> LiteralSet<T> {
    pub fn none() -> Self {
        Self {
            set: BTreeSet::new(),
            cofinite: false,
        }
    }
    pub fn any() -> Self {
        Self {
            set: BTreeSet::new(),
            cofinite: true,
        }
    }
    pub fn lit(v: T) -> Self {
        let mut s = BTreeSet::new();
        s.insert(v);
        Self {
            set: s,
            cofinite: false,
        }
    }
    pub fn is_none(&self) -> bool {
        !self.cofinite && self.set.is_empty()
    }
    pub fn is_any(&self) -> bool {
        self.cofinite && self.set.is_empty()
    }

    pub fn union(&self, o: &Self) -> Self {
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
    pub fn intersect(&self, o: &Self) -> Self {
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
    pub fn neg(&self) -> Self {
        Self {
            set: self.set.clone(),
            cofinite: !self.cofinite,
        }
    }
}

pub type AtomSet = LiteralSet<String>;
pub type IntSet = LiteralSet<i64>;
pub type StrSet = LiteralSet<String>;
pub type FloatSet = LiteralSet<F64Bits>;

/// Bit-pattern wrapper around a non-NaN `f64` so we can put floats in
/// ordered/hashed sets. Two distinct bit patterns are considered distinct
/// values. `+0.0` and `-0.0` are distinct (matches IEEE bit equality but not
/// IEEE value equality — fine here, where the type system tracks values).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct F64Bits(u64);

impl F64Bits {
    pub fn new(f: f64) -> Self {
        assert!(!f.is_nan(), "F64Bits literal types do not support NaN");
        Self(f.to_bits())
    }
    pub fn get(self) -> f64 {
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
pub struct TupleSig {
    pub elems: Vec<Descr>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ListSig {
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
pub struct ClosureLit {
    pub fn_id: crate::fz_ir::FnId,
    pub captures: Vec<Descr>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ArrowSig {
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
pub struct MapSig {
    pub fields: std::collections::BTreeMap<MapKey, Descr>,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum MapKey {
    Atom(String),
    Int(i64),
    Str(String),
}

/// One conjunctive clause inside a DNF: `⋀ pos  ∧  ⋀ (¬neg)`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Conj<T> {
    pub pos: Vec<T>,
    pub neg: Vec<T>,
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
    pub fn pos_of(t: T) -> Self {
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
pub struct Descr {
    pub basic: BasicBits,
    pub atoms: AtomSet,
    pub ints: IntSet,
    pub floats: FloatSet,
    pub strs: StrSet,
    /// Nominal opaque-type tags. A value of opaque type `T` (declared as
    /// `@type T :: opaque U`) has `opaques = {"T"}` AND the underlying `U`
    /// axes populated. Opaque types are nominal: `T ⊄ U` even when the
    /// underlying type of `T` is `U`, because the opaques axis is non-empty
    /// and distinct from the plain-`U` descriptor (which has `opaques = ∅`).
    pub opaques: LiteralSet<String>,
    /// DNF over tuple shapes. Empty Vec = no tuples ("false"); a single
    /// `Conj::top()` clause = every tuple ("true").
    pub tuples: Vec<Conj<TupleSig>>,
    pub lists: Vec<Conj<ListSig>>,
    pub funcs: Vec<Conj<ArrowSig>>,
    pub maps: Vec<Conj<MapSig>>,
}

impl Descr {
    // ---- top / bottom ----

    pub fn any() -> Self {
        Descr {
            basic: BasicBits::ALL,
            atoms: AtomSet::any(),
            ints: IntSet::any(),
            floats: FloatSet::any(),
            strs: StrSet::any(),
            opaques: LiteralSet::any(),
            tuples: vec![Conj::top()],
            lists: vec![Conj::top()],
            funcs: vec![Conj::top()],
            maps: vec![Conj::top()],
        }
    }

    pub fn none() -> Self {
        Descr {
            basic: BasicBits::NONE,
            atoms: AtomSet::none(),
            ints: IntSet::none(),
            floats: FloatSet::none(),
            strs: StrSet::none(),
            opaques: LiteralSet::none(),
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
    pub fn opaque_of(name: impl Into<String>) -> Self {
        let mut d = Self::none();
        d.opaques = LiteralSet::lit(name.into());
        d
    }

    // ---- basic types ----

    fn from_basic(b: BasicBits) -> Self {
        let mut d = Self::none();
        d.basic = b;
        d
    }
    pub fn nil() -> Self {
        Self::from_basic(BasicBits::NIL)
    }
    pub fn bool_t() -> Self {
        Self::from_basic(BasicBits::BOOL)
    }
    /// All atom literals (no other axis). Used by VR.5a (typed equality) to
    /// recognise atom-monomorphic operands and lower `==` to a single icmp
    /// without going through fz_value_eq.
    pub fn atom_top() -> Self {
        let mut d = Self::none();
        d.atoms = AtomSet::any();
        d
    }
    pub fn vec_i64() -> Self {
        Self::from_basic(BasicBits::VEC_I64)
    }
    pub fn vec_f64() -> Self {
        Self::from_basic(BasicBits::VEC_F64)
    }
    pub fn vec_u8() -> Self {
        Self::from_basic(BasicBits::VEC_U8)
    }
    pub fn vec_bit() -> Self {
        Self::from_basic(BasicBits::VEC_BIT)
    }

    // ---- singletons (atoms / ints / floats / strs) ----

    pub fn atom_lit(name: impl Into<String>) -> Self {
        let mut d = Self::none();
        d.atoms = AtomSet::lit(name.into());
        d
    }

    /// "any int" — top of the int axis.
    pub fn int() -> Self {
        let mut d = Self::none();
        d.ints = IntSet::any();
        d
    }
    pub fn int_lit(n: i64) -> Self {
        let mut d = Self::none();
        d.ints = IntSet::lit(n);
        d
    }

    /// fz-zmu fz-ul4.dce.2 — If this Descr is a pure singleton int (exactly one
    /// integer value with all other type axes empty), return that integer.
    /// Used by ir_fold to detect BinOp results the typer proved to a constant.
    pub fn as_int_singleton(&self) -> Option<i64> {
        if !self.ints.cofinite
            && self.ints.set.len() == 1
            && self.atoms.is_none()
            && self.floats.is_none()
            && self.strs.is_none()
            && self.basic.is_empty()
            && self.tuples.is_empty()
            && self.lists.is_empty()
            && self.funcs.is_empty()
            && self.maps.is_empty()
        {
            self.ints.set.iter().next().copied()
        } else {
            None
        }
    }

    /// Top of the string/binary axis. Promoted from test-only in
    /// fz-ul4.31.1 to let the type-expression parser lower `binary` to
    /// the correct Descr. (`dead_code` allowed: production consumers
    /// land in .31.4 when @spec wires it in.)
    #[allow(dead_code)]
    pub fn str_t() -> Self {
        let mut d = Self::none();
        d.strs = StrSet::any();
        d
    }

    pub fn float() -> Self {
        let mut d = Self::none();
        d.floats = FloatSet::any();
        d
    }
    pub fn float_lit(f: f64) -> Self {
        let mut d = Self::none();
        d.floats = FloatSet::lit(F64Bits::new(f));
        d
    }

    pub fn str_lit(s: impl Into<String>) -> Self {
        let mut d = Self::none();
        d.strs = StrSet::lit(s.into());
        d
    }

    // ---- structurals (single positive clause each — composition lands in fz-ul4.2) ----

    pub fn tuple_of(elems: impl IntoIterator<Item = Descr>) -> Self {
        let sig = TupleSig {
            elems: elems.into_iter().collect(),
        };
        let mut d = Self::none();
        d.tuples.push(Conj::pos_of(sig));
        d
    }

    pub fn list_of(elem: Descr) -> Self {
        let sig = ListSig {
            elem: Box::new(elem),
        };
        let mut d = Self::none();
        d.lists.push(Conj::pos_of(sig));
        d
    }

    pub fn arrow(args: impl IntoIterator<Item = Descr>, ret: Descr) -> Self {
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
    pub fn closure_lit(fn_id: crate::fz_ir::FnId, captures: Vec<Descr>, n_args: usize) -> Self {
        let sig = ArrowSig {
            args: vec![Descr::any(); n_args],
            ret: Box::new(Descr::any()),
            lit: Some(ClosureLit { fn_id, captures }),
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
    pub fn as_closure_lit(&self) -> Option<&ClosureLit> {
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
    pub fn map_top() -> Self {
        let mut d = Self::none();
        d.maps.push(Conj::top());
        d
    }

    /// Open-shape map type with the given required (key, value-type) pairs.
    pub fn map_of(fields: impl IntoIterator<Item = (MapKey, Descr)>) -> Self {
        let sig = MapSig {
            fields: fields.into_iter().collect(),
        };
        let mut d = Self::none();
        d.maps.push(Conj::pos_of(sig));
        d
    }

    // ---- recognizers ----

    pub fn looks_empty(&self) -> bool {
        self.basic.is_empty()
            && self.atoms.is_none()
            && self.ints.is_none()
            && self.floats.is_none()
            && self.strs.is_none()
            && self.opaques.is_none()
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
    pub fn arrow_join_return(&self) -> Descr {
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

    pub fn looks_full(&self) -> bool {
        self.basic == BasicBits::ALL
            && self.atoms.is_any()
            && self.ints.is_any()
            && self.floats.is_any()
            && self.strs.is_any()
            && self.opaques.is_any()
            && is_dnf_top(&self.tuples)
            && is_dnf_top(&self.lists)
            && is_dnf_top(&self.funcs)
            && is_dnf_top(&self.maps)
    }

    // ---- operations ----

    pub fn union(&self, other: &Descr) -> Descr {
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
            strs: self.strs.union(&other.strs),
            opaques: self.opaques.union(&other.opaques),
            tuples,
            lists,
            funcs,
            maps,
        }
    }

    pub fn intersect(&self, other: &Descr) -> Descr {
        Descr {
            basic: self.basic.intersect(other.basic),
            atoms: self.atoms.intersect(&other.atoms),
            ints: self.ints.intersect(&other.ints),
            floats: self.floats.intersect(&other.floats),
            strs: self.strs.intersect(&other.strs),
            opaques: self.opaques.intersect(&other.opaques),
            tuples: dnf_intersect(&self.tuples, &other.tuples),
            lists: dnf_intersect(&self.lists, &other.lists),
            funcs: dnf_intersect(&self.funcs, &other.funcs),
            maps: dnf_intersect(&self.maps, &other.maps),
        }
    }

    pub fn neg(&self) -> Descr {
        Descr {
            basic: self.basic.neg(),
            atoms: self.atoms.neg(),
            ints: self.ints.neg(),
            floats: self.floats.neg(),
            strs: self.strs.neg(),
            opaques: self.opaques.neg(),
            tuples: dnf_neg(&self.tuples),
            lists: dnf_neg(&self.lists),
            funcs: dnf_neg(&self.funcs),
            maps: dnf_neg(&self.maps),
        }
    }

    pub fn diff(&self, other: &Descr) -> Descr {
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
    pub fn is_empty(&self) -> bool {
        let mut memo = Memo::default();
        self.is_empty_memo(&mut memo)
    }

    /// `self <: other` iff `(self ∧ ¬other)` is empty.
    pub fn is_subtype(&self, other: &Descr) -> bool {
        self.diff(other).is_empty()
    }

    /// Mutual subtyping.
    ///
    /// Structural equality is a sufficient (not necessary) condition for
    /// semantic equivalence — two `Descr` values with identical fields
    /// denote the same set, so `self == other` short-circuits the
    /// set-theoretic kernel. Misses fall through to the slow path.
    pub fn is_equiv(&self, other: &Descr) -> bool {
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
            && self.strs.is_none()
            && self.opaques.is_none()
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
        return false; // list(t) is non-empty (contains nil)
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
                    if a.intersect(b).is_empty_memo(memo) {
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
                .all(|(pc, nc)| nc.diff(pc).is_empty_memo(memo));
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
pub trait MergeSig: Clone + PartialEq {
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
                let caps: Vec<Descr> = la
                    .captures
                    .iter()
                    .zip(lb.captures.iter())
                    .map(|(x, y)| x.intersect(y))
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

        for (bit, name) in BASIC_NAMES {
            if self.basic.contains_all(*bit) {
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
        format_lit_set(&mut parts, &self.strs, "str", |s| format!("{:?}", s));
        format_lit_set(&mut parts, &self.atoms, "atom", |a| format!(":{}", a));
        format_lit_set(&mut parts, &self.opaques, "opaque", |n| n.clone());

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
    pub fn display_for_diag(&self) -> String {
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
        format_lit_set_capped(&mut parts, &self.floats, "float", CAP, |f| {
            format!("{}", f.get())
        });
        format_lit_set_capped(&mut parts, &self.strs, "str", CAP, |s| format!("{:?}", s));
        format_lit_set_capped(&mut parts, &self.atoms, "atom", CAP, |a| format!(":{}", a));
        format_lit_set_capped(&mut parts, &self.opaques, "opaque", CAP, |n| n.clone());

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
            let caps: Vec<String> = l.captures.iter().map(|d| format!("{}", d)).collect();
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
        MapKey::Str(s) => format!("{:?}", s),
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
        assert_eq!(Descr::str_t().to_string(), "str");
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
    fn tuple_constructor() {
        let t = Descr::tuple_of([Descr::int(), Descr::str_t()]);
        assert_eq!(t.to_string(), "{int, str}");
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
        assert!(n.strs.is_any());
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
        assert_eq!(u.to_string(), "{:ok, int} | {:error, str}");
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
        // list(none) only contains nil, so it's a subtype of every list type.
        let nil_only = Descr::list_of(Descr::none());
        assert!(nil_only.is_subtype(&Descr::list_of(Descr::int())));
        assert!(nil_only.is_subtype(&Descr::list_of(Descr::atom_top())));
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
    fn str_lit_singletons() {
        assert!(Descr::str_lit("hello").is_subtype(&Descr::str_t()));
        assert!(!Descr::str_lit("a").is_subtype(&Descr::str_lit("b")));
        assert_eq!(Descr::str_lit("hi").to_string(), "\"hi\"");
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
        assert_eq!(m.to_string(), "%{:age: int, :name: str}");
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
            BasicBits::NIL,
            BasicBits::BOOL,
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
        assert_eq!(tag.captures[0], Descr::int_lit(10));
        assert_eq!(tag.captures[1], Descr::int_lit(20));
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
        assert_eq!(tag.captures[0], Descr::int_lit(10));
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
        // crate::typer::widen on int_lit(N) → int. Lit FnId preserved.
        use crate::typer::widen;
        let a = Descr::closure_lit(fid(3), vec![Descr::int_lit(10)], 1);
        let w = widen(&a);
        let tag = w.as_closure_lit().expect("widen should preserve singleton");
        assert_eq!(tag.fn_id, fid(3));
        assert_eq!(
            tag.captures[0],
            Descr::int(),
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
}
