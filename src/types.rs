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
    pub const NIL:     BasicBits = BasicBits(1 << 0);
    pub const BOOL:    BasicBits = BasicBits(1 << 1);
    pub const VEC_I64: BasicBits = BasicBits(1 << 2);
    pub const VEC_F64: BasicBits = BasicBits(1 << 3);
    pub const VEC_U8:  BasicBits = BasicBits(1 << 4);
    pub const VEC_BIT: BasicBits = BasicBits(1 << 5);

    pub const NONE: BasicBits = BasicBits(0);
    pub const ALL:  BasicBits = BasicBits((1 << 6) - 1);
    pub const fn contains_all(self, o: BasicBits) -> bool { (self.0 & o.0) == o.0 }
    pub const fn is_empty(self) -> bool { self.0 == 0 }
}

impl fmt::Debug for BasicBits {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "BasicBits(0b{:b})", self.0)
    }
}

const BASIC_NAMES: &[(BasicBits, &str)] = &[
    (BasicBits::NIL,     "nil"),
    (BasicBits::BOOL,    "bool"),
    (BasicBits::VEC_I64, "vec(i64)"),
    (BasicBits::VEC_F64, "vec(f64)"),
    (BasicBits::VEC_U8,  "vec(u8)"),
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
    pub fn none() -> Self { Self { set: BTreeSet::new(), cofinite: false } }
    pub fn any()  -> Self { Self { set: BTreeSet::new(), cofinite: true } }
    pub fn lit(v: T) -> Self {
        let mut s = BTreeSet::new(); s.insert(v);
        Self { set: s, cofinite: false }
    }
    pub fn is_none(&self) -> bool { !self.cofinite && self.set.is_empty() }
    pub fn is_any(&self)  -> bool {  self.cofinite && self.set.is_empty() }

    pub fn union(&self, o: &Self) -> Self {
        let (a, b) = (&self.set, &o.set);
        match (self.cofinite, o.cofinite) {
            (false, false) => Self { set: a | b, cofinite: false },
            (false, true)  => Self { set: b - a, cofinite: true },
            (true, false)  => Self { set: a - b, cofinite: true },
            (true, true)   => Self { set: a & b, cofinite: true },
        }
    }
    pub fn intersect(&self, o: &Self) -> Self {
        let (a, b) = (&self.set, &o.set);
        match (self.cofinite, o.cofinite) {
            (false, false) => Self { set: a & b, cofinite: false },
            (false, true)  => Self { set: a - b, cofinite: false },
            (true, false)  => Self { set: b - a, cofinite: false },
            (true, true)   => Self { set: a | b, cofinite: true },
        }
    }
    pub fn neg(&self) -> Self {
        Self { set: self.set.clone(), cofinite: !self.cofinite }
    }
}

pub type AtomSet  = LiteralSet<String>;
pub type IntSet   = LiteralSet<i64>;
pub type StrSet   = LiteralSet<String>;
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
    pub fn get(self) -> f64 { f64::from_bits(self.0) }
}
impl fmt::Debug for F64Bits {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}", self.get()) }
}

// ----------------------------------------------------------------------
// Structural signatures
// ----------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct TupleSig { pub elems: Vec<Descr> }

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ListSig  { pub elem: Box<Descr> }

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ArrowSig { pub args: Vec<Descr>, pub ret: Box<Descr> }

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
    pub const fn top() -> Self { Self { pos: Vec::new(), neg: Vec::new() } }
}
impl<T: Clone> Conj<T> {
    pub fn pos_of(t: T) -> Self { Self { pos: vec![t], neg: vec![] } }
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
    /// DNF over tuple shapes. Empty Vec = no tuples ("false"); a single
    /// `Conj::top()` clause = every tuple ("true").
    pub tuples: Vec<Conj<TupleSig>>,
    pub lists:  Vec<Conj<ListSig>>,
    pub funcs:  Vec<Conj<ArrowSig>>,
    pub maps:   Vec<Conj<MapSig>>,
}

impl Descr {
    // ---- top / bottom ----

    pub fn any() -> Self {
        Descr {
            basic: BasicBits::ALL,
            atoms: AtomSet::any(),
            ints:  IntSet::any(),
            floats: FloatSet::any(),
            strs:  StrSet::any(),
            tuples: vec![Conj::top()],
            lists:  vec![Conj::top()],
            funcs:  vec![Conj::top()],
            maps:   vec![Conj::top()],
        }
    }

    pub fn none() -> Self {
        Descr {
            basic: BasicBits::NONE,
            atoms: AtomSet::none(),
            ints:  IntSet::none(),
            floats: FloatSet::none(),
            strs:  StrSet::none(),
            tuples: Vec::new(),
            lists: Vec::new(),
            funcs: Vec::new(),
            maps:  Vec::new(),
        }
    }

    // ---- basic types ----

    fn from_basic(b: BasicBits) -> Self {
        let mut d = Self::none();
        d.basic = b;
        d
    }
    pub fn nil()     -> Self { Self::from_basic(BasicBits::NIL) }
    pub fn bool_t()  -> Self { Self::from_basic(BasicBits::BOOL) }
    pub fn vec_i64() -> Self { Self::from_basic(BasicBits::VEC_I64) }
    pub fn vec_f64() -> Self { Self::from_basic(BasicBits::VEC_F64) }
    pub fn vec_u8()  -> Self { Self::from_basic(BasicBits::VEC_U8) }
    pub fn vec_bit() -> Self { Self::from_basic(BasicBits::VEC_BIT) }

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
        let sig = TupleSig { elems: elems.into_iter().collect() };
        let mut d = Self::none();
        d.tuples.push(Conj::pos_of(sig));
        d
    }

    pub fn list_of(elem: Descr) -> Self {
        let sig = ListSig { elem: Box::new(elem) };
        let mut d = Self::none();
        d.lists.push(Conj::pos_of(sig));
        d
    }

    pub fn arrow(args: impl IntoIterator<Item = Descr>, ret: Descr) -> Self {
        let sig = ArrowSig { args: args.into_iter().collect(), ret: Box::new(ret) };
        let mut d = Self::none();
        d.funcs.push(Conj::pos_of(sig));
        d
    }

    /// Top of the map axis: any map.
    pub fn map_top() -> Self {
        let mut d = Self::none();
        d.maps.push(Conj::top());
        d
    }

    /// Open-shape map type with the given required (key, value-type) pairs.
    pub fn map_of(fields: impl IntoIterator<Item = (MapKey, Descr)>) -> Self {
        let sig = MapSig { fields: fields.into_iter().collect() };
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
            && self.tuples.is_empty()
            && self.lists.is_empty()
            && self.funcs.is_empty()
            && self.maps.is_empty()
    }

    pub fn looks_full(&self) -> bool {
        self.basic == BasicBits::ALL
            && self.atoms.is_any()
            && self.ints.is_any()
            && self.floats.is_any()
            && self.strs.is_any()
            && is_dnf_top(&self.tuples)
            && is_dnf_top(&self.lists)
            && is_dnf_top(&self.funcs)
            && is_dnf_top(&self.maps)
    }

    // ---- operations ----

    pub fn union(&self, other: &Descr) -> Descr {
        Descr {
            basic: self.basic.union(other.basic),
            atoms: self.atoms.union(&other.atoms),
            ints:  self.ints.union(&other.ints),
            floats: self.floats.union(&other.floats),
            strs:  self.strs.union(&other.strs),
            tuples: dnf_union(&self.tuples, &other.tuples),
            lists:  dnf_union(&self.lists,  &other.lists),
            funcs:  dnf_union(&self.funcs,  &other.funcs),
            maps:   dnf_union(&self.maps,   &other.maps),
        }
    }

    pub fn intersect(&self, other: &Descr) -> Descr {
        Descr {
            basic: self.basic.intersect(other.basic),
            atoms: self.atoms.intersect(&other.atoms),
            ints:  self.ints.intersect(&other.ints),
            floats: self.floats.intersect(&other.floats),
            strs:  self.strs.intersect(&other.strs),
            tuples: dnf_intersect(&self.tuples, &other.tuples),
            lists:  dnf_intersect(&self.lists,  &other.lists),
            funcs:  dnf_intersect(&self.funcs,  &other.funcs),
            maps:   dnf_intersect(&self.maps,   &other.maps),
        }
    }

    pub fn neg(&self) -> Descr {
        Descr {
            basic: self.basic.neg(),
            atoms: self.atoms.neg(),
            ints:  self.ints.neg(),
            floats: self.floats.neg(),
            strs:  self.strs.neg(),
            tuples: dnf_neg(&self.tuples),
            lists:  dnf_neg(&self.lists),
            funcs:  dnf_neg(&self.funcs),
            maps:   dnf_neg(&self.maps),
        }
    }

    pub fn diff(&self, other: &Descr) -> Descr { self.intersect(&other.neg()) }

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
    pub fn is_equiv(&self, other: &Descr) -> bool {
        self.is_subtype(other) && other.is_subtype(self)
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
    let negs: Vec<Vec<Descr>> = c.neg.iter()
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
        for p in &c.pos[1..] { t = t.intersect(&p.elem); }
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
            for i in 0..n_pos {
                if (mask >> i) & 1 == 1 {
                    union_in = union_in.union(&arrow_input(&p[i]));
                } else {
                    inter_out = inter_out.intersect(&p[i].ret);
                }
            }
            // Either inputs of P' cover s, OR outputs of P\P' refine v.
            if s.diff(&union_in).is_empty_memo(memo) { continue; }
            if inter_out.diff(&v).is_empty_memo(memo) { continue; }
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
            merged.entry(k.clone())
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
        if !n_keys_subset { continue; }
        let value_refines = n.fields.iter().all(|(k, nv)| {
            merged.get(k).map(|pv| pv.diff(nv).is_empty_memo(memo)).unwrap_or(false)
        });
        if value_refines { return true; }
    }
    false
}

// ----------------------------------------------------------------------
// BasicBits operations
// ----------------------------------------------------------------------

impl BasicBits {
    pub const fn union(self, o: BasicBits) -> BasicBits { BasicBits(self.0 | o.0) }
    pub const fn intersect(self, o: BasicBits) -> BasicBits { BasicBits(self.0 & o.0) }
    pub const fn neg(self) -> BasicBits { BasicBits(BasicBits::ALL.0 & !self.0) }
}

// ----------------------------------------------------------------------
// DNF operations
// ----------------------------------------------------------------------

fn dnf_union<T: Clone>(a: &[Conj<T>], b: &[Conj<T>]) -> Vec<Conj<T>> {
    let mut out = a.to_vec();
    out.extend_from_slice(b);
    out
}

fn dnf_intersect<T: Clone + PartialEq>(a: &[Conj<T>], b: &[Conj<T>]) -> Vec<Conj<T>> {
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
fn dnf_neg<T: Clone + PartialEq>(d: &[Conj<T>]) -> Vec<Conj<T>> {
    let mut acc: Vec<Conj<T>> = vec![Conj::top()]; // start with "true"
    for c in d {
        let neg_c = neg_clause(c);
        acc = dnf_intersect(&acc, &neg_c);
    }
    acc
}

fn merge_clauses<T: Clone + PartialEq>(a: &Conj<T>, b: &Conj<T>) -> Conj<T> {
    let mut pos = a.pos.clone();
    for x in &b.pos { if !pos.contains(x) { pos.push(x.clone()); } }
    let mut neg = a.neg.clone();
    for x in &b.neg { if !neg.contains(x) { neg.push(x.clone()); } }
    Conj { pos, neg }
}

/// ¬(⋀ pos ∧ ⋀ ¬neg) = ⋁ (¬p) ∨ ⋁ n  — one single-literal clause per element.
fn neg_clause<T: Clone>(c: &Conj<T>) -> Vec<Conj<T>> {
    let mut out: Vec<Conj<T>> = Vec::with_capacity(c.pos.len() + c.neg.len());
    for p in &c.pos { out.push(Conj { pos: vec![],         neg: vec![p.clone()] }); }
    for n in &c.neg { out.push(Conj { pos: vec![n.clone()], neg: vec![] }); }
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
        if self.looks_full() { return write!(f, "any"); }
        if self.looks_empty() { return write!(f, "none"); }

        let mut parts: Vec<String> = Vec::new();

        for (bit, name) in BASIC_NAMES {
            if self.basic.contains_all(*bit) { parts.push((*name).to_string()); }
        }

        format_lit_set(&mut parts, &self.ints,   "int",   |n| format!("{}", n));
        format_lit_set(&mut parts, &self.floats, "float", |f| format!("{}", f.get()));
        format_lit_set(&mut parts, &self.strs,   "str",   |s| format!("{:?}", s));
        format_lit_set(&mut parts, &self.atoms,  "atom",  |a| format!(":{}", a));

        for c in &self.tuples { parts.push(format_tuple_clause(c)); }
        for c in &self.lists  { parts.push(format_list_clause(c)); }
        for c in &self.funcs  { parts.push(format_arrow_clause(c)); }
        for c in &self.maps   { parts.push(format_map_clause(c)); }

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
        if self.looks_full() { return "any".into(); }
        if self.looks_empty() { return "none".into(); }

        let mut parts: Vec<String> = Vec::new();

        for (bit, name) in BASIC_NAMES {
            if self.basic.contains_all(*bit) { parts.push((*name).to_string()); }
        }

        format_lit_set_capped(&mut parts, &self.ints,   "int",   CAP, |n| format!("{}", n));
        format_lit_set_capped(&mut parts, &self.floats, "float", CAP, |f| format!("{}", f.get()));
        format_lit_set_capped(&mut parts, &self.strs,   "str",   CAP, |s| format!("{:?}", s));
        format_lit_set_capped(&mut parts, &self.atoms,  "atom",  CAP, |a| format!(":{}", a));

        for c in &self.tuples { parts.push(format_tuple_clause(c)); }
        for c in &self.lists  { parts.push(format_list_clause(c)); }
        for c in &self.funcs  { parts.push(format_arrow_clause(c)); }
        for c in &self.maps   { parts.push(format_map_clause(c)); }

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
    if s.is_none() { return; }
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}", self) }
}

fn format_lit_set<T: Ord + Clone>(
    parts: &mut Vec<String>,
    s: &LiteralSet<T>,
    top_name: &str,
    fmt_one: impl Fn(&T) -> String,
) {
    if s.is_none() { return; }
    if s.cofinite {
        if s.set.is_empty() {
            parts.push(top_name.into());
        } else {
            let exc: Vec<String> = s.set.iter().map(&fmt_one).collect();
            parts.push(format!("{} \\ {{{}}}", top_name, exc.join(", ")));
        }
    } else {
        for v in &s.set { parts.push(fmt_one(v)); }
    }
}

fn format_tuple_clause(c: &Conj<TupleSig>) -> String {
    let pos: Vec<String> = c.pos.iter().map(format_tuple).collect();
    let neg: Vec<String> = c.neg.iter().map(|t| format!("¬{}", format_tuple(t))).collect();
    join_clause(&pos, &neg, "tuple")
}
fn format_list_clause(c: &Conj<ListSig>) -> String {
    let pos: Vec<String> = c.pos.iter().map(format_list).collect();
    let neg: Vec<String> = c.neg.iter().map(|t| format!("¬{}", format_list(t))).collect();
    join_clause(&pos, &neg, "list")
}
fn format_arrow_clause(c: &Conj<ArrowSig>) -> String {
    let pos: Vec<String> = c.pos.iter().map(format_arrow).collect();
    let neg: Vec<String> = c.neg.iter().map(|t| format!("¬{}", format_arrow(t))).collect();
    join_clause(&pos, &neg, "fn")
}
fn format_tuple(t: &TupleSig) -> String {
    let inner: Vec<String> = t.elems.iter().map(|d| format!("{}", d)).collect();
    format!("{{{}}}", inner.join(", "))
}
fn format_list(t: &ListSig)  -> String { format!("list({})", t.elem) }
fn format_arrow(t: &ArrowSig) -> String {
    let args: Vec<String> = t.args.iter().map(|d| format!("{}", d)).collect();
    format!("({}) -> {}", args.join(", "), t.ret)
}
fn format_map_clause(c: &Conj<MapSig>) -> String {
    let pos: Vec<String> = c.pos.iter().map(format_map).collect();
    let neg: Vec<String> = c.neg.iter().map(|m| format!("¬{}", format_map(m))).collect();
    join_clause(&pos, &neg, "map")
}
fn format_map(m: &MapSig) -> String {
    let inner: Vec<String> = m.fields.iter().map(|(k, v)| format!("{}: {}", format_map_key(k), v)).collect();
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
    if all.is_empty() { top.to_string() } else { all.join(" & ") }
}

// ----------------------------------------------------------------------
// Tests
// ----------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // Test-only conveniences. `atom_top` / `str_t` are useful for type-algebra
    // tests that want "every atom" / "every string", but the live pipeline
    // never asks for those tops directly — it always narrows. `raw` is a
    // newtype probe used by axis-disjointness assertions.
    impl Descr {
        pub(super) fn atom_top() -> Self {
            let mut d = Self::none();
            d.atoms = AtomSet::any();
            d
        }
        pub(super) fn str_t() -> Self {
            let mut d = Self::none();
            d.strs = StrSet::any();
            d
        }
    }
    impl BasicBits {
        pub(super) const fn raw(self) -> u32 { self.0 }
    }

    #[test]
    fn top_and_bottom_render() {
        assert_eq!(Descr::any().to_string(), "any");
        assert_eq!(Descr::none().to_string(), "none");
    }

    #[test]
    fn each_basic_constructor_renders_its_name() {
        assert_eq!(Descr::nil().to_string(),     "nil");
        assert_eq!(Descr::bool_t().to_string(),  "bool");
        assert_eq!(Descr::int().to_string(),     "int");
        assert_eq!(Descr::float().to_string(),   "float");
        assert_eq!(Descr::str_t().to_string(),   "str");
        assert_eq!(Descr::vec_i64().to_string(), "vec(i64)");
        assert_eq!(Descr::vec_f64().to_string(), "vec(f64)");
        assert_eq!(Descr::vec_u8().to_string(),  "vec(u8)");
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
        // one clause from a × one clause from b = one merged clause with two positives
        assert_eq!(inter.tuples.len(), 1);
        assert_eq!(inter.tuples[0].pos.len(), 2);
        assert!(inter.tuples[0].neg.is_empty());
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
        assert!(!Descr::int().union(&Descr::float()).is_subtype(&Descr::int()));
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
        let parts = Descr::list_of(Descr::atom_lit("a"))
            .union(&Descr::list_of(Descr::atom_lit("b")));
        assert!(!mixed.is_subtype(&parts), "homogeneous lists do not cover mixed");
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
        assert!(!combined.is_subtype(&multi),
            "combined arrow loses the per-clause return refinement");
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
        assert!(Descr::list_of(Descr::int()).intersect(&Descr::tuple_of([Descr::int()])).is_empty());
    }

    #[test]
    fn ok_or_error_result_subtype() {
        // Result(int, atom) = {:ok, int} ∪ {:error, atom}
        // {:ok, int} <: Result(int, atom)
        let result_t = Descr::tuple_of([Descr::atom_lit("ok"), Descr::int()])
            .union(&Descr::tuple_of([Descr::atom_lit("error"), Descr::atom_top()]));
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
        assert_eq!(Descr::int_lit(0).union(&Descr::int_lit(1)).to_string(), "0 | 1");
    }

    // ---- maps ----

    fn ak(s: &str) -> MapKey { MapKey::Atom(s.into()) }

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
            BasicBits::NIL, BasicBits::BOOL,
            BasicBits::VEC_I64, BasicBits::VEC_F64,
            BasicBits::VEC_U8, BasicBits::VEC_BIT,
        ];
        for (i, a) in bits.iter().enumerate() {
            for b in &bits[i+1..] {
                assert_eq!(a.raw() & b.raw(), 0,
                    "bits should be disjoint: {:?} vs {:?}", a, b);
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
        assert!(pipe_parts.len() == 6, "expected 5 ints + ellipsis, got: {}", s);
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
}
