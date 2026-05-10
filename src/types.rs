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

use std::collections::BTreeSet;
use std::fmt;

// ----------------------------------------------------------------------
// Basic-type bitmap
// ----------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct BasicBits(u32);

impl BasicBits {
    pub const NIL:     BasicBits = BasicBits(1 << 0);
    pub const BOOL:    BasicBits = BasicBits(1 << 1);
    pub const INT:     BasicBits = BasicBits(1 << 2);
    pub const FLOAT:   BasicBits = BasicBits(1 << 3);
    pub const STR:     BasicBits = BasicBits(1 << 4);
    pub const VEC_I64: BasicBits = BasicBits(1 << 5);
    pub const VEC_F64: BasicBits = BasicBits(1 << 6);
    pub const VEC_U8:  BasicBits = BasicBits(1 << 7);
    pub const VEC_BIT: BasicBits = BasicBits(1 << 8);

    pub const NONE: BasicBits = BasicBits(0);
    pub const ALL:  BasicBits = BasicBits((1 << 9) - 1);

    pub const fn raw(self) -> u32 { self.0 }
    pub const fn from_raw(b: u32) -> Self { BasicBits(b) }
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
    (BasicBits::INT,     "int"),
    (BasicBits::FLOAT,   "float"),
    (BasicBits::STR,     "str"),
    (BasicBits::VEC_I64, "vec(i64)"),
    (BasicBits::VEC_F64, "vec(f64)"),
    (BasicBits::VEC_U8,  "vec(u8)"),
    (BasicBits::VEC_BIT, "vec(bit)"),
];

// ----------------------------------------------------------------------
// Atom set (finite or cofinite over atom literals)
// ----------------------------------------------------------------------

/// `Finite(s)` = exactly the atoms in `s` (so `Finite({})` = no atoms).
/// `Cofinite(s)` = every atom EXCEPT those in `s` (so `Cofinite({})` = all atoms).
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum AtomSet {
    Finite(BTreeSet<String>),
    Cofinite(BTreeSet<String>),
}

impl AtomSet {
    pub fn none() -> Self { AtomSet::Finite(BTreeSet::new()) }
    pub fn any()  -> Self { AtomSet::Cofinite(BTreeSet::new()) }
    pub fn lit(name: impl Into<String>) -> Self {
        let mut s = BTreeSet::new();
        s.insert(name.into());
        AtomSet::Finite(s)
    }
    pub fn is_none(&self) -> bool { matches!(self, AtomSet::Finite(s) if s.is_empty()) }
    pub fn is_any(&self)  -> bool { matches!(self, AtomSet::Cofinite(s) if s.is_empty()) }
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
    /// DNF over tuple shapes. Empty Vec = no tuples ("false"); a single
    /// `Conj::top()` clause = every tuple ("true").
    pub tuples: Vec<Conj<TupleSig>>,
    pub lists:  Vec<Conj<ListSig>>,
    pub funcs:  Vec<Conj<ArrowSig>>,
}

impl Descr {
    // ---- top / bottom ----

    pub fn any() -> Self {
        Descr {
            basic: BasicBits::ALL,
            atoms: AtomSet::any(),
            tuples: vec![Conj::top()],
            lists:  vec![Conj::top()],
            funcs:  vec![Conj::top()],
        }
    }

    pub fn none() -> Self {
        Descr {
            basic: BasicBits::NONE,
            atoms: AtomSet::none(),
            tuples: Vec::new(),
            lists: Vec::new(),
            funcs: Vec::new(),
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
    pub fn int()     -> Self { Self::from_basic(BasicBits::INT) }
    pub fn float()   -> Self { Self::from_basic(BasicBits::FLOAT) }
    pub fn str_t()   -> Self { Self::from_basic(BasicBits::STR) }
    pub fn vec_i64() -> Self { Self::from_basic(BasicBits::VEC_I64) }
    pub fn vec_f64() -> Self { Self::from_basic(BasicBits::VEC_F64) }
    pub fn vec_u8()  -> Self { Self::from_basic(BasicBits::VEC_U8) }
    pub fn vec_bit() -> Self { Self::from_basic(BasicBits::VEC_BIT) }

    // ---- atoms ----

    /// Every atom literal — the type usually called `atom`.
    pub fn atom_top() -> Self {
        let mut d = Self::none();
        d.atoms = AtomSet::any();
        d
    }

    /// A specific atom literal as a singleton type, e.g. `:ok`.
    pub fn atom_lit(name: impl Into<String>) -> Self {
        let mut d = Self::none();
        d.atoms = AtomSet::lit(name);
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

    // ---- recognizers ----

    /// True if every component is at its bottom. This is a *structural* check
    /// after the operations in this ticket; the real semantic emptiness
    /// (`is_empty`) lands in fz-ul4.3 and reasons about element subtyping.
    pub fn looks_empty(&self) -> bool {
        self.basic.is_empty()
            && self.atoms.is_none()
            && self.tuples.is_empty()
            && self.lists.is_empty()
            && self.funcs.is_empty()
    }

    /// True if every component is at its top.
    pub fn looks_full(&self) -> bool {
        self.basic == BasicBits::ALL
            && self.atoms.is_any()
            && is_dnf_top(&self.tuples)
            && is_dnf_top(&self.lists)
            && is_dnf_top(&self.funcs)
    }

    // ---- operations ----

    pub fn union(&self, other: &Descr) -> Descr {
        Descr {
            basic: self.basic.union(other.basic),
            atoms: self.atoms.union(&other.atoms),
            tuples: dnf_union(&self.tuples, &other.tuples),
            lists:  dnf_union(&self.lists,  &other.lists),
            funcs:  dnf_union(&self.funcs,  &other.funcs),
        }
    }

    pub fn intersect(&self, other: &Descr) -> Descr {
        Descr {
            basic: self.basic.intersect(other.basic),
            atoms: self.atoms.intersect(&other.atoms),
            tuples: dnf_intersect(&self.tuples, &other.tuples),
            lists:  dnf_intersect(&self.lists,  &other.lists),
            funcs:  dnf_intersect(&self.funcs,  &other.funcs),
        }
    }

    /// Negation within each kind, then unioned across kinds (since values
    /// belong to exactly one kind, ¬D restricted to kind K equals ¬(D ∩ K)
    /// within K). The result has saturated other-kind components.
    pub fn neg(&self) -> Descr {
        Descr {
            basic: self.basic.neg(),
            atoms: self.atoms.neg(),
            tuples: dnf_neg(&self.tuples),
            lists:  dnf_neg(&self.lists),
            funcs:  dnf_neg(&self.funcs),
        }
    }

    pub fn diff(&self, other: &Descr) -> Descr { self.intersect(&other.neg()) }
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
// AtomSet operations
// ----------------------------------------------------------------------

impl AtomSet {
    pub fn union(&self, o: &Self) -> Self {
        use AtomSet::*;
        match (self, o) {
            (Finite(a), Finite(b))     => Finite(a | b),
            (Finite(a), Cofinite(b))   => Cofinite(b - a),
            (Cofinite(a), Finite(b))   => Cofinite(a - b),
            (Cofinite(a), Cofinite(b)) => Cofinite(a & b),
        }
    }
    pub fn intersect(&self, o: &Self) -> Self {
        use AtomSet::*;
        match (self, o) {
            (Finite(a), Finite(b))     => Finite(a & b),
            (Finite(a), Cofinite(b))   => Finite(a - b),
            (Cofinite(a), Finite(b))   => Finite(b - a),
            (Cofinite(a), Cofinite(b)) => Cofinite(a | b),
        }
    }
    pub fn neg(&self) -> Self {
        match self {
            AtomSet::Finite(s)   => AtomSet::Cofinite(s.clone()),
            AtomSet::Cofinite(s) => AtomSet::Finite(s.clone()),
        }
    }
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

        match &self.atoms {
            AtomSet::Finite(s) => {
                for a in s { parts.push(format!(":{}", a)); }
            }
            AtomSet::Cofinite(s) if s.is_empty() => parts.push("atom".into()),
            AtomSet::Cofinite(s) => {
                let exc: Vec<String> = s.iter().map(|a| format!(":{}", a)).collect();
                parts.push(format!("atom \\ {{{}}}", exc.join(", ")));
            }
        }

        for c in &self.tuples { parts.push(format_tuple_clause(c)); }
        for c in &self.lists  { parts.push(format_list_clause(c)); }
        for c in &self.funcs  { parts.push(format_arrow_clause(c)); }

        write!(f, "{}", parts.join(" | "))
    }
}

impl fmt::Debug for Descr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}", self) }
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
        assert!(u.basic.contains_all(BasicBits::INT));
        assert!(u.basic.contains_all(BasicBits::FLOAT));
        assert_eq!(u.to_string(), "int | float");

        let inter = i.intersect(&f);
        assert!(inter.looks_empty());
    }

    #[test]
    fn neg_int_excludes_int_only_in_basics() {
        let n = Descr::int().neg();
        assert!(!n.basic.contains_all(BasicBits::INT));
        assert!(n.basic.contains_all(BasicBits::FLOAT));
        assert!(n.basic.contains_all(BasicBits::STR));
        // and the other kinds saturate
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
        // restricted to atoms: cofinite excluding "ok"
        match &n.atoms {
            AtomSet::Cofinite(s) => assert!(s.contains("ok") && s.len() == 1),
            other => panic!("expected Cofinite, got {:?}", other.is_any()),
        }
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
        // The saturated other-kind parts of ¬int (atoms/tuples/lists/funcs)
        // get killed by intersecting with the empty parts of (int|float),
        // so the result is structurally exactly float.
        assert_eq!(only_float, Descr::float());
    }

    #[test]
    fn basic_bits_flags_are_disjoint() {
        let bits = [
            BasicBits::NIL, BasicBits::BOOL, BasicBits::INT, BasicBits::FLOAT,
            BasicBits::STR, BasicBits::VEC_I64, BasicBits::VEC_F64,
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
}
