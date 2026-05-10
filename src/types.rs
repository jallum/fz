//! Set-theoretic type descriptors.
//!
//! A `Descr` represents a set of values. The lattice has top (`any` — every
//! value) and bottom (`none` — no value), and is closed under union,
//! intersection, and complement (those operations land in the next ticket).
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
//! This ticket: representation + constructors + a debug printer. Operations
//! (union/intersect/diff/neg) and subtyping land in fz-ul4.2 / fz-ul4.3.

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
/// The next ticket will define union/intersect/normalize over these.
#[derive(Clone, PartialEq, Eq, Hash, Default)]
pub struct Conj<T> {
    pub pos: Vec<T>,
    pub neg: Vec<T>,
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
    /// DNF over tuple shapes. Empty Vec = no tuples in this descriptor.
    pub tuples: Vec<Conj<TupleSig>>,
    /// DNF over list-of-T shapes.
    pub lists:  Vec<Conj<ListSig>>,
    /// DNF over function arrows.
    pub funcs:  Vec<Conj<ArrowSig>>,
    /// `true` means structural parts are "top" — every tuple, every list,
    /// every function. Set by `Descr::any()`. Operations in the next ticket
    /// will normalize this away (representing top as a saturated DNF), but
    /// for the constructor pass it's a clean way to spell `any`.
    pub structurals_top: bool,
}

impl Descr {
    // ---- top / bottom ----

    pub fn any() -> Self {
        Descr {
            basic: BasicBits::ALL,
            atoms: AtomSet::any(),
            tuples: Vec::new(),
            lists: Vec::new(),
            funcs: Vec::new(),
            structurals_top: true,
        }
    }

    pub fn none() -> Self {
        Descr {
            basic: BasicBits::NONE,
            atoms: AtomSet::none(),
            tuples: Vec::new(),
            lists: Vec::new(),
            funcs: Vec::new(),
            structurals_top: false,
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

    /// True if this descriptor has been built only from `none()` constructors
    /// (no operations applied yet). With operations landing next ticket, this
    /// is a structural check, not a true emptiness check — that's fz-ul4.3.
    pub fn looks_empty(&self) -> bool {
        self.basic.is_empty()
            && self.atoms.is_none()
            && self.tuples.is_empty()
            && self.lists.is_empty()
            && self.funcs.is_empty()
            && !self.structurals_top
    }
}

// ----------------------------------------------------------------------
// Display
// ----------------------------------------------------------------------

impl fmt::Display for Descr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.basic == BasicBits::ALL && self.atoms.is_any() && self.structurals_top {
            return write!(f, "any");
        }
        if self.looks_empty() {
            return write!(f, "none");
        }

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

        if self.structurals_top {
            parts.push("tuple".into());
            parts.push("list".into());
            parts.push("fn".into());
        } else {
            for c in &self.tuples { parts.push(format_tuple_clause(c)); }
            for c in &self.lists  { parts.push(format_list_clause(c)); }
            for c in &self.funcs  { parts.push(format_arrow_clause(c)); }
        }

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
    let all: Vec<String> = pos.iter().cloned()
        .chain(neg.iter().cloned())
        .collect();
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
