use std::rc::Rc;

#[derive(Debug, Clone)]
pub enum Expr {
    // literals
    Int(i64),
    Float(f64),
    Str(String),
    Atom(String),
    Bool(bool),
    Nil,

    // identifier reference
    Var(String),

    // collections
    List(Vec<Expr>, Option<Box<Expr>>),  // [a, b, c | tail]
    Tuple(Vec<Expr>),
    /// Vector literal: monotyped contiguous storage; sigil determines element kind.
    /// `~v[1, 2, 3]` -> kind Numeric (I64/F64 inferred), `~b[0xff]` -> Bytes, `~bits[1,0,1]` -> Bits.
    VecLit(VecKind, Vec<Expr>),
    /// Bitstring literal: `<< field, field, ... >>` where each field carries a value
    /// (an arbitrary expression) and a type/size/endian/signedness/unit spec.
    Bitstring(Vec<BitField<Expr>>),
    Map(Vec<(Expr, Expr)>),
    /// %{m | k => v, ...} — functional update; each key must already exist.
    MapUpdate(Box<Expr>, Vec<(Expr, Expr)>),
    /// m[k] — bracket access; returns nil if key absent.
    Index(Box<Expr>, Box<Expr>),

    // call: target(args...)  — target is an expr (usually Var or Dot)
    Call(Box<Expr>, Vec<Expr>),
    // qualified: Mod.fun  (lhs.name)
    Dot(Box<Expr>, String),

    // operators
    BinOp(BinOp, Box<Expr>, Box<Expr>),
    UnOp(UnOp, Box<Expr>),

    // control flow
    If(Box<Expr>, Box<Expr>, Option<Box<Expr>>),
    Case(Box<Expr>, Vec<MatchClause>),
    Cond(Vec<(Expr, Expr)>),
    With(Vec<WithBinding>, Box<Expr>, Vec<MatchClause>),

    // bindings
    // pattern = expr (rebinds names; immutable, just shadows)
    Match(Pattern, Box<Expr>),

    // sequence of expressions; result is the last
    Block(Vec<Expr>),

    // anonymous fn: fn (p1, p2) -> body  /  multi-clause via Case under the hood later
    Lambda(Vec<Pattern>, Box<Expr>),

    // macro support (fz-ul4.10):
    /// `quote do: <e>` / `quote do <e> end`. Eval reifies `e` to a Value,
    /// recursing through inner Unquote nodes which evaluate their inner
    /// expression and splice the resulting Value in place.
    Quote(Box<Expr>),
    /// `unquote(<e>)`. Only meaningful inside a Quote; outside, evaluation
    /// errors. The macro expansion pass (.10.3) is also responsible for
    /// rejecting any leftover Unquote nodes after expansion completes.
    Unquote(Box<Expr>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VecKind {
    Numeric,  // ~v  — I64 or F64 inferred from elements
    Bytes,    // ~b  — Vec(U8)
    Bits,     // ~bits — packed Vec(Bit)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add, Sub, Mul, Div, Rem,
    Eq, Neq, Lt, LtEq, Gt, GtEq,
    And, Or,
    Pipe,        // |>
    Cons,        // |  (head | tail)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp { Neg, Not }

#[derive(Debug, Clone)]
pub struct MatchClause {
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Expr,
}

#[derive(Debug, Clone)]
pub enum WithBinding {
    /// pattern <- expr
    Match(Pattern, Expr),
    /// arbitrary expression in the with-chain (rare)
    Bare(Expr),
}

#[derive(Debug, Clone)]
pub enum Pattern {
    Wildcard,
    Var(String),
    Int(i64),
    Float(f64),
    Str(String),
    Atom(String),
    Bool(bool),
    Nil,
    Tuple(Vec<Pattern>),
    List(Vec<Pattern>, Option<Box<Pattern>>), // [a, b | rest]
    Map(Vec<(Pattern, Pattern)>),
    /// pinned/literal pattern — `^name` would go here (deferred)
    /// As-pattern: name = pattern (Elixir lets you write it both ways)
    As(String, Box<Pattern>),
    /// Bitstring pattern: `<< field, field, ... >>`. Each field's `value` is a
    /// Pattern (binds variables or matches a literal); the spec governs how
    /// many bits to consume and how to interpret them.
    Bitstring(Vec<BitField<Pattern>>),
}

// ----------------------------------------------------------------------
// Bitstring fields (shared between expressions and patterns)
// ----------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct BitField<V> {
    pub value: V,
    pub spec: BitFieldSpec,
}

#[derive(Debug, Clone)]
pub struct BitFieldSpec {
    pub ty: BitType,
    pub size: Option<BitSize>,
    pub endian: Endian,
    pub signed: bool,
    pub unit: Option<u32>,
}

impl Default for BitFieldSpec {
    fn default() -> Self {
        Self { ty: BitType::Integer, size: None, endian: Endian::Big, signed: false, unit: None }
    }
}

impl BitFieldSpec {
    /// Resolve the unit (bits per element) for this spec, applying type-default
    /// when no explicit unit was provided.
    pub fn resolved_unit(&self) -> u32 {
        if let Some(u) = self.unit { return u; }
        match self.ty {
            BitType::Integer => 1,
            BitType::Float   => 1,
            BitType::Binary  => 8,
            BitType::Bits    => 1,
            BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => 1,
        }
    }
    /// Default size in elements when `size` is `None` (Elixir defaults). Returns
    /// `None` for binary/bits "rest" semantics.
    pub fn default_size(&self) -> Option<u32> {
        match self.ty {
            BitType::Integer => Some(8),
            BitType::Float => Some(64),
            BitType::Binary | BitType::Bits => None, // "rest"
            BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => None, // size is implicit per codepoint
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BitType { Integer, Float, Binary, Bits, Utf8, Utf16, Utf32 }

#[derive(Debug, Clone)]
pub enum BitSize {
    /// `::8`, `::16`, `::size(42)` with a literal
    Literal(u32),
    /// `::size(n)` where n is an in-scope variable name (or, in patterns, a previously-bound variable)
    Var(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Endian { Big, Little, Native }

#[derive(Debug, Clone)]
pub struct FnClause {
    pub params: Vec<Pattern>,
    pub guard: Option<Expr>,
    pub body: Expr,
}

#[derive(Debug, Clone)]
pub struct FnDef {
    pub name: String,
    pub clauses: Vec<FnClause>,
    pub is_macro: bool,
}

#[derive(Debug, Clone)]
pub enum Item {
    Fn(FnDef),
    Module(ModuleDef),
    /// `alias A.B.C` (as_name = "C") or `alias A.B.C, as: D` (as_name = "D").
    /// Only valid inside a defmodule body; the resolver consumes these and
    /// they don't survive into the flattened Program.
    Alias { full_path: Vec<String>, as_name: String },
}

#[derive(Debug, Clone)]
pub struct ModuleDef {
    pub name: String,
    /// In .18.1 the body holds only Item::Fn (incl. defmacro). Nested
    /// modules join in .18.2 (recursive Item::Module here).
    pub items: Vec<Rc<Item>>,
}

#[derive(Debug, Clone)]
pub struct Program {
    pub items: Vec<Rc<Item>>,
}
