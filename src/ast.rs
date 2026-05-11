use crate::diag::{Span, SpanOrigin};
use std::rc::Rc;

/// Wraps an AST node with the source span that produced it. Every Expr
/// and Pattern reference in the AST is `Spanned<…>`; the outer enum
/// values themselves are unwrapped so pattern matching stays clean.
///
/// `origin` defaults to `Source` for parser-produced nodes. The macro
/// expansion pass walks decoded-Value subtrees and stamps
/// `SpanOrigin::Expanded` so a downstream diagnostic can show "expanded
/// from `<macro>` at <macro_call>".
#[derive(Debug, Clone)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
    pub origin: SpanOrigin,
}

impl<T> Spanned<T> {
    pub fn new(node: T, span: Span) -> Self {
        Self { node, span, origin: SpanOrigin::Source }
    }

    /// Synthesize a Spanned with no source position. Used by tests and by
    /// `value_to_expr` (which decodes runtime Values back to AST and has
    /// no original span). The macro expander stamps `SpanOrigin::Expanded`
    /// on these once it knows the call site.
    pub fn dummy(node: T) -> Self {
        Self { node, span: Span::DUMMY, origin: SpanOrigin::Source }
    }
}

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
    List(Vec<Spanned<Expr>>, Option<Box<Spanned<Expr>>>),  // [a, b, c | tail]
    Tuple(Vec<Spanned<Expr>>),
    /// Vector literal: monotyped contiguous storage; sigil determines element kind.
    /// `~v[1, 2, 3]` -> kind Numeric (I64/F64 inferred), `~b[0xff]` -> Bytes, `~bits[1,0,1]` -> Bits.
    VecLit(VecKind, Vec<Spanned<Expr>>),
    /// Bitstring literal: `<< field, field, ... >>` where each field carries a value
    /// (an arbitrary expression) and a type/size/endian/signedness/unit spec.
    Bitstring(Vec<BitField<Spanned<Expr>>>),
    Map(Vec<(Spanned<Expr>, Spanned<Expr>)>),
    /// %{m | k => v, ...} — functional update; each key must already exist.
    MapUpdate(Box<Spanned<Expr>>, Vec<(Spanned<Expr>, Spanned<Expr>)>),
    /// m[k] — bracket access; returns nil if key absent.
    Index(Box<Spanned<Expr>>, Box<Spanned<Expr>>),

    // call: target(args...)  — target is an expr (usually Var; module
    // qualification is desugared to Index by the parser)
    Call(Box<Spanned<Expr>>, Vec<Spanned<Expr>>),

    // operators
    BinOp(BinOp, Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    UnOp(UnOp, Box<Spanned<Expr>>),

    // control flow
    If(Box<Spanned<Expr>>, Box<Spanned<Expr>>, Option<Box<Spanned<Expr>>>),
    Case(Box<Spanned<Expr>>, Vec<MatchClause>),
    Cond(Vec<(Spanned<Expr>, Spanned<Expr>)>),
    With(Vec<WithBinding>, Box<Spanned<Expr>>, Vec<MatchClause>),

    // bindings
    // pattern = expr (rebinds names; immutable, just shadows)
    Match(Spanned<Pattern>, Box<Spanned<Expr>>),

    // sequence of expressions; result is the last
    Block(Vec<Spanned<Expr>>),

    // anonymous fn: fn (p1, p2) -> body  /  multi-clause via Case under the hood later
    Lambda(Vec<Spanned<Pattern>>, Box<Spanned<Expr>>),

    // macro support (fz-ul4.10):
    /// `quote do: <e>` / `quote do <e> end`. Eval reifies `e` to a Value,
    /// recursing through inner Unquote nodes which evaluate their inner
    /// expression and splice the resulting Value in place.
    Quote(Box<Spanned<Expr>>),
    /// `unquote(<e>)`. Only meaningful inside a Quote; outside, evaluation
    /// errors. The macro expansion pass (.10.3) is also responsible for
    /// rejecting any leftover Unquote nodes after expansion completes.
    Unquote(Box<Spanned<Expr>>),
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
    pub pattern: Spanned<Pattern>,
    pub guard: Option<Spanned<Expr>>,
    pub body: Spanned<Expr>,
    /// Span of the whole clause: `pattern when guard -> body`.
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum WithBinding {
    /// pattern <- expr
    Match(Spanned<Pattern>, Spanned<Expr>),
    /// arbitrary expression in the with-chain (rare)
    Bare(Spanned<Expr>),
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
    Tuple(Vec<Spanned<Pattern>>),
    List(Vec<Spanned<Pattern>>, Option<Box<Spanned<Pattern>>>), // [a, b | rest]
    Map(Vec<(Spanned<Pattern>, Spanned<Pattern>)>),
    /// pinned/literal pattern — `^name` would go here (deferred)
    /// As-pattern: name = pattern (Elixir lets you write it both ways)
    As(String, Box<Spanned<Pattern>>),
    /// Bitstring pattern: `<< field, field, ... >>`. Each field's `value` is a
    /// Pattern (binds variables or matches a literal); the spec governs how
    /// many bits to consume and how to interpret them.
    Bitstring(Vec<BitField<Spanned<Pattern>>>),
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
    pub params: Vec<Spanned<Pattern>>,
    pub guard: Option<Spanned<Expr>>,
    pub body: Spanned<Expr>,
    /// Span of the whole clause: from the `fn`/`defmacro` keyword through
    /// the body's last token.
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct FnDef {
    pub name: String,
    /// Span of just the name token. Useful for "redefinition" diagnostics.
    pub name_span: Span,
    pub clauses: Vec<FnClause>,
    pub is_macro: bool,
    /// `@doc "..."` attached above the first clause of this fn. Inert
    /// in v1 — stored for future doc tooling and the test runner (.16).
    pub doc: Option<String>,
    /// Span covering all clauses (and `@doc` if present).
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Item {
    Fn(FnDef),
    Module(ModuleDef),
    /// `alias A.B.C` (as_name = "C") or `alias A.B.C, as: D` (as_name = "D").
    /// Only valid inside a defmodule body; the resolver consumes these and
    /// they don't survive into the flattened Program.
    Alias { full_path: Vec<String>, as_name: String, span: Span },
    /// `import Mod` / `import Mod, only: [f: 1, g: 2]` /
    /// `import Mod, except: [...]`. Only valid inside a defmodule body;
    /// resolver-consumed.
    Import {
        path: Vec<String>,
        /// Whitelist of (name, arity) pairs. None means "all fns in the
        /// imported module". Mutually exclusive with `except`.
        only: Option<Vec<(String, usize)>>,
        /// Blacklist of (name, arity) pairs.
        except: Option<Vec<(String, usize)>>,
        span: Span,
    },
    /// A macro invocation at item-position (top of program or top of a
    /// defmodule body): `test("name") do <body> end` parses as
    /// MacroCall { name: "test", args: [Str("name"), Block([...])] }.
    /// .16.3's expansion pass replaces these with the items the macro
    /// returns (typically Item::Fn). Surviving instances at downstream
    /// stages are an error.
    ///
    /// `parent_module` is set by the resolver when the MacroCall was
    /// nested inside a defmodule body — the spliced fn names are then
    /// qualified under that path so tests written inside `defmodule
    /// MyTest do ... end` land as `MyTest.test_xxx`. At top-level it's
    /// `None`.
    MacroCall {
        name: String,
        name_span: Span,
        args: Vec<Spanned<Expr>>,
        parent_module: Option<String>,
        span: Span,
    },
}

#[derive(Debug, Clone)]
pub struct ModuleDef {
    pub name: String,
    pub name_span: Span,
    /// In .18.1 the body holds only Item::Fn (incl. defmacro). Nested
    /// modules join in .18.2 (recursive Item::Module here).
    pub items: Vec<Rc<Item>>,
    /// `@moduledoc "..."` attached at the top of the module body.
    /// Inert in v1.
    pub moduledoc: Option<String>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Program {
    pub items: Vec<Rc<Item>>,
}
