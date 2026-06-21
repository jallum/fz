use crate::modules::identity::ModuleName;
use crate::parser::lexer::Token;
use crate::source::{Span, SpanOrigin};

/// A `Vec<Token>` representing a type expression whose resolution is deferred
/// until compiler2 resolves it against the captured namespace.
#[derive(Debug, Clone, PartialEq)]
pub struct TypeExprBody(pub Vec<Token>);

/// Wraps an AST node with the source span that produced it. Every Expr
/// and Pattern reference in the AST is `Spanned<…>`; the outer enum
/// values themselves are unwrapped so pattern matching stays clean.
///
/// `origin` defaults to `Source` for source-produced nodes. Macro expansion
/// stamps `SpanOrigin::Expanded` so a downstream diagnostic can show
/// "expanded from `<macro>` at <macro_call>".
#[derive(Debug, Clone)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
    pub origin: SpanOrigin,
}

impl<T> Spanned<T> {
    pub fn new(node: T, span: Span) -> Self {
        Self {
            node,
            span,
            origin: SpanOrigin::Source,
        }
    }

    /// Synthesize a Spanned with no source position. Used by tests and by
    /// generated nodes that have no original span.
    pub fn dummy(node: T) -> Self {
        Self {
            node,
            span: Span::DUMMY,
            origin: SpanOrigin::Source,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Expr {
    // literals
    Int(i64),
    Float(f64),
    /// fz-axu.10 (L2) — raw bytes of the quoted binary literal. Pre-L2
    /// this used Rust text storage; widened so byte payloads written as
    /// `"..."` can flow through to L3 desugaring without losing precision.
    /// The L3 pass validates UTF-8 and mints a `utf8`-branded bitstring;
    /// bare binaries skip the brand.
    Binary(Vec<u8>),
    Atom(String),
    Bool(bool),
    Nil,

    // identifier reference
    Var(String),

    /// Explicit function reference: `&name/arity` (fz-swt.5).
    /// `name` may be dotted (`Mod.fun`). Lowers to a thin `Prim::MakeFnRef`
    /// over the fn matching `(name, arity)` exactly, rather than the bare-name
    /// path's "first defined wins".
    FnRef {
        name: String,
        arity: usize,
    },

    /// fz-g58.2.6 — capture expression `&(...)`. The body may contain
    /// `CaptureArg` placeholders; the whole form desugars to a `Lambda` whose
    /// params are the placeholders, in fz-g58.15 (Arc 3). Until then it parses
    /// but neither evaluates nor lowers.
    Capture(Box<Spanned<Expr>>),
    /// fz-g58.2.6 — capture placeholder `&N` (1-based), only meaningful inside
    /// a `Capture` body. Desugars to the Nth lambda parameter in fz-g58.15.
    CaptureArg(usize),

    // collections
    List(Vec<Spanned<Expr>>, Option<Box<Spanned<Expr>>>), // [a, b, c | tail]
    Tuple(Vec<Spanned<Expr>>),
    /// Bitstring literal: `<< field, field, ... >>` where each field carries a value
    /// (an arbitrary expression) and a type/size/endian/signedness/unit spec.
    Bitstring(Vec<BitField<Spanned<Expr>>>),
    Map(Vec<(Spanned<Expr>, Spanned<Expr>)>),
    /// %{m | k => v, ...} — functional update; each key must already exist.
    MapUpdate(Box<Spanned<Expr>>, Vec<(Spanned<Expr>, Spanned<Expr>)>),
    /// `%Mod{field: value, ...}` — named struct construction.
    Struct {
        module: ModuleName,
        fields: Vec<(String, Spanned<Expr>)>,
    },
    /// m[k] — bracket access; returns nil if key absent.
    Index(Box<Spanned<Expr>>, Box<Spanned<Expr>>),

    // named call: target(args...) — target is an expr, usually Var. This is
    // distinct from anonymous-function call.
    Call(Box<Spanned<Expr>>, Vec<Spanned<Expr>>),
    // anonymous-function call: target.(args...)
    ClosureCall(Box<Spanned<Expr>>, Vec<Spanned<Expr>>),
    /// Call-argument type ascription: `expr :: TypeExpr`. Consumed by extern
    /// lowering.
    Ascribe(Box<Spanned<Expr>>, TypeExprBody),

    // operators
    BinOp(BinOp, Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    UnOp(UnOp, Box<Spanned<Expr>>),

    // control flow
    If(Box<Spanned<Expr>>, Box<Spanned<Expr>>, Option<Box<Spanned<Expr>>>),
    Case(Option<Box<Spanned<Expr>>>, Vec<MatchClause>),
    Cond(Vec<(Spanned<Expr>, Spanned<Expr>)>),
    With(Vec<WithBinding>, Box<Spanned<Expr>>, Vec<MatchClause>),
    /// fz-5vj — selective `receive do … after … end`. Each clause matches
    /// against a message popped from the mailbox; the optional `after`
    /// clause fires when no message matches within `timeout` milliseconds.
    /// See `docs/receive-matched.md §6, §7`.
    Receive {
        clauses: Vec<MatchClause>,
        after: Option<Box<AfterClause>>,
    },

    // bindings
    // pattern = expr (rebinds names; immutable, just shadows)
    Match(Spanned<Pattern>, Box<Spanned<Expr>>),

    // sequence of expressions; result is the last
    Block(Vec<Spanned<Expr>>),

    // anonymous fn: `fn p1 -> b1; p2 when g -> b2 end`. A non-empty list of
    // clauses, mirroring Elixir's `fn`. A single unguarded clause lowers and
    // evals directly; multi-clause and guarded forms desugar to a
    // pattern-matrix lambda in fz-g58.15 (Arc 3).
    Lambda(Vec<LambdaClause>),

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
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Neq,
    Lt,
    LtEq,
    Gt,
    GtEq,
    And,
    Or,
    Pipe, // |>
    Cons, // |  (head | tail)

    // Elixir-aligned operators. Like Pipe and Cons, these never reach IR
    // lowering: the frontend desugar pass (src/frontend/macros.rs) rewrites
    // them into ordinary calls or constructions first.
    ListConcat,   // ++   list concatenation
    ListSubtract, // --   list subtraction
    BinConcat,    // <>   binary concatenation
    Range,        // ..   a..b
    RangeStep,    // //   (a..b)//step — valid only with a Range on the left
    In,           // in   membership (desugars to Enum.member?)
    NotIn,        // not in
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Not,
}

#[derive(Debug, Clone)]
pub struct MatchClause {
    pub pattern: Spanned<Pattern>,
    pub guard: Option<Spanned<Expr>>,
    pub body: Spanned<Expr>,
    /// Span of the whole clause: `pattern when guard -> body`.
    pub span: Span,
}

/// fz-g58.2.5 — one clause of an anonymous `fn`: `params [when guard] -> body`.
/// A `fn` carries a non-empty `Vec<LambdaClause>` (see `Expr::Lambda`).
#[derive(Debug, Clone)]
pub struct LambdaClause {
    pub params: Vec<Spanned<Pattern>>,
    pub guard: Option<Spanned<Expr>>,
    pub body: Spanned<Expr>,
    /// Span of the whole clause: `params [when guard] -> body`.
    pub span: Span,
}

/// fz-5vj — `after <timeout_ms> -> <body>` tail clause on a `receive`.
/// `timeout` is an arbitrary expression so users can write `after 0`,
/// `after 500`, `after some_var`, etc. Semantics: `0` skips parking
/// entirely (peek-only); `infinity` (an atom, checked by the runtime)
/// means no timer.
#[derive(Debug, Clone)]
pub struct AfterClause {
    pub timeout: Spanned<Expr>,
    pub body: Spanned<Expr>,
    /// Span of the full `after <expr> -> <body>` clause; threaded into
    /// `ReceiveAfter.span` for diagnostics.
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
    /// fz-axu.10 (L2) — see `Expr::Binary`. Carries raw bytes; L3 narrows
    /// to UTF-8 + utf8 brand for matching against branded subjects.
    Binary(Vec<u8>),
    Atom(String),
    Bool(bool),
    Nil,
    Tuple(Vec<Spanned<Pattern>>),
    List(Vec<Spanned<Pattern>>, Option<Box<Spanned<Pattern>>>), // [a, b | rest]
    Map(Vec<(Spanned<Pattern>, Spanned<Pattern>)>),
    Struct {
        module: ModuleName,
        fields: Vec<(String, Spanned<Pattern>)>,
    },
    /// fz-5vj — `^name` pinned variable. The matcher compares the
    /// scrutinee against the value bound to `name` in the enclosing
    /// scope (snapshotted at pattern-match time for `receive`).
    Pinned(String),
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
        Self {
            ty: BitType::Integer,
            size: None,
            endian: Endian::Big,
            signed: false,
            unit: None,
        }
    }
}

impl BitFieldSpec {
    /// Resolve the unit (bits per element) for this spec, applying type-default
    /// when no explicit unit was provided.
    pub fn resolved_unit(&self) -> u32 {
        if let Some(u) = self.unit {
            return u;
        }
        match self.ty {
            BitType::Integer => 1,
            BitType::Float => 1,
            BitType::Binary => 8,
            BitType::Bits => 1,
            BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => 1,
        }
    }
    /// Default size in elements when `size` is `None` (Elixir defaults). Returns
    /// `None` for binary/bits "rest" semantics.
    pub fn default_size(&self) -> Option<u32> {
        match self.ty {
            BitType::Integer => Some(8),
            BitType::Float => Some(64),
            BitType::Binary | BitType::Bits => None,                 // "rest"
            BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => None, // size is implicit per codepoint
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BitType {
    Integer,
    Float,
    Binary,
    Bits,
    Utf8,
    Utf16,
    Utf32,
}

#[derive(Debug, Clone)]
pub enum BitSize {
    /// `::8`, `::16`, `::size(42)` with a literal
    Literal(u32),
    /// `::size(n)` where n is an in-scope variable name (or, in patterns, a previously-bound variable)
    Var(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Endian {
    Big,
    Little,
    Native,
}

#[derive(Debug, Clone)]
pub struct FnClause {
    pub params: Vec<Spanned<Pattern>>,
    /// fz-ty1.8: per-parameter type annotation tokens (`x :: T`).
    /// `param_annotations.len() == params.len()`. `None` means unannotated.
    pub param_annotations: Vec<Option<TypeExprBody>>,
    pub guard: Option<Spanned<Expr>>,
    pub body: Spanned<Expr>,
    /// Span of the whole clause: from the `fn`/`defmacro` keyword through
    /// the body's last token.
    pub span: Span,
}

/// fz-ul4.31.2 — uniform attribute carrier on parsed function/module surfaces.
#[derive(Debug, Clone)]
pub enum Attribute {
    /// `@doc "..."` attached above a fn/defmacro.
    Doc(String),
    /// `@moduledoc "..."` at the top of a module body.
    ModuleDoc(String),
    /// `@type Name :: <type-expr>`. The body is stored as raw tokens and
    /// resolved by compiler2 after the declaration namespace is known.
    TypeAlias(TypeAliasDecl),
    /// fz-ul4.31.4 — `@spec name(T1, T2) :: R` declaration attached
    /// above a fn/defmacro. Per-parameter and result type-expression
    /// bodies are stored as raw tokens and resolved by compiler2 against the
    /// captured namespace.
    Spec(SpecDecl),
}

#[derive(Debug, Clone)]
pub struct SpecDecl {
    pub name: String,
    /// Per-parameter type-expression body tokens. `param_body_tokens.len()`
    /// gives the declared arity (used for parse-time arity-vs-fn checks).
    pub param_body_tokens: Vec<TypeExprBody>,
    /// Result type-expression body tokens.
    pub result_body_tokens: TypeExprBody,
    /// Optional constrained type variables from `when t: Bound`.
    pub constraints: Vec<(String, TypeExprBody)>,
}

#[derive(Debug, Clone)]
pub struct TypeAliasDecl {
    pub name: String,
    pub name_span: Span,
    /// Formal type parameters from `@type name(t, u) :: ...`.
    /// Empty for monomorphic aliases.
    pub params: Vec<String>,
    /// Raw type-expression tokens for the body, terminated by but not
    /// including the trailing newline / eof / end.
    pub body_tokens: TypeExprBody,
    /// Span of the whole `@type ... :: ...` declaration.
    pub span: Span,
}
