use crate::diag::{Span, SpanOrigin};
use std::rc::Rc;

/// A `Vec<Token>` representing a type expression whose resolution is deferred
/// until the full module type environment is available. Used in five AST fields
/// that are parsed eagerly but resolved later via `parse_type_expr`.
#[derive(Debug, Clone)]
pub struct TypeExprBody(pub Vec<crate::lexer::Token>);

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
        Self {
            node,
            span,
            origin: SpanOrigin::Source,
        }
    }

    /// Synthesize a Spanned with no source position. Used by tests and by
    /// `value_to_expr` (which decodes runtime Values back to AST and has
    /// no original span). The macro expander stamps `SpanOrigin::Expanded`
    /// on these once it knows the call site.
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
    /// `name` may be dotted (`Mod.fun`). Lowers to a zero-capture
    /// `Prim::MakeClosure` over the fn matching `(name, arity)` exactly,
    /// rather than the bare-name path's "first defined wins".
    FnRef {
        name: String,
        arity: usize,
    },

    // collections
    List(Vec<Spanned<Expr>>, Option<Box<Spanned<Expr>>>), // [a, b, c | tail]
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
    If(
        Box<Spanned<Expr>>,
        Box<Spanned<Expr>>,
        Option<Box<Spanned<Expr>>>,
    ),
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
    Numeric, // ~v  — I64 or F64 inferred from elements
    Bytes,   // ~b  — Vec(U8)
    Bits,    // ~bits — packed Vec(Bit)
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
            BitType::Binary | BitType::Bits => None, // "rest"
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

/// fz-ul4.31.2 — uniform attribute carrier on FnDef / ModuleDef.
/// Replaces the prior `doc: Option<String>` / `moduledoc: Option<String>`
/// fields with a list of typed attribute variants. .31.4 adds `Spec` —
/// extending this enum doesn't churn callers that already consume via
/// `attrs: Vec<Attribute>`.
#[derive(Debug, Clone)]
pub enum Attribute {
    /// `@doc "..."` attached above a fn/defmacro.
    Doc(String),
    /// `@moduledoc "..."` at the top of a module body.
    ModuleDoc(String),
    /// fz-ul4.31.3 — `@type Name :: <type-expr>`. The body is stored as
    /// raw tokens and parsed via `type_expr::build_module_type_env`
    /// after all aliases in a module are collected, so forward
    /// references resolve and cycles are detectable.
    TypeAlias(TypeAliasDecl),
    /// fz-ul4.31.4 — `@spec name(T1, T2) :: R` declaration attached
    /// above a fn/defmacro. Per-parameter and result type-expression
    /// bodies are stored as raw tokens; `SpecDecl::resolve` lowers them
    /// to types against the enclosing module's `ModuleTypeEnv`.
    Spec(SpecDecl),
}

#[derive(Debug, Clone)]
pub struct SpecDecl {
    pub name: String,
    /// Span of the fn-name token in the `@spec` header. Used by .31.5
    /// diagnostics; unread at parse time.
    #[allow(dead_code)]
    pub name_span: Span,
    /// Per-parameter type-expression body tokens. `param_body_tokens.len()`
    /// gives the declared arity (used for parse-time arity-vs-fn checks).
    pub param_body_tokens: Vec<TypeExprBody>,
    /// Result type-expression body tokens.
    pub result_body_tokens: TypeExprBody,
    /// Span of the whole `@spec ... :: ...` declaration. Used by .31.5
    /// diagnostics.
    #[allow(dead_code)]
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct TypeAliasDecl {
    pub name: String,
    pub name_span: Span,
    /// Raw type-expression tokens for the body, terminated by but not
    /// including the trailing newline / eof / end.
    pub body_tokens: TypeExprBody,
    /// Span of the whole `@type ... :: ...` declaration.
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct FnDef {
    pub name: String,
    /// Span of just the name token. Useful for "redefinition" diagnostics.
    pub name_span: Span,
    pub clauses: Vec<FnClause>,
    pub is_macro: bool,
    /// `Some("C")` for `extern "C" fn` declarations; `None` for regular fns.
    #[allow(dead_code)] // read by ir_lower in T3
    pub extern_abi: Option<String>,
    /// Per-parameter type name strings for `extern "C" fn` declarations.
    /// `extern_params.len()` gives the arity. Empty for regular fns.
    #[allow(dead_code)] // read by ir_lower
    pub extern_params: Vec<String>,
    /// Raw return-type tokens from `:: RetType`. Empty for regular fns.
    /// Kept as tokens because lowering consults the type_env alias table.
    #[allow(dead_code)] // read by ir_lower
    pub extern_ret_tokens: TypeExprBody,
    /// Attributes attached above the first clause of this fn. The REPL
    /// surfaces `Attribute::Doc` via `?<name>`. Empty when no `@…`
    /// preceded the fn.
    pub attrs: Vec<Attribute>,
    /// Span covering all clauses (and any `@…` if present).
    pub span: Span,
}

impl FnDef {
    /// Returns the first `@doc` string attached to this fn, if any.
    pub fn doc(&self) -> Option<&str> {
        self.attrs.iter().find_map(|a| match a {
            Attribute::Doc(s) => Some(s.as_str()),
            _ => None,
        })
    }
}

#[derive(Debug, Clone)]
pub enum Item {
    Fn(FnDef),
    Module(ModuleDef),
    /// `alias A.B.C` (as_name = "C") or `alias A.B.C, as: D` (as_name = "D").
    /// Only valid inside a defmodule body; the resolver consumes these and
    /// they don't survive into the flattened Program.
    Alias {
        full_path: Vec<String>,
        as_name: String,
        span: Span,
    },
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
    /// MacroCall { name: "test", args: [Binary("name"), Block([...])] }.
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
    /// Attributes attached at the top of the module body. The resolver
    /// surfaces `Attribute::ModuleDoc` into `Program.moduledocs` keyed by
    /// the module's qualified path.
    pub attrs: Vec<Attribute>,
    pub span: Span,
}

impl ModuleDef {
    /// Returns the first `@moduledoc` string attached to this module, if any.
    pub fn moduledoc(&self) -> Option<&str> {
        self.attrs.iter().find_map(|a| match a {
            Attribute::ModuleDoc(s) => Some(s.as_str()),
            _ => None,
        })
    }
}

#[derive(Debug, Clone, Default)]
pub struct Program {
    pub items: Vec<Rc<Item>>,
    /// Qualified-module-path → `@moduledoc "..."` text. Populated by
    /// `resolve::flatten_modules` (the only stage that still sees
    /// `ModuleDef`s). Used by the REPL's `?M` query.
    pub module_docs: std::collections::HashMap<String, String>,
    /// fz-ul4.31.5 — Qualified-module-path → resolved `@type` aliases
    /// for that module. Built by `resolve::flatten_modules` (which is
    /// where the original `ModuleDef.attrs` are still visible). Used by
    /// `spec_check::validate_specs` to resolve `@spec` bodies against
    /// the right env. Top-level fns (outside any defmodule) use the
    /// empty env stored under "".
    #[allow(dead_code)] // .31.6 wires validate_specs into the drivers.
    pub module_type_envs: std::collections::HashMap<String, crate::type_expr::ModuleTypeEnv>,
    /// fz-swt.8 — Inner-type map for `opaque` aliases across every
    /// module in the program. Keyed by the qualified opaque tag (as
    /// stored on the qualified opaque type name); value is the parsed body
    /// `T` following the `opaque` keyword. Used by the typer to type
    /// `handle.value` accesses (a `Prim::MapGet` with key `:value` on
    /// a singleton-opaque subject) as `T` rather than the generic
    /// map-lookup fallback.
    pub opaque_inners: std::collections::HashMap<String, crate::types::Ty>,
    /// fz-axu.2 (K1) — Inner-type map for `refines` brand declarations,
    /// parallel to `opaque_inners`. Keyed by the qualified brand tag (as
    /// stored on the qualified brand type name); value is the parsed body `T`
    /// following the `refines` keyword. K2 populates this during type-env
    /// construction; K4's is_subtype rule consults it to recognise that
    /// `brand("B") ⊆ T` when the declaration is in scope.
    pub brand_inners: std::collections::HashMap<String, crate::types::Ty>,
}
