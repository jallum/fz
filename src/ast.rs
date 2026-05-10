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
    Map(Vec<(Expr, Expr)>),

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
    With(Vec<WithBinding>, Box<Expr>),

    // bindings
    // pattern = expr (rebinds names; immutable, just shadows)
    Match(Pattern, Box<Expr>),

    // sequence of expressions; result is the last
    Block(Vec<Expr>),

    // anonymous fn: fn (p1, p2) -> body  /  multi-clause via Case under the hood later
    Lambda(Vec<Pattern>, Box<Expr>),
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
}

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
}

#[derive(Debug, Clone)]
pub struct Program {
    pub items: Vec<Rc<Item>>,
}
