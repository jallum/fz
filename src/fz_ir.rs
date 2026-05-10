//! fz-IR: canonical CPS form for fz programs.
//!
//! Pure data + builder + pretty-printer. No translation, no execution here
//! (those are .11.4 and .11.5). Codegen consumes this in .11.7+.
//!
//! Shape:
//!   Module { fns, schemas } — holds all fns and the schema table referenced
//!     by their frame_schema_id (populated by liveness in .11.6).
//!   FnIr { blocks } — basic-block CFG. Each block has a list of let-bindings
//!     plus a terminator. Terminators are the CPS-shaped control: Goto, If,
//!     Call (with explicit continuation), TailCall (forwards our continuation),
//!     Return (invoke our frame's continuation), Halt (process result).
//!   Cont { fn_id, captured } — first-class continuation: an IR fn id plus a
//!     list of locals to splice in when invoked. Frames materialize these as
//!     special-purpose structs at codegen time.
//!
//! Multi-clause dispatch is NOT a runtime table — it lowers to a chain of
//! If-else continuations in this IR.

#![allow(dead_code)]

use crate::ast::{BitType, Endian, Pattern};
use crate::heap::Schema;
use std::fmt;

/// Element-kind for a heap-allocated vector. The AST-level `VecKind` (Numeric
/// / Bytes / Bits) is a sigil-shape; lowering bifurcates `Numeric` into I64
/// or F64 by inspecting the element exprs, so by IR time the element type
/// is concrete. Mirrors `HeapKind::VecI64 / VecF64 / VecU8 / VecBit`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VecKindIr {
    I64,
    F64,
    U8,
    Bit,
}

#[derive(Debug, Clone)]
pub enum BitSizeIr {
    Literal(u32),
    Var(Var),
}

#[derive(Debug, Clone)]
pub struct BitFieldIr {
    pub value: Var,
    pub ty: BitType,
    pub size: Option<BitSizeIr>,
    pub endian: Endian,
    pub signed: bool,
    pub unit: Option<u32>,
}

#[derive(Debug, Clone)]
pub struct BitFieldPatIr {
    /// Per-field AST pattern (binding/literal-check) — applied to the extracted
    /// IR value via standard pattern lowering after BitstringMatch returns.
    pub pattern: Pattern,
    pub ty: BitType,
    pub size: Option<BitSizeIr>,
    pub endian: Endian,
    pub signed: bool,
    pub unit: Option<u32>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FnId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BlockId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Var(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BuiltinId(pub u32);

/// Typed view of a `BuiltinId`. The discriminants match the registration
/// order in `BuiltinTable::new` (single source of truth for that mapping
/// is `BuiltinKind::name`). Codegen dispatches on this enum so the wire
/// between ir_lower's name-based BuiltinTable and ir_codegen's per-builtin
/// runtime fns stays type-checked.
#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinKind {
    Print = 0,
    Assert = 1,
    AssertEq = 2,
    AssertNeq = 3,
    VecGet = 4,
}

impl BuiltinKind {
    pub const ALL: [BuiltinKind; 5] = [
        Self::Print,
        Self::Assert,
        Self::AssertEq,
        Self::AssertNeq,
        Self::VecGet,
    ];

    pub fn name(self) -> &'static str {
        match self {
            Self::Print => "print",
            Self::Assert => "assert",
            Self::AssertEq => "assert_eq",
            Self::AssertNeq => "assert_neq",
            Self::VecGet => "vec_get",
        }
    }

    pub fn from_id(id: BuiltinId) -> Option<Self> {
        Self::ALL.iter().copied().find(|k| *k as u32 == id.0)
    }

    pub fn id(self) -> BuiltinId {
        BuiltinId(self as u32)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Const {
    Int(i64),
    Float(f64),
    Str(String),
    Atom(u32),
    Nil,
    True,
    False,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Not,
}

#[derive(Debug, Clone)]
pub enum Prim {
    Const(Const),
    BinOp(BinOp, Var, Var),
    UnOp(UnOp, Var),
    AllocStruct(u32, Vec<Var>),
    Builtin(BuiltinId, Vec<Var>),
    ListCons(Var, Var),
    ListHead(Var),
    ListTail(Var),
    ListIsNil(Var),
    /// Build a tuple (struct with the canonical tuple-of-arity-N schema).
    MakeTuple(Vec<Var>),
    /// Project the i-th element of a tuple.
    TupleField(Var, u32),
    /// Build a list [v1, v2, ... | optional_tail]; tail defaults to Nil.
    MakeList(Vec<Var>, Option<Var>),
    /// Allocate a closure: a struct holding the IR fn id of the lambda body
    /// plus the captured environment locals.
    MakeClosure(FnId, Vec<Var>),
    /// Build a map from (key, value) pairs in insertion order.
    MakeMap(Vec<(Var, Var)>),
    /// Functional update of `base` map: every key in entries must exist.
    MapUpdate(Var, Vec<(Var, Var)>),
    /// `m[k]` — bracket access. Returns nil if key absent.
    MapGet(Var, Var),
    /// Monotyped vector literal.
    MakeVec(VecKindIr, Vec<Var>),
    /// Build a bitstring from a sequence of fields.
    MakeBitstring(Vec<BitFieldIr>),
    /// Initialize a bit-reader from a binary/bitstring value. Returns an
    /// opaque reader value. Pattern-matching of bitstrings uses this plus
    /// `BitReadField` per field, so size-vars in later fields can refer to
    /// IR vars bound from earlier fields' patterns.
    BitReaderInit(Var),
    /// Read one field from a reader. Returns
    /// `Tuple([ok_bool, extracted_value, new_reader])` on success and
    /// `Tuple([false])` on failure (in which case extracted/new_reader are
    /// absent). `is_last` matters for None-sized binary/bits ("rest").
    BitReadField {
        reader: Var,
        ty: BitType,
        size: Option<BitSizeIr>,
        endian: Endian,
        signed: bool,
        unit: Option<u32>,
        is_last: bool,
    },
    /// True if the reader has consumed all bits.
    BitReaderDone(Var),
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Let(Var, Prim),
}

/// First-class continuation: an IR fn to invoke with the given captured vars
/// (plus the value(s) being returned to it, supplied by the caller at runtime).
#[derive(Debug, Clone)]
pub struct Cont {
    pub fn_id: FnId,
    pub captured: Vec<Var>,
}

#[derive(Debug, Clone)]
pub enum Term {
    Goto(BlockId, Vec<Var>),
    If(Var, BlockId, BlockId),
    Call {
        callee: FnId,
        args: Vec<Var>,
        continuation: Cont,
    },
    TailCall {
        callee: FnId,
        args: Vec<Var>,
    },
    /// Invoke a closure value (Var holding a Value::IrClosure). The closure's
    /// captured slots are spliced ahead of `args` when entering the lambda's fn.
    CallClosure {
        closure: Var,
        args: Vec<Var>,
        continuation: Cont,
    },
    TailCallClosure {
        closure: Var,
        args: Vec<Var>,
    },
    Return(Var),
    Halt(Var),
}

#[derive(Debug, Clone)]
pub struct Block {
    pub id: BlockId,
    pub params: Vec<Var>,
    pub stmts: Vec<Stmt>,
    pub terminator: Term,
}

#[derive(Debug, Clone)]
pub struct FnIr {
    pub id: FnId,
    pub name: String,
    /// Populated by liveness analysis in .11.6 (0 means "not yet computed").
    pub frame_schema_id: u32,
    pub blocks: Vec<Block>,
    pub entry: BlockId,
}

impl FnIr {
    pub fn block(&self, id: BlockId) -> &Block {
        self.blocks.iter().find(|b| b.id == id).expect("unknown block")
    }
}

#[derive(Debug, Default)]
pub struct Module {
    pub fns: Vec<FnIr>,
    pub schemas: Vec<Schema>,
}

impl Module {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn fn_by_id(&self, id: FnId) -> &FnIr {
        self.fns.iter().find(|f| f.id == id).expect("unknown fn id")
    }

    pub fn fn_by_name(&self, name: &str) -> Option<&FnIr> {
        self.fns.iter().find(|f| f.name == name)
    }
}

// ---------- builder ----------

/// Builder for one FnIr. `next_var` and `next_block` mint fresh ids; the entry
/// block is the first block created via `block()`. Set the terminator on each
/// block before calling `build()`.
pub struct FnBuilder {
    id: FnId,
    name: String,
    next_var: u32,
    next_block: u32,
    blocks: Vec<Block>,
    entry: Option<BlockId>,
}

impl FnBuilder {
    pub fn new(id: FnId, name: impl Into<String>) -> Self {
        Self {
            id,
            name: name.into(),
            next_var: 0,
            next_block: 0,
            blocks: Vec::new(),
            entry: None,
        }
    }

    pub fn fresh_var(&mut self) -> Var {
        let v = Var(self.next_var);
        self.next_var += 1;
        v
    }

    /// Create a new block with the given parameters; first call's block becomes
    /// the entry block. Returns the new block's id.
    pub fn block(&mut self, params: Vec<Var>) -> BlockId {
        let id = BlockId(self.next_block);
        self.next_block += 1;
        self.blocks.push(Block {
            id,
            params,
            stmts: Vec::new(),
            terminator: Term::Halt(Var(0)),
        });
        if self.entry.is_none() {
            self.entry = Some(id);
        }
        id
    }

    fn block_mut(&mut self, id: BlockId) -> &mut Block {
        self.blocks
            .iter_mut()
            .find(|b| b.id == id)
            .expect("unknown block")
    }

    /// Append `let v = prim` to the given block; returns the bound var.
    pub fn let_(&mut self, block: BlockId, prim: Prim) -> Var {
        let v = self.fresh_var();
        self.block_mut(block).stmts.push(Stmt::Let(v, prim));
        v
    }

    pub fn set_terminator(&mut self, block: BlockId, term: Term) {
        self.block_mut(block).terminator = term;
    }

    pub fn build(self) -> FnIr {
        let entry = self.entry.expect("FnBuilder built with no blocks");
        FnIr {
            id: self.id,
            name: self.name,
            frame_schema_id: 0,
            blocks: self.blocks,
            entry,
        }
    }
}

pub struct ModuleBuilder {
    next_fn: u32,
    fns: Vec<FnIr>,
    schemas: Vec<Schema>,
}

impl ModuleBuilder {
    pub fn new() -> Self {
        Self { next_fn: 0, fns: Vec::new(), schemas: Vec::new() }
    }

    pub fn fresh_fn_id(&mut self) -> FnId {
        let id = FnId(self.next_fn);
        self.next_fn += 1;
        id
    }

    pub fn add_fn(&mut self, fn_ir: FnIr) {
        self.fns.push(fn_ir);
    }

    pub fn add_schema(&mut self, schema: Schema) -> u32 {
        let id = self.schemas.len() as u32;
        self.schemas.push(schema);
        id
    }

    pub fn build(self) -> Module {
        Module { fns: self.fns, schemas: self.schemas }
    }
}

impl Default for ModuleBuilder {
    fn default() -> Self {
        Self::new()
    }
}

// ---------- pretty-printer ----------

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}

impl fmt::Display for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bb{}", self.0)
    }
}

impl fmt::Display for FnId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fn{}", self.0)
    }
}

impl fmt::Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Const::Int(n) => write!(f, "{}", n),
            Const::Float(x) => write!(f, "{}f", x),
            Const::Str(s) => write!(f, "{:?}", s),
            Const::Atom(id) => write!(f, ":atom_{}", id),
            Const::Nil => write!(f, "nil"),
            Const::True => write!(f, "true"),
            Const::False => write!(f, "false"),
        }
    }
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Mod => "%",
            BinOp::Eq => "==",
            BinOp::Neq => "!=",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::And => "and",
            BinOp::Or => "or",
        };
        f.write_str(s)
    }
}

impl fmt::Display for UnOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            UnOp::Neg => "-",
            UnOp::Not => "not",
        };
        f.write_str(s)
    }
}

fn fmt_var_list(vars: &[Var]) -> String {
    vars.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(", ")
}

impl fmt::Display for Prim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Prim::Const(c) => write!(f, "const({})", c),
            Prim::BinOp(op, a, b) => write!(f, "{} {} {}", a, op, b),
            Prim::UnOp(op, a) => write!(f, "{} {}", op, a),
            Prim::AllocStruct(sid, args) => {
                write!(f, "alloc_struct(schema={}, [{}])", sid, fmt_var_list(args))
            }
            Prim::Builtin(b, args) => {
                write!(f, "builtin#{}([{}])", b.0, fmt_var_list(args))
            }
            Prim::ListCons(h, t) => write!(f, "cons({}, {})", h, t),
            Prim::ListHead(l) => write!(f, "head({})", l),
            Prim::ListTail(l) => write!(f, "tail({})", l),
            Prim::ListIsNil(l) => write!(f, "is_nil({})", l),
            Prim::MakeTuple(args) => write!(f, "tuple([{}])", fmt_var_list(args)),
            Prim::TupleField(v, i) => write!(f, "tuple_field({}, {})", v, i),
            Prim::MakeList(els, tail) => match tail {
                Some(t) => write!(f, "list([{}] | {})", fmt_var_list(els), t),
                None => write!(f, "list([{}])", fmt_var_list(els)),
            },
            Prim::MakeClosure(fid, captured) => {
                write!(f, "closure({}, captured=[{}])", fid, fmt_var_list(captured))
            }
            Prim::MakeMap(entries) => {
                let s = entries
                    .iter()
                    .map(|(k, v)| format!("{} => {}", k, v))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "map({{{}}})", s)
            }
            Prim::MapUpdate(base, entries) => {
                let s = entries
                    .iter()
                    .map(|(k, v)| format!("{} => {}", k, v))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "map_update({}, {{{}}})", base, s)
            }
            Prim::MapGet(m, k) => write!(f, "map_get({}, {})", m, k),
            Prim::MakeVec(kind, els) => {
                let kstr = match kind {
                    VecKindIr::I64 => "i64",
                    VecKindIr::F64 => "f64",
                    VecKindIr::U8 => "u8",
                    VecKindIr::Bit => "bit",
                };
                write!(f, "vec({}, [{}])", kstr, fmt_var_list(els))
            }
            Prim::MakeBitstring(fields) => {
                write!(f, "bitstring([{}])", fields.len())
            }
            Prim::BitReaderInit(v) => write!(f, "bit_reader_init({})", v),
            Prim::BitReadField { reader, .. } => write!(f, "bit_read_field({})", reader),
            Prim::BitReaderDone(v) => write!(f, "bit_reader_done({})", v),
        }
    }
}

impl fmt::Display for Cont {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "cont({}, captured=[{}])", self.fn_id, fmt_var_list(&self.captured))
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Goto(b, args) => write!(f, "goto {}({})", b, fmt_var_list(args)),
            Term::If(c, t, e) => write!(f, "if {} then {} else {}", c, t, e),
            Term::Call { callee, args, continuation } => write!(
                f,
                "call {}([{}]) -> {}",
                callee,
                fmt_var_list(args),
                continuation
            ),
            Term::TailCall { callee, args } => {
                write!(f, "tail_call {}([{}])", callee, fmt_var_list(args))
            }
            Term::CallClosure { closure, args, continuation } => write!(
                f,
                "call_closure {}([{}]) -> {}",
                closure,
                fmt_var_list(args),
                continuation
            ),
            Term::TailCallClosure { closure, args } => {
                write!(f, "tail_call_closure {}([{}])", closure, fmt_var_list(args))
            }
            Term::Return(v) => write!(f, "return {}", v),
            Term::Halt(v) => write!(f, "halt {}", v),
        }
    }
}

impl fmt::Display for Block {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "  {}({}):\n", self.id, fmt_var_list(&self.params))?;
        for s in &self.stmts {
            match s {
                Stmt::Let(v, p) => writeln!(f, "    let {} = {}", v, p)?,
            }
        }
        writeln!(f, "    {}", self.terminator)
    }
}

impl fmt::Display for FnIr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "{} {} (entry={}, frame_schema={}) {{",
            self.id, self.name, self.entry, self.frame_schema_id
        )?;
        for b in &self.blocks {
            write!(f, "{}", b)?;
        }
        writeln!(f, "}}")
    }
}

impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "module (schemas={}) {{", self.schemas.len())?;
        for fn_ir in &self.fns {
            write!(f, "{}", fn_ir)?;
        }
        writeln!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// fn identity(x) = x
    fn build_identity() -> FnIr {
        let mut b = FnBuilder::new(FnId(0), "identity");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        b.set_terminator(entry, Term::Return(x));
        b.build()
    }

    /// fn add1(x) = x + 1
    fn build_add1() -> FnIr {
        let mut b = FnBuilder::new(FnId(1), "add1");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let one = b.let_(entry, Prim::Const(Const::Int(1)));
        let sum = b.let_(entry, Prim::BinOp(BinOp::Add, x, one));
        b.set_terminator(entry, Term::Return(sum));
        b.build()
    }

    /// fn iszero(x) = if x == 0 then true else false
    fn build_iszero() -> FnIr {
        let mut b = FnBuilder::new(FnId(2), "iszero");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let zero = b.let_(entry, Prim::Const(Const::Int(0)));
        let cond = b.let_(entry, Prim::BinOp(BinOp::Eq, x, zero));
        let then_b = b.block(vec![]);
        let else_b = b.block(vec![]);
        b.set_terminator(entry, Term::If(cond, then_b, else_b));
        let t = b.let_(then_b, Prim::Const(Const::True));
        b.set_terminator(then_b, Term::Return(t));
        let fl = b.let_(else_b, Prim::Const(Const::False));
        b.set_terminator(else_b, Term::Return(fl));
        b.build()
    }

    #[test]
    fn build_identity_fn_has_one_block_and_returns_param() {
        let fn_ir = build_identity();
        assert_eq!(fn_ir.name, "identity");
        assert_eq!(fn_ir.blocks.len(), 1);
        assert_eq!(fn_ir.entry, BlockId(0));
        let entry = fn_ir.block(BlockId(0));
        assert_eq!(entry.params.len(), 1);
        assert!(entry.stmts.is_empty());
        match entry.terminator {
            Term::Return(v) => assert_eq!(v, Var(0)),
            _ => panic!("expected Return"),
        }
    }

    #[test]
    fn fresh_vars_are_unique() {
        let mut b = FnBuilder::new(FnId(0), "f");
        let a = b.fresh_var();
        let c = b.fresh_var();
        assert_ne!(a, c);
    }

    #[test]
    fn build_add1_has_two_lets_and_returns_sum() {
        let fn_ir = build_add1();
        let entry = fn_ir.block(fn_ir.entry);
        assert_eq!(entry.stmts.len(), 2);
        match &entry.stmts[0] {
            Stmt::Let(_, Prim::Const(Const::Int(1))) => {}
            other => panic!("expected let _ = const(1), got {:?}", other),
        }
        match &entry.stmts[1] {
            Stmt::Let(_, Prim::BinOp(BinOp::Add, _, _)) => {}
            other => panic!("expected let _ = add, got {:?}", other),
        }
    }

    #[test]
    fn build_iszero_has_three_blocks_with_if_then_else() {
        let fn_ir = build_iszero();
        assert_eq!(fn_ir.blocks.len(), 3);
        let entry = fn_ir.block(fn_ir.entry);
        match entry.terminator {
            Term::If(_, t, e) => {
                assert_ne!(t, e);
                assert_eq!(t, BlockId(1));
                assert_eq!(e, BlockId(2));
            }
            _ => panic!("expected If terminator"),
        }
    }

    #[test]
    fn module_holds_multiple_fns_and_lookup_by_name() {
        let mut mb = ModuleBuilder::new();
        mb.add_fn(build_identity());
        mb.add_fn(build_add1());
        let m = mb.build();
        assert_eq!(m.fns.len(), 2);
        assert!(m.fn_by_name("identity").is_some());
        assert!(m.fn_by_name("add1").is_some());
        assert!(m.fn_by_name("missing").is_none());
        assert_eq!(m.fn_by_id(FnId(0)).name, "identity");
        assert_eq!(m.fn_by_id(FnId(1)).name, "add1");
    }

    #[test]
    fn module_holds_schemas() {
        use crate::heap::{FieldDescriptor, FieldKind};
        let mut mb = ModuleBuilder::new();
        let id = mb.add_schema(Schema {
            name: "Frame_identity".into(),
            size: 16,
            fields: vec![FieldDescriptor { offset: 0, kind: FieldKind::FzValue }],
        });
        assert_eq!(id, 0);
        let m = mb.build();
        assert_eq!(m.schemas.len(), 1);
        assert_eq!(m.schemas[0].name, "Frame_identity");
    }

    #[test]
    fn pretty_print_identity() {
        let fn_ir = build_identity();
        let s = format!("{}", fn_ir);
        assert!(s.contains("fn0 identity"));
        assert!(s.contains("entry=bb0"));
        assert!(s.contains("bb0(v0):"));
        assert!(s.contains("return v0"));
    }

    #[test]
    fn pretty_print_add1() {
        let fn_ir = build_add1();
        let s = format!("{}", fn_ir);
        assert!(s.contains("let v1 = const(1)"));
        assert!(s.contains("let v2 = v0 + v1"));
        assert!(s.contains("return v2"));
    }

    #[test]
    fn pretty_print_iszero_branches() {
        let fn_ir = build_iszero();
        let s = format!("{}", fn_ir);
        assert!(s.contains("if v2 then bb1 else bb2"));
        assert!(s.contains("return"));
    }

    #[test]
    fn pretty_print_module() {
        let mut mb = ModuleBuilder::new();
        mb.add_fn(build_identity());
        mb.add_fn(build_add1());
        let m = mb.build();
        let s = format!("{}", m);
        assert!(s.starts_with("module"));
        assert!(s.contains("identity"));
        assert!(s.contains("add1"));
    }

    #[test]
    fn term_call_with_continuation_round_trips() {
        let mut b = FnBuilder::new(FnId(3), "caller");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        b.set_terminator(
            entry,
            Term::Call {
                callee: FnId(0),
                args: vec![x],
                continuation: Cont { fn_id: FnId(7), captured: vec![x] },
            },
        );
        let fn_ir = b.build();
        let s = format!("{}", fn_ir);
        assert!(s.contains("call fn0([v0]) -> cont(fn7, captured=[v0])"));
    }

    #[test]
    fn term_tail_call() {
        let mut b = FnBuilder::new(FnId(4), "tc");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        b.set_terminator(entry, Term::TailCall { callee: FnId(0), args: vec![x] });
        let fn_ir = b.build();
        let s = format!("{}", fn_ir);
        assert!(s.contains("tail_call fn0([v0])"));
    }

    #[test]
    fn term_halt_pretty_prints() {
        let mut b = FnBuilder::new(FnId(5), "top");
        let entry = b.block(vec![]);
        let v = b.let_(entry, Prim::Const(Const::Int(42)));
        b.set_terminator(entry, Term::Halt(v));
        let s = format!("{}", b.build());
        assert!(s.contains("halt v0"));
    }

    #[test]
    fn list_prims_pretty_print() {
        let mut b = FnBuilder::new(FnId(6), "lst");
        let entry = b.block(vec![]);
        let nil = b.let_(entry, Prim::Const(Const::Nil));
        let one = b.let_(entry, Prim::Const(Const::Int(1)));
        let l = b.let_(entry, Prim::ListCons(one, nil));
        let h = b.let_(entry, Prim::ListHead(l));
        let _t = b.let_(entry, Prim::ListTail(l));
        let _z = b.let_(entry, Prim::ListIsNil(l));
        b.set_terminator(entry, Term::Return(h));
        let s = format!("{}", b.build());
        assert!(s.contains("cons(v1, v0)"));
        assert!(s.contains("head(v2)"));
        assert!(s.contains("tail(v2)"));
        assert!(s.contains("is_nil(v2)"));
    }

    #[test]
    fn alloc_struct_prim_pretty_prints() {
        let mut b = FnBuilder::new(FnId(7), "mk");
        let entry = b.block(vec![]);
        let a = b.let_(entry, Prim::Const(Const::Int(1)));
        let bb = b.let_(entry, Prim::Const(Const::Int(2)));
        let s_ = b.let_(entry, Prim::AllocStruct(3, vec![a, bb]));
        b.set_terminator(entry, Term::Return(s_));
        let s = format!("{}", b.build());
        assert!(s.contains("alloc_struct(schema=3, [v0, v1])"));
    }

    #[test]
    fn goto_with_args_pretty_prints() {
        let mut b = FnBuilder::new(FnId(8), "g");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let next = b.block(vec![Var(99)]);
        b.set_terminator(entry, Term::Goto(next, vec![x]));
        b.set_terminator(next, Term::Return(Var(99)));
        let s = format!("{}", b.build());
        assert!(s.contains("goto bb1(v0)"));
    }
}
