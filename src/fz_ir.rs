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
use crate::diag::Span;
use fz_runtime::heap::Schema;
use std::collections::{HashMap, HashSet};
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FnId(pub u32);

/// Per-callsite specialization identifier. fz-ul4.29.2.
///
/// One `SpecId` corresponds to one compiled body — a specific `(FnId,
/// input-Descr-tuple)` pairing. Today each fn has exactly one SpecId
/// (its any-key spec); fz-ul4.29.2.1 enables multiple SpecIds per FnId
/// when call sites request narrow specializations.
///
/// SpecId.0 doubles as the runtime's `schema_id` (frame header field),
/// so the runtime contract — schema_ids are dense u32 from 0..count —
/// is preserved as the codegen layer grows multiple specs per FnIr.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SpecId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BlockId(pub u32);

/// fz-9pr.1 — disambiguates *which kind of emit* a given block produces.
///
/// A single block can be the source of multiple callsite emits (e.g., a
/// `Term::Call` block produces both a `Direct` callee target and a
/// `Cont` target). The slot value names which one. Mirrors the
/// `EmitSlot` used by ir_typer's discovery walker — by hosting it in
/// fz_ir we make `CallsiteId` independent of typer internals.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum EmitSlot {
    /// `Term::Call` / `Term::TailCall` callee.
    Direct,
    /// The continuation of `Term::Call` / `Term::CallClosure` /
    /// `Term::Receive` — i.e., (cont.fn_id, [slot0, captures...]).
    Cont,
    /// `Term::CallClosure` / `Term::TailCallClosure` target resolved
    /// via `fn_constants`. Distinct from `Direct` because the same
    /// block can also produce a `Cont` (separate slot, same block).
    CallClosureKnown,
    /// `(clause_idx, sig_idx)` of a `closure_lit`-resolved CallClosure
    /// target. Multiple lit clauses ⇒ multiple emits per block.
    ClosureLit(usize, usize),
    /// `Prim::MakeClosure` at this `stmt_idx` in the block.
    MakeClosure(usize),
}

/// fz-9pr.1 — the address of one callsite in the module.
///
/// `(caller, block, slot)` uniquely names a place that can produce a
/// callee target. Identical in shape to the (caller, block, slot)
/// triple of `EmitterSite`, minus the spec-key — phases that don't
/// distinguish between caller specs (the reducer, ir_inline) use
/// `CallsiteId`; the typer's spec-aware discovery walk uses
/// `EmitterSite` and round-trips through `with_spec_key` / `callsite_id`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CallsiteId {
    pub caller: FnId,
    pub block: BlockId,
    pub slot: EmitSlot,
}

/// fz-9pr.1 — what happened at a callsite, as recorded on the Module.
///
/// Four outcomes, three writers (reducer, ir_inline, typer), one
/// table. See the fz-9pr epic for the unified model. `Consumed`'s
/// `Descr` is boxed and `Emitted`'s tuple is heap-tailed already, so
/// the enum stays compact (one word + tag).
#[derive(Clone, Debug, PartialEq)]
pub enum CallsiteOutcome {
    /// Reducer folded the call away. Result Descr is what the
    /// continuation will see in slot 0.
    Consumed { result: Box<crate::types::Descr> },
    /// Callee body was spliced into the caller (ir_inline today,
    /// reducer once fz-9pr.E lands).
    Inlined,
    /// Typer minted a spec for this callsite's target.
    Emitted {
        target: (FnId, Vec<crate::types::Descr>),
    },
    /// Provisional — nobody has decided yet. Debug invariant
    /// (fz-9pr.5): no `Stalled` may survive end of pipeline.
    Stalled,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Var(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExternId(pub u32);

/// C ABI wire type for `extern "C" fn` declarations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExternTy {
    I64,
    F64,
    Any,   // opaque u64 fz value
    Unit,  // maps to 0 on return
    Never, // diverges
}

/// One resolved `extern "C" fn` declaration stored in `Module.externs`.
#[derive(Debug, Clone)]
pub struct ExternDecl {
    pub id: ExternId,
    pub fz_name: String,
    /// C symbol name (same as fz_name for v1; override possible later).
    pub symbol: String,
    pub params: Vec<ExternTy>,
    pub ret: ExternTy,
    /// Semantic return type for the type system. Used by ir_typer to give
    /// `Prim::Extern` calls their declared return type instead of `any`.
    /// Defaults to `Descr::any()` when no return type is declared.
    pub ret_descr: crate::types::Descr,
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
    Extern(ExternId, Vec<Var>),
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
    /// fz-cty.8 — constant-folded byte-payload bitstring. Carries the
    /// materialised bytes and bit length; codegen interns the payload as a
    /// module-private data symbol and emits a single allocation call. Produced
    /// only by `ir_const_bs::fold_module`; lowered identically to a
    /// `MakeBitstring` of byte fields at runtime.
    ConstBitstring(Vec<u8>, u64),
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
    /// Runtime type test: returns `true` if the value held in `Var` belongs
    /// to the described type, `false` otherwise.
    ///
    /// For structural types (BasicBits, ints, etc.) this is a real runtime
    /// tag check. For opaque types, the check is resolved to a constant by
    /// the typer (opaque types have no runtime tag) — the branch is then
    /// eliminated by DCE.
    TypeTest(Var, Box<crate::types::Descr>),
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
        /// True when the callee is in the same SCC as the caller — i.e., this
        /// call is on a loop back-edge. Set by ir_lower via the SCC map from
        /// ir_typer. Self-recursion is the degenerate SCC-of-one case; mutual
        /// recursion (f→g→f) is covered automatically. Back-edge sites get
        /// the yield-check inline check in JIT/AOT codegen and in the interp.
        is_back_edge: bool,
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
    /// fz-ul4.19.3: receive next mailbox message; fire continuation with it
    /// when one is available. If the mailbox is empty at the point of
    /// Receive, the running task suspends (state = Blocked); the scheduler
    /// resumes the task when a `send` delivers a message. On resume the
    /// trampoline re-enters this same Term — fz_receive_attempt re-checks
    /// the mailbox, now finds the message, and fires the continuation.
    ///
    /// The continuation receives one argument (the message) followed by
    /// the captured Vars — exactly like Term::Call's continuation. No
    /// `callee` field because receive has no source-language callee; it's
    /// a scheduler-mediated rendezvous point.
    Receive {
        continuation: Cont,
    },
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
        self.blocks
            .iter()
            .find(|b| b.id == id)
            .expect("unknown block")
    }
}

/// Side-tables that map IR positions back to source spans. Populated by
/// `ir_lower` as it goes; consumed by `ir_typer` / diagnostics renderers
/// to point at the right source byte range for a given Var or Stmt.
///
/// The IR types themselves stay narrow (`Prim`, `Stmt`, `Term` carry no
/// span fields). Spans live here so codegen-internal IR transformations
/// don't have to thread spans through every constructor.
#[derive(Debug, Default, Clone)]
pub struct SourceInfo {
    /// Indexed by `Var.0`: span of the source expression / pattern that
    /// introduced this Var. `Span::DUMMY` for compiler-introduced temps
    /// or any Var introduced before .20.4 hooks (e.g. ir_typer's
    /// rewrite_vec_kinds may mint Vars during a pass).
    pub var_span: Vec<Span>,
    /// Indexed by `Var.0`: the source name that produced this Var, or
    /// "" for compiler-introduced temps. Used by .20.8 to render
    /// "`x` has type `int | atom`" instead of "v3 has type …".
    pub var_name: Vec<String>,
    /// Span per `(FnId, BlockId, stmt_idx)` for `Stmt::Let`. Sparse —
    /// absent entries mean DUMMY. Populated by `ir_lower` per emitted
    /// stmt; codegen-internal transformations may leave their stmts
    /// unspanned, which is fine.
    pub stmt_spans: HashMap<(FnId, BlockId), Vec<Span>>,
    /// Span per `(FnId, BlockId)` for the block's terminator. Same
    /// sparsity contract as `stmt_spans`.
    pub term_span: HashMap<(FnId, BlockId), Span>,
    /// Span of the source fn declaration. Indexed by `FnId.0`. Synthetic
    /// continuations created by CPS-splitting an expression use the
    /// originating Call's span (the user-visible position of the work
    /// the continuation is doing).
    pub fn_span: Vec<Span>,
}

impl SourceInfo {
    pub fn var_name_of(&self, v: Var) -> Option<&str> {
        self.var_name
            .get(v.0 as usize)
            .map(|s| s.as_str())
            .filter(|s| !s.is_empty())
    }

    pub fn var_span_of(&self, v: Var) -> Span {
        self.var_span
            .get(v.0 as usize)
            .copied()
            .unwrap_or(Span::DUMMY)
    }

    pub fn fn_span_of(&self, f: FnId) -> Span {
        self.fn_span
            .get(f.0 as usize)
            .copied()
            .unwrap_or(Span::DUMMY)
    }
}

#[derive(Debug, Default, Clone)]
pub struct Module {
    pub fns: Vec<FnIr>,
    pub schemas: Vec<Schema>,
    pub source: SourceInfo,
    /// Atom names indexed by id. `atom_names[id]` is the source spelling of
    /// the atom interned at `Const::Atom(id)`. Populated by ir_lower from
    /// its per-module AtomTable. Every runtime path (JIT, interp, AOT)
    /// hands this to its Process so `fz_value::debug::render` can print
    /// `:ok` instead of `:atom_1`. Closed by fz-ul4.25.
    pub atom_names: Vec<String>,
    /// O(1) index from FnId to position in `fns`. Kept in sync by
    /// `ModuleBuilder::add_fn`; never mutated after `build()`.
    pub fn_idx: HashMap<FnId, usize>,
    /// All `extern "C" fn` declarations. Stable: ExternId is a counter, not a vec index.
    pub externs: Vec<ExternDecl>,
    /// O(1) index from ExternId to position in `externs`. Mirrors fn_idx.
    pub extern_idx: HashMap<ExternId, usize>,
    /// fz-jg5.12 (RED.9) — Fns marked as reduction boundaries. Populated
    /// by ir_lower from `@spec` declarations. The reducer treats these as
    /// firewalls: a declared spec is the user's signed contract that the
    /// body is a stable unit, so reduction does not cross into it (except
    /// for trivially-inlinable single-stmt bodies, which carry no risk).
    pub boundary_fns: HashSet<FnId>,
    /// fz-9pr.2 — unified callsite outcome table. Three writers
    /// (reducer, ir_inline, typer) and several readers all share this
    /// one map. Empty on a freshly-built module; populated as phases
    /// decide each callsite's fate. See `CallsiteOutcome` for the
    /// shape of each entry and the fz-9pr epic for the design.
    pub callsite_outcomes: HashMap<CallsiteId, CallsiteOutcome>,
}

impl Module {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn extern_by_id(&self, eid: ExternId) -> &ExternDecl {
        &self.externs[*self.extern_idx.get(&eid).expect("unknown extern id")]
    }

    pub fn fn_by_id(&self, id: FnId) -> &FnIr {
        &self.fns[*self.fn_idx.get(&id).expect("unknown fn id")]
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
    fn_idx: HashMap<FnId, usize>,
    schemas: Vec<Schema>,
}

impl ModuleBuilder {
    pub fn new() -> Self {
        Self {
            next_fn: 0,
            fns: Vec::new(),
            fn_idx: HashMap::new(),
            schemas: Vec::new(),
        }
    }

    pub fn fresh_fn_id(&mut self) -> FnId {
        let id = FnId(self.next_fn);
        self.next_fn += 1;
        id
    }

    /// The FnId value that would be assigned by the next `fresh_fn_id` call.
    /// Used to snapshot the prelude/user boundary in `lower_program_full`.
    pub fn next_fn_id(&self) -> u32 {
        self.next_fn
    }

    pub fn add_fn(&mut self, fn_ir: FnIr) {
        self.fn_idx.insert(fn_ir.id, self.fns.len());
        self.fns.push(fn_ir);
    }

    pub fn add_schema(&mut self, schema: Schema) -> u32 {
        let id = self.schemas.len() as u32;
        self.schemas.push(schema);
        id
    }

    pub fn build(self) -> Module {
        Module {
            fns: self.fns,
            fn_idx: self.fn_idx,
            schemas: self.schemas,
            source: SourceInfo::default(),
            atom_names: Vec::new(),
            externs: Vec::new(),
            extern_idx: HashMap::new(),
            boundary_fns: HashSet::new(),
            callsite_outcomes: HashMap::new(),
        }
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
    vars.iter()
        .map(|v| v.to_string())
        .collect::<Vec<_>>()
        .join(", ")
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
            Prim::Extern(e, args) => {
                write!(f, "extern#{}([{}])", e.0, fmt_var_list(args))
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
            Prim::ConstBitstring(bytes, bit_len) => {
                write!(
                    f,
                    "const_bitstring(byte_len={}, bit_len={})",
                    bytes.len(),
                    bit_len
                )
            }
            Prim::BitReaderInit(v) => write!(f, "bit_reader_init({})", v),
            Prim::BitReadField { reader, .. } => write!(f, "bit_read_field({})", reader),
            Prim::BitReaderDone(v) => write!(f, "bit_reader_done({})", v),
            Prim::TypeTest(v, d) => write!(f, "type_test({}, {})", v, d),
        }
    }
}

impl fmt::Display for Cont {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "cont({}, captured=[{}])",
            self.fn_id,
            fmt_var_list(&self.captured)
        )
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Goto(b, args) => write!(f, "goto {}({})", b, fmt_var_list(args)),
            Term::If(c, t, e) => write!(f, "if {} then {} else {}", c, t, e),
            Term::Call {
                callee,
                args,
                continuation,
            } => write!(
                f,
                "call {}([{}]) -> {}",
                callee,
                fmt_var_list(args),
                continuation
            ),
            Term::TailCall { callee, args, .. } => {
                write!(f, "tail_call {}([{}])", callee, fmt_var_list(args))
            }
            Term::CallClosure {
                closure,
                args,
                continuation,
            } => write!(
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
            Term::Receive { continuation } => write!(f, "receive -> {}", continuation),
        }
    }
}

impl fmt::Display for Block {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "  {}({}):", self.id, fmt_var_list(&self.params))?;
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
        use fz_runtime::heap::{FieldDescriptor, FieldKind};
        let mut mb = ModuleBuilder::new();
        let id = mb.add_schema(Schema {
            name: "Frame_identity".into(),
            size: 16,
            fields: vec![FieldDescriptor {
                offset: 0,
                kind: FieldKind::FzValue,
            }],
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
                continuation: Cont {
                    fn_id: FnId(7),
                    captured: vec![x],
                },
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
        b.set_terminator(
            entry,
            Term::TailCall {
                callee: FnId(0),
                args: vec![x],
                is_back_edge: false,
            },
        );
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
    fn fresh_module_has_empty_callsite_outcomes() {
        let m = ModuleBuilder::new().build();
        assert!(m.callsite_outcomes.is_empty());
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
