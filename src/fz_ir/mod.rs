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

use crate::ast::{BitType, Endian};
use crate::diag::Span;
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternSubjectRef};
use crate::frontend::protocols::ProtocolRegistry;
use crate::modules::identity::{ExportKey, ModuleName};
use crate::modules::interface::ModuleInterface;
use crate::specs::{ResolvedSpecSet, StructuralCorrespondenceGroup};
use crate::types::{KeySlot, Nominals, Ty, ty_display};
use fz_runtime::heap::Schema;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::error::Error;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem::take;
use std::rc::Rc;
use std::sync::Arc;

/// fz-kgk — intrinsic identity for a callsite (call-shape terminator,
/// `Prim::MakeClosure`, or `Prim::Extern` stmt).
///
/// Carries the source `Span` for diagnostics. Identity is **pointer
/// equality on the inner `Rc`**: two `CallsiteIdent` values are equal iff
/// their `Rc`s alias the same allocation.
///
/// ## Identity discipline
///
/// - `from_source(span)` — lower-time construction. One per source
///   call expression.
/// - `clone()` — preserves identity. Cloning a `Term` shares the
///   ident; "same callsite, different position." Used by fuse / dce
///   / fold / per-spec body cloning.
/// - `synthetic()` — test-only. `FnBuilder` mints these so tests don't
///   thread spans manually.
///
/// ## Hashing
///
/// Hash uses the `Rc`'s pointer address. Stable within a single
/// process; not reproducible across runs. Golden dumps must render
/// by span and context, not by raw pointer.
#[derive(Clone, Debug)]
pub struct CallsiteIdent(Rc<CallsiteIdentInner>);

#[derive(Debug)]
pub struct CallsiteIdentInner {
    pub span: Span,
}

impl PartialEq for CallsiteIdent {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for CallsiteIdent {}
impl Hash for CallsiteIdent {
    fn hash<H: Hasher>(&self, h: &mut H) {
        (Rc::as_ptr(&self.0) as usize).hash(h);
    }
}

impl CallsiteIdent {
    pub fn from_source(span: Span) -> Self {
        Self(Rc::new(CallsiteIdentInner { span }))
    }

    #[cfg(test)]
    pub fn synthetic() -> Self {
        Self(Rc::new(CallsiteIdentInner { span: Span::DUMMY }))
    }

    pub fn span(&self) -> Span {
        self.0.span
    }
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FnId(pub u32);

/// Per-callsite specialization identifier. fz-ul4.29.2.
///
/// One `SpecId` corresponds to one compiled body — a specific `(FnId,
/// input-type-tuple)` pairing. Today each fn has exactly one SpecId
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
/// `EmitSlot` used by ir_planner's discovery walker — by hosting it in
/// fz_ir we make `CallsiteId` independent of planner internals.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum EmitSlot {
    /// `Term::Call` / `Term::TailCall` callee.
    Direct,
    /// The continuation of `Term::Call` / `Term::CallClosure` — i.e.,
    /// (cont.fn_id, [slot0, captures...]).
    Cont,
    /// fz-try.11: `Term::CallClosure` / `Term::TailCallClosure` callsite.
    /// Purely structural — identifies *where* in the IR the closure
    /// dispatch happens, not which clause of the closure's arrow DNF
    /// resolves. Pre-fz-try.11 this was split into `CallClosureKnown`
    /// and `ClosureLit(c, s)`; the design wanted slots to be structural
    /// ("where") while the planner's dispatch target shapes the variation
    /// ("what").
    ClosureCall,
    /// A known local closure value crosses an external/provider boundary that
    /// may call it later. This is not an in-IR dispatch site, but it is a
    /// real reachability obligation for the closure target body.
    CallableBoundary,
}

/// fz-kgk — the identity of one callsite in the module.
///
/// `(caller, ident, slot)` uniquely names a place that can produce a
/// callee target. `ident` is the intrinsic identity carried on the
/// `Term` (or callsite-bearing `Prim`); see [`CallsiteIdent`] for the
/// fork-vs-inherit rules.
///
/// Previously keyed by `(caller, block, slot)` where slot's MakeClosure
/// variant carried a `stmt_idx`. The positional keys broke under
/// post-planner passes that renumber blocks (per-spec fuse, dce_module's
/// internal fuse). The ident is intrinsic to the IR object and
/// survives all positional moves.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CallsiteId {
    pub caller: FnId,
    pub ident: CallsiteIdent,
    pub slot: EmitSlot,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExternalCallEdge {
    pub callsite: CallsiteId,
    pub target: ExportKey,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProtocolCallTarget {
    pub protocol: ModuleName,
    pub callback: String,
    pub arity: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExternalLinkError {
    MissingTarget(ExportKey),
    MissingCallsite(CallsiteId),
}

impl fmt::Display for ExternalLinkError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingTarget(target) => {
                write!(f, "missing external call target `{}`", target)
            }
            Self::MissingCallsite(callsite) => {
                write!(f, "missing external callsite for caller {}", callsite.caller)
            }
        }
    }
}

impl Error for ExternalLinkError {}

impl CallsiteId {
    pub fn new(caller: FnId, ident: &CallsiteIdent, slot: EmitSlot) -> Self {
        Self {
            caller,
            ident: ident.clone(),
            slot,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Var(pub u32);

/// Linear construction token for destination-passing IR.
///
/// A token names permission to initialize one unpublished destination state.
/// Destination primitives consume one token and either produce the next token
/// or freeze the value. Tokens are not source values and must never become
/// observable runtime data.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct InitTokenId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExternId(pub u32);

/// Per-call-site key for concrete extern argument marshal decisions.
/// `stmt_idx` indexes the `Stmt::Let` in `(fn_id, block_id)`;
/// `arg_idx` indexes the `Prim::Extern` argument list.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExternMarshalSite {
    pub block: BlockId,
    pub stmt_idx: usize,
    pub arg_idx: usize,
}

/// C ABI wire type for `extern "C" fn` declarations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExternTy {
    I64,
    F64,
    Any,   // opaque u64 fz value
    Unit,  // maps to 0 on return
    Never, // diverges
    /// fz-0cv — pass `*const u8` to the bytes of a binary; length is the
    /// caller's responsibility (typically a separate `integer` arg, libc
    /// `write(fd, buf, len)` style). No NUL guarantee.
    Binary,
    /// fz-0cv — pass `*const u8` to the bytes of a binary with a
    /// guaranteed trailing NUL (libc `open(path, flags)` style). Relies
    /// on the +1-NUL invariant from [[fz-wu9]].
    CString,
}

/// Per-call-site marshal decision for an extern argument.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExternMarshal {
    /// Fixed argument governed by `ExternDecl.params`.
    Fixed(ExternTy),
    /// Explicit call-site ascription, e.g. `arg :: cstring`.
    Ascribed(ExternTy),
    /// Variadic argument whose concrete class needs post-typer resolution.
    Auto,
}

/// One argument to `Prim::Extern`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExternArg {
    pub var: Var,
    pub marshal: ExternMarshal,
}

impl ExternArg {
    pub fn fixed(var: Var, ty: ExternTy) -> Self {
        Self {
            var,
            marshal: ExternMarshal::Fixed(ty),
        }
    }

    pub fn ascribed(var: Var, ty: ExternTy) -> Self {
        Self {
            var,
            marshal: ExternMarshal::Ascribed(ty),
        }
    }

    pub fn auto(var: Var) -> Self {
        Self {
            var,
            marshal: ExternMarshal::Auto,
        }
    }
}

/// One resolved `extern "C" fn` declaration stored in `Module.externs`.
#[derive(Debug, Clone)]
pub struct ExternDecl {
    pub id: ExternId,
    pub fz_name: String,
    /// C symbol name (same as fz_name for v1; override possible later).
    pub symbol: String,
    pub params: Vec<ExternTy>,
    pub variadic: bool,
    pub ret: ExternTy,
    /// Semantic return type for the type system. Used by ir_planner to give
    /// `Prim::Extern` calls their declared return type instead of `any`.
    /// Defaults to the `any` Ty when no return type is declared.
    pub ret_descr: Ty,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Const {
    Int(i64),
    Float(f64),
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
    Extern(CallsiteIdent, ExternId, Vec<ExternArg>),
    ListHead(Var),
    ListTail(Var),
    IsEmptyList(Var),
    IsListCons(Var),
    /// Build a tuple (struct with the canonical tuple-of-arity-N schema).
    MakeTuple(Vec<Var>),
    /// Build a named struct using a source `defstruct` schema.
    MakeStruct {
        module: String,
        fields: Vec<(String, Var)>,
    },
    /// Allocate an unpublished tuple destination and mint its first linear
    /// init token. The enclosing `Stmt::Let` binds the destination handle.
    #[allow(dead_code)] // Produced by the DP transform starting in fz-za0.2.
    DestTupleBegin {
        token: InitTokenId,
        arity: usize,
    },
    /// Initialize one field of an unpublished tuple destination.
    ///
    /// Consumes `token` and produces `next`. The enclosing `Stmt::Let` binds
    /// a dead/unit marker; the destination itself remains named by `dest`.
    #[allow(dead_code)] // Produced by the DP transform starting in fz-za0.2.
    DestTupleSet {
        dest: Var,
        token: InitTokenId,
        index: u32,
        value: Var,
        next: InitTokenId,
    },
    /// Freeze a fully-initialized unpublished destination into an ordinary
    /// immutable value. The enclosing `Stmt::Let` binds the published value.
    #[allow(dead_code)] // Produced by the DP transform starting in fz-za0.2.
    DestFreeze {
        dest: Var,
        token: InitTokenId,
    },
    /// Project the i-th element of a tuple.
    TupleField(Var, u32),
    /// Project a named field from a schema-backed struct.
    StructField(Var, String),
    /// Build a list [v1, v2, ... | optional_tail]; tail defaults to Nil.
    MakeList(Vec<Var>, Option<Var>),
    /// Mint the first token for a destination-built list chain.
    #[allow(dead_code)] // Produced by the DP transform starting in fz-za0.3.
    DestListBegin {
        token: InitTokenId,
    },
    /// Initialize one unpublished list cons destination and return the newly
    /// constructed cons ref. `tail = None` means the empty-list sentinel.
    #[allow(dead_code)] // Produced by the DP transform starting in fz-za0.3.
    DestListCons {
        token: InitTokenId,
        head: Var,
        tail: Option<Var>,
        next: InitTokenId,
    },
    /// Freeze a destination-built list value into an ordinary immutable list.
    #[allow(dead_code)] // Produced by the DP transform starting in fz-za0.3.
    DestListFreeze {
        list: Var,
        token: InitTokenId,
    },
    /// Build a thin function reference: callable code identity with no
    /// environment payload.
    MakeFnRef(CallsiteIdent, FnId),
    /// Allocate a closure: callable code identity plus the captured
    /// environment locals.
    MakeClosure(CallsiteIdent, FnId, Vec<Var>),
    /// Build a map from (key, value) pairs in insertion order.
    MakeMap(Vec<(Var, Var)>),
    /// Functional update of `base` map: every key in entries must exist.
    MapUpdate(Var, Vec<(Var, Var)>),
    /// Allocate an unpublished map destination. `base` seeds the destination
    /// with an existing immutable map before `extra` additional entries are set.
    #[allow(dead_code)] // Produced by the DP transform starting in fz-za0.4.
    DestMapBegin {
        token: InitTokenId,
        base: Option<Var>,
        extra: usize,
    },
    /// Set one key/value pair in an unpublished map destination.
    #[allow(dead_code)] // Produced by the DP transform starting in fz-za0.4.
    DestMapPut {
        map: Var,
        token: InitTokenId,
        key: Var,
        value: Var,
        next: InitTokenId,
    },
    /// Sort/dedup a map destination and publish the immutable map.
    #[allow(dead_code)] // Produced by the DP transform starting in fz-za0.4.
    DestMapFreeze {
        map: Var,
        token: InitTokenId,
    },
    /// `m[k]` — bracket access. Returns nil if key absent.
    MapGet(Var, Var),
    /// Matcher-only map lookup. Returns a private miss sentinel if absent so
    /// present `nil` remains distinguishable from absence.
    MatcherMapGet(Var, Var),
    /// True when a `MatcherMapGet` result is the private miss sentinel.
    IsMatcherMapMiss(Var),
    /// Build a bitstring from a sequence of fields.
    MakeBitstring(Vec<BitFieldIr>),
    /// fz-cty.8 — byte-payload bitstring with materialised bytes and bit
    /// length. Codegen interns the payload as a module-private data symbol and
    /// emits a single allocation call.
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
    /// For structural types (ints, tuples, lists, etc.) this is a real runtime
    /// tag check. For opaque types, the check is resolved to a constant by
    /// the planner (opaque types have no runtime tag) — the branch is then
    /// eliminated by DCE.
    TypeTest(Var, Box<Ty>),

    /// fz-axu.4 (K3) — brand-mint. Tags the source value with the
    /// nominal brand `name` (resolved against `Module.brand_inners` to
    /// recover the inner type). Pure at the type-system level: the
    /// result type keeps the source's structural axes and adds
    /// `brands = {name}`. Runtime-identity: codegen and the interpreter
    /// pass the source value through unchanged. K5's erasure pass
    /// rewrites `Brand(v, _)` to a simple alias for `v` once typing is
    /// stable, so post-erasure IR contains no `Brand` nodes.
    ///
    /// Not user-visible in v1. The L3 desugaring pass inserts these
    /// for literal `"…"` → utf8 mint sites.
    Brand(Var, String),
}

impl Prim {
    /// Insert every `Var` this prim reads into `used`. The single exhaustive
    /// source of truth for prim operand vars — backward slices (dispatch-mask
    /// analysis) and liveness (`ir_dce`) both rely on it, so the compiler-
    /// enforced exhaustive match guarantees no operand is ever silently missed.
    pub fn collect_used_vars(&self, used: &mut HashSet<Var>) {
        match self {
            Prim::Const(_) | Prim::MakeFnRef(_, _) | Prim::DestTupleBegin { .. } | Prim::DestListBegin { .. } => {}
            Prim::ConstBitstring(_, _) => {}
            Prim::BinOp(_, a, b) => {
                used.insert(*a);
                used.insert(*b);
            }
            Prim::UnOp(_, a) | Prim::ListHead(a) | Prim::ListTail(a) | Prim::IsEmptyList(a) | Prim::IsListCons(a) => {
                used.insert(*a);
            }
            Prim::Extern(_, _, args) => {
                for arg in args {
                    used.insert(arg.var);
                }
            }
            Prim::MakeTuple(args) => {
                for v in args {
                    used.insert(*v);
                }
            }
            Prim::MakeStruct { fields, .. } => {
                for (_, v) in fields {
                    used.insert(*v);
                }
            }
            Prim::DestTupleSet { dest, value, .. } => {
                used.insert(*dest);
                used.insert(*value);
            }
            Prim::DestFreeze { dest, .. } => {
                used.insert(*dest);
            }
            Prim::DestListCons { head, tail, .. } => {
                used.insert(*head);
                if let Some(tail) = tail {
                    used.insert(*tail);
                }
            }
            Prim::DestListFreeze { list, .. } => {
                used.insert(*list);
            }
            Prim::TupleField(a, _) | Prim::StructField(a, _) => {
                used.insert(*a);
            }
            Prim::MakeList(els, tail) => {
                for v in els {
                    used.insert(*v);
                }
                if let Some(t) = tail {
                    used.insert(*t);
                }
            }
            Prim::MakeClosure(_, _, caps) => {
                for v in caps {
                    used.insert(*v);
                }
            }
            Prim::MakeMap(entries) => {
                for (k, v) in entries {
                    used.insert(*k);
                    used.insert(*v);
                }
            }
            Prim::MapUpdate(base, entries) => {
                used.insert(*base);
                for (k, v) in entries {
                    used.insert(*k);
                    used.insert(*v);
                }
            }
            Prim::DestMapBegin { base, .. } => {
                if let Some(base) = base {
                    used.insert(*base);
                }
            }
            Prim::DestMapPut { map, key, value, .. } => {
                used.insert(*map);
                used.insert(*key);
                used.insert(*value);
            }
            Prim::DestMapFreeze { map, .. } => {
                used.insert(*map);
            }
            Prim::MapGet(a, b) | Prim::MatcherMapGet(a, b) => {
                used.insert(*a);
                used.insert(*b);
            }
            Prim::IsMatcherMapMiss(v) => {
                used.insert(*v);
            }
            Prim::MakeBitstring(fields) => {
                for f in fields {
                    used.insert(f.value);
                    if let Some(BitSizeIr::Var(sv)) = &f.size {
                        used.insert(*sv);
                    }
                }
            }
            Prim::BitReaderInit(a) | Prim::BitReaderDone(a) => {
                used.insert(*a);
            }
            Prim::BitReadField { reader, size, .. } => {
                used.insert(*reader);
                if let Some(BitSizeIr::Var(sv)) = size {
                    used.insert(*sv);
                }
            }
            Prim::TypeTest(v, _) | Prim::Brand(v, _) => {
                used.insert(*v);
            }
        }
    }
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

/// fz-fyq.2 — which branch of a `Term::If` is provably never taken.
///
/// Published per `(FnId, BlockId)` by `ir_planner` in `ModulePlan::dead_branches`.
/// Cross-spec consensus: a branch is `Dead` only if every live spec of the
/// enclosing fn agreed the scrutinee narrows to `none` on that side. A
/// branch dead under some specs and live under others is source-reachable
/// and must not appear here (e.g. `sum`'s `[]` arm — dead in the narrow
/// `[list(int_set)]` spec but live in the recursive `[nil | list(int_set)]`
/// spec).
///
/// Both-branches-dead means the enclosing If is unreachable; out of scope
/// here and handled by block-level DCE. So at most one variant per If.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DeadBranch {
    Then,
    Else,
}

/// fz-fyq.1 — origin of a `Term::If`, set at lowering time.
///
/// Distinguishes user-authored conditionals (`if`/`case`/`with`/guards in
/// the source) from `If` terminators ir_lower generates as scaffolding for
/// pattern dispatch. Consumers branch on this:
///
/// - The unreachable-arm diagnostic (`collect_diagnostics`) fires only on
///   `User` — a synthesized check the planner proves dead is not noise the
///   programmer caused.
/// - Planned-body materialization may fold any-origin dead branches once the
///   planner publishes the branch as dead for that specialization.
///
/// On the term itself, not in a side-table: transformations that clone,
/// remove, or renumber blocks must carry branch origin with the branch, so
/// survival is structural instead of depending on stale `(FnId, BlockId)`
/// metadata.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BranchOrigin {
    /// Hand-written conditional in source: `if`, `case`, `with`, fn guards.
    User,
    /// Generated by `Expr::Match` pattern-bind dispatch.
    PatternBind,
    /// Generated by multi-clause fn-clause selection.
    ClauseDispatch,
    /// Generated by `emit_param_type_guards` for `@spec`-typed parameters.
    ParamGuard,
}

#[derive(Debug, Clone)]
pub enum Term {
    Goto(BlockId, Vec<Var>),
    If {
        cond: Var,
        then_b: BlockId,
        else_b: BlockId,
        origin: BranchOrigin,
    },
    Call {
        ident: CallsiteIdent,
        callee: FnId,
        args: Vec<Var>,
        continuation: Cont,
    },
    TailCall {
        ident: CallsiteIdent,
        callee: FnId,
        args: Vec<Var>,
        /// True when the callee is in the same SCC as the caller — i.e., this
        /// call is on a loop back-edge. Set by ir_lower via the SCC map from
        /// ir_planner. Self-recursion is the degenerate SCC-of-one case; mutual
        /// recursion (f→g→f) is covered automatically. Back-edge sites get
        /// the yield-check inline check in JIT/AOT codegen and in the interp.
        is_back_edge: bool,
    },
    /// Invoke a closure value (Var holding a Value::IrClosure). The closure's
    /// captured slots are spliced ahead of `args` when entering the lambda's fn.
    CallClosure {
        ident: CallsiteIdent,
        closure: Var,
        args: Vec<Var>,
        continuation: Cont,
    },
    TailCallClosure {
        ident: CallsiteIdent,
        closure: Var,
        args: Vec<Var>,
    },
    Return(Var),
    Halt(Var),
    /// fz-yxs — selective `receive do … after … end`. The cached dispatch
    /// plan is the executable route. Clause bodies receive bound pattern vars
    /// (source order)
    /// followed by `captures`. Body fns tail-call the join cont set up by
    /// lowering — Term::ReceiveMatched is itself a terminator.
    ///
    /// `pinned` carries the outer-scope vars referenced via `^name`
    /// inside any clause's pattern (snapshotted at the receive site);
    /// `captures` carries the outer-scope vars threaded into every
    /// body/guard/after fn so they can keep evaluating in scope.
    ReceiveMatched {
        ident: CallsiteIdent,
        clauses: Vec<ReceiveClause>,
        /// Cached AST-free dispatch plan for interpreter and native receive probes.
        dispatch: Arc<PatternDispatchPlan>,
        after: Option<ReceiveAfter>,
        /// Outer-scope vars referenced by `^name` patterns across all
        /// clauses, paired with their source names so backends can
        /// resolve `^name` lookups when materialising the matcher.
        /// Deduplicated by name at lowering time.
        pinned: Vec<(String, Var)>,
        captures: Vec<Var>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ContinuationProvenanceKind {
    DirectCall { callee: FnId, args: Vec<Var> },
    ClosureCall { closure: Var, args: Vec<Var> },
    DispatchBody { bindings: Vec<(Var, PatternSubjectRef)> },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContinuationProvenance {
    pub caller: FnId,
    pub captured: Vec<Var>,
    pub capture_param_offset: usize,
    pub kind: ContinuationProvenanceKind,
}

/// fz-yxs — one arm of a `Term::ReceiveMatched`.
#[derive(Debug, Clone)]
pub struct ReceiveClause {
    /// Intrinsic identity for this clause outcome site. Planner discovery,
    /// reachability, and codegen use this instead of reconstructing a fresh
    /// ident from `span`.
    pub ident: CallsiteIdent,
    /// Names of the pattern's bound vars in source order. The body
    /// and guard fns take these as their first `bound_names.len()`
    /// parameters; the rest of their params are the captures.
    pub bound_names: Vec<String>,
    /// Optional guard fn. Params = bound vars ++ captures. Returns
    /// bool. Pure-codegen restricted (verified by ir_planner via F3).
    pub guard: Option<FnId>,
    /// Clause body fn. Params = bound vars ++ captures. Body tail-
    /// calls the join cont set up by ir_lower.
    pub body: FnId,
    /// Span of the whole `pattern when guard -> body` clause.
    pub span: Span,
}

/// fz-yxs — optional `after timeout -> body` tail clause.
#[derive(Debug, Clone)]
pub struct ReceiveAfter {
    /// Intrinsic identity for this after-outcome site.
    pub ident: CallsiteIdent,
    /// Timeout value, computed into a Var before the ReceiveMatched
    /// term. Interpreted at runtime as milliseconds, or the atom
    /// `:infinity` for "no timer".
    pub timeout: Var,
    /// After body fn. Params = captures only (no message). Tail-calls
    /// the join cont set up by ir_lower.
    pub body: FnId,
    /// Span of the `after … -> …` clause.
    pub span: Span,
}

/// Default optimizer boundary for selective-receive outcome closures.
///
/// A receive matcher may classify, extract, and materialize the winning
/// closure, but ordinary clause/outcome code starts behind an opaque closure
/// env. Its body spec key is therefore all-`any` by default, preventing
/// receive result values from cloning downstream continuation lattices.
pub fn receive_outcome_spec_key<Ty: Clone>(any: &Ty, param_count: usize) -> Vec<Ty> {
    vec![any.clone(); param_count]
}

impl Term {
    /// Construct a `Term::If` with `BranchOrigin::User`. Convenient for the
    /// many non-lowering construction sites (tests, reducer/fold rewrites,
    /// user-source If lowering) where the origin is obviously `User`.
    /// Lowering paths that synthesize Ifs build the struct variant directly
    /// with the appropriate origin.
    #[cfg(test)]
    pub fn if_user(cond: Var, then_b: BlockId, else_b: BlockId) -> Self {
        Term::If {
            cond,
            then_b,
            else_b,
            origin: BranchOrigin::User,
        }
    }

    /// fz-kgk — the `CallsiteIdent` if this Term is a call-shape
    /// terminator, else `None`. `Goto` / `If` / `Return` / `Halt` are
    /// not callsites; the others all carry an ident.
    pub fn ident(&self) -> Option<&CallsiteIdent> {
        match self {
            Term::Call { ident, .. }
            | Term::TailCall { ident, .. }
            | Term::CallClosure { ident, .. }
            | Term::TailCallClosure { ident, .. }
            | Term::ReceiveMatched { ident, .. } => Some(ident),
            _ => None,
        }
    }

    /// fz-rrh — overwrite this Term's `CallsiteIdent` with a fresh one
    /// keyed by `span`. No-op for non-call-shape terminators and for
    /// DUMMY spans (preserves whatever the term already has).
    ///
    /// Lets `LowerCtx::set_term_at` auto-upgrade idents whose
    /// per-construction span was missing — most ir_lower call sites
    /// already pass the real span to `set_term_at`, so this hoists
    /// the span into the intrinsic identity without per-site edits.
    pub fn set_source_span(&mut self, span: Span) {
        if span.is_dummy() {
            return;
        }
        let new_ident = CallsiteIdent::from_source(span);
        match self {
            Term::Call { ident, .. }
            | Term::TailCall { ident, .. }
            | Term::CallClosure { ident, .. }
            | Term::TailCallClosure { ident, .. }
            | Term::ReceiveMatched { ident, .. } => *ident = new_ident,
            _ => {}
        }
    }
}

impl Prim {
    /// fz-kgk — convenience constructor for callsite-bearing prims.
    pub fn make_fn_ref(span: Span, fn_id: FnId) -> Self {
        Prim::MakeFnRef(CallsiteIdent::from_source(span), fn_id)
    }

    pub fn make_closure(span: Span, fn_id: FnId, captured: Vec<Var>) -> Self {
        Prim::MakeClosure(CallsiteIdent::from_source(span), fn_id, captured)
    }

    pub fn extern_call(span: Span, extern_id: ExternId, args: Vec<ExternArg>) -> Self {
        Prim::Extern(CallsiteIdent::from_source(span), extern_id, args)
    }

    /// fz-rrh — overwrite the `CallsiteIdent` on a callsite-bearing prim
    /// with a fresh one keyed by `span`. No-op for other prims and
    /// for DUMMY spans. Mirror of `Term::set_source_span`.
    pub fn set_source_span(&mut self, span: Span) {
        if span.is_dummy() {
            return;
        }
        match self {
            Prim::MakeFnRef(ident, _) | Prim::MakeClosure(ident, _, _) | Prim::Extern(ident, _, _) => {
                *ident = CallsiteIdent::from_source(span);
            }
            _ => {}
        }
    }
}

pub(crate) fn visit_prim_vars(prim: &Prim, mut visit: impl FnMut(Var)) {
    match prim {
        Prim::Const(_) | Prim::DestTupleBegin { .. } | Prim::DestListBegin { .. } | Prim::ConstBitstring(_, _) => {}
        Prim::BinOp(_, a, b) | Prim::MapGet(a, b) | Prim::MatcherMapGet(a, b) => {
            visit(*a);
            visit(*b);
        }
        Prim::UnOp(_, v)
        | Prim::ListHead(v)
        | Prim::ListTail(v)
        | Prim::IsEmptyList(v)
        | Prim::IsListCons(v)
        | Prim::TupleField(v, _)
        | Prim::StructField(v, _)
        | Prim::IsMatcherMapMiss(v)
        | Prim::BitReaderInit(v)
        | Prim::BitReaderDone(v)
        | Prim::Brand(v, _)
        | Prim::TypeTest(v, _) => visit(*v),
        Prim::Extern(_, _, args) => {
            for arg in args {
                visit(arg.var);
            }
        }
        Prim::MakeTuple(args) => {
            for v in args {
                visit(*v);
            }
        }
        Prim::MakeStruct { fields, .. } => {
            for (_, v) in fields {
                visit(*v);
            }
        }
        Prim::DestTupleSet { dest, value, .. } => {
            visit(*dest);
            visit(*value);
        }
        Prim::DestFreeze { dest, .. } => visit(*dest),
        Prim::DestListCons { head, tail, .. } => {
            visit(*head);
            if let Some(tail) = tail {
                visit(*tail);
            }
        }
        Prim::DestListFreeze { list, .. } => visit(*list),
        Prim::DestMapBegin { base, .. } => {
            if let Some(base) = base {
                visit(*base);
            }
        }
        Prim::DestMapPut { map, key, value, .. } => {
            visit(*map);
            visit(*key);
            visit(*value);
        }
        Prim::DestMapFreeze { map, .. } => visit(*map),
        Prim::MakeList(elems, tail) => {
            for v in elems {
                visit(*v);
            }
            if let Some(tail) = tail {
                visit(*tail);
            }
        }
        Prim::MakeFnRef(_, _) => {}
        Prim::MakeClosure(_, _, caps) => {
            for v in caps {
                visit(*v);
            }
        }
        Prim::MakeMap(entries) => {
            for (k, v) in entries {
                visit(*k);
                visit(*v);
            }
        }
        Prim::MapUpdate(base, entries) => {
            visit(*base);
            for (k, v) in entries {
                visit(*k);
                visit(*v);
            }
        }
        Prim::MakeBitstring(fields) => {
            for field in fields {
                visit(field.value);
                if let Some(BitSizeIr::Var(v)) = field.size {
                    visit(v);
                }
            }
        }
        Prim::BitReadField { reader, size, .. } => {
            visit(*reader);
            if let Some(BitSizeIr::Var(v)) = size {
                visit(*v);
            }
        }
    }
}

pub(crate) fn visit_term_vars(term: &Term, mut visit: impl FnMut(Var)) {
    match term {
        Term::Goto(_, args) | Term::TailCall { args, .. } | Term::TailCallClosure { args, .. } => {
            for v in args {
                visit(*v);
            }
        }
        Term::If { cond, .. } | Term::Return(cond) | Term::Halt(cond) => visit(*cond),
        Term::Call { args, continuation, .. } | Term::CallClosure { args, continuation, .. } => {
            for v in args {
                visit(*v);
            }
            for v in &continuation.captured {
                visit(*v);
            }
        }
        Term::ReceiveMatched {
            after,
            pinned,
            captures,
            ..
        } => {
            for (_, v) in pinned {
                visit(*v);
            }
            for v in captures {
                visit(*v);
            }
            if let Some(after) = after {
                visit(after.timeout);
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Block {
    pub id: BlockId,
    pub params: Vec<Var>,
    pub stmts: Vec<Stmt>,
    pub terminator: Term,
}

/// fz-f88.5 — origin of an FnIr, set at lowering time.
///
/// Lets downstream consumers (dump filtering, reachability accounting)
/// answer "where did this fn come from?" without re-deriving from the
/// `prelude_fn_id_cutoff` boundary or string-matching the `name`
/// (`fn_clause_N`, `k_N`, `lambda_N`, etc.).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FnCategory {
    /// Parsed from user source.
    User,
    /// `runtime.fz` builtins lowered alongside user code.
    Prelude,
    /// Per-clause continuation minted by `mint_cont_fn` — the
    /// `fn_clause_N` family.
    MultiClauseCont,
    /// `lambda_N` — top-level body of a lifted closure.
    LambdaLift,
    /// CPS continuation: `k_N`.
    CpsCont,
    /// Internal matcher router. These fns are compiler-owned
    /// dispatch thunks: they test subjects, then tail-call leaf/fail
    /// continuations with captured bindings. They are not user-callable and
    /// should disappear under normal inlining for simple case sites.
    Matcher,
    /// Control-flow continuation: `if_then` / `if_else` /
    /// `case_clause_N` / `cond_arm_N` / `with_else_N`.
    ControlFlowCont,
    /// Compiler-owned REPL expression entry. These fns receive the current
    /// top-level frame as params and return `{display, next_frame...}`.
    ReplEntry,
}

#[derive(Debug, Clone)]
pub struct FnIr {
    pub id: FnId,
    pub name: String,
    /// Populated by liveness analysis in .11.6 (0 means "not yet computed").
    pub frame_schema_id: u32,
    pub blocks: Vec<Block>,
    pub entry: BlockId,
    /// fz-f88.5 — origin tag set at lowering. Default `User` so
    /// hand-built `FnBuilder` callers (tests) don't have to thread it.
    pub category: FnCategory,
    /// Source module path whose lexical scope owns this lowered fn.
    pub owner_module: String,
    /// Entry parameter positions that are arity-bearing holes (`_`).
    /// The slot exists physically, but semantic specialization must not
    /// inspect its type.
    pub ignored_entry_params: Vec<bool>,
    /// Entry parameters that transport physical capabilities, not source
    /// values. They are ignored by semantic specialization by construction.
    pub physical_entry_params: Vec<Var>,
    /// Object-local capabilities available inside this function body.
    pub physical_capabilities: Vec<PhysicalCapabilityFact>,
}

impl FnIr {
    pub fn semantic_key(&self, input_tys: Vec<Ty>) -> Vec<KeySlot> {
        let entry_params = &self.block(self.entry).params;
        input_tys
            .into_iter()
            .enumerate()
            .map(|(i, ty)| {
                let is_physical = entry_params
                    .get(i)
                    .is_some_and(|param| self.is_physical_entry_param(*param));
                if is_physical || self.ignored_entry_params.get(i).copied().unwrap_or(false) {
                    None
                } else {
                    Some(ty)
                }
            })
            .collect()
    }

    pub fn semantic_entry_params(&self) -> Vec<Var> {
        self.block(self.entry)
            .params
            .iter()
            .enumerate()
            .filter_map(|(i, param)| {
                let ignored = self.ignored_entry_params.get(i).copied().unwrap_or(false);
                (!ignored && !self.is_physical_entry_param(*param)).then_some(*param)
            })
            .collect()
    }

    pub fn is_physical_entry_param(&self, param: Var) -> bool {
        self.physical_entry_params.contains(&param)
    }

    pub fn dedup_physical_facts(&mut self) {
        let mut entry_seen = HashSet::new();
        self.physical_entry_params.retain(|param| entry_seen.insert(*param));
        let mut capability_seen = HashSet::new();
        self.physical_capabilities.retain(|fact| capability_seen.insert(*fact));
    }

    pub fn block(&self, id: BlockId) -> &Block {
        self.blocks.iter().find(|b| b.id == id).expect("unknown block")
    }

    /// Per entry-param slot: `true` iff that param can influence which code
    /// this body runs — i.e. it reaches, through the body's value graph,
    /// either the condition of a `Term::If` (which branch) or the invoked
    /// value of a closure call (which callable identity, hence which body).
    /// These "dispatch subjects" must stay type-precise; the complement carries
    /// data the body neither branches on nor invokes, so distinct activations
    /// that agree on every dispatch subject are behaviourally identical up to
    /// those slots and may be joined.
    ///
    /// Sound by construction: the only intra-body binding edges are
    /// `Stmt::Let` (def reads its prim's operands) and `Term::Goto` (a target
    /// block param reads the matching call arg). A backward closure over both,
    /// seeded from every branch condition and every invoked-closure operand,
    /// reaches every entry param a control decision can depend on — never
    /// fewer. Entry params not reached are safe to widen: widening them cannot
    /// flip a branch or redirect a call in this body.
    pub fn dispatch_subject_slots(&self) -> Vec<bool> {
        let mut def_uses: HashMap<Var, Vec<Var>> = HashMap::new();
        let mut param_sources: HashMap<Var, Vec<Var>> = HashMap::new();
        let mut work: Vec<Var> = Vec::new();
        for block in &self.blocks {
            for Stmt::Let(v, prim) in &block.stmts {
                let mut uses = HashSet::new();
                prim.collect_used_vars(&mut uses);
                def_uses.entry(*v).or_default().extend(uses);
            }
            match &block.terminator {
                Term::If { cond, .. } => work.push(*cond),
                Term::CallClosure { closure, .. } | Term::TailCallClosure { closure, .. } => work.push(*closure),
                Term::Goto(target, args) => {
                    for (param, arg) in self.block(*target).params.iter().zip(args) {
                        param_sources.entry(*param).or_default().push(*arg);
                    }
                }
                _ => {}
            }
        }
        let mut reached: HashSet<Var> = HashSet::new();
        while let Some(v) = work.pop() {
            if !reached.insert(v) {
                continue;
            }
            if let Some(uses) = def_uses.get(&v) {
                work.extend(uses.iter().copied());
            }
            if let Some(srcs) = param_sources.get(&v) {
                work.extend(srcs.iter().copied());
            }
        }
        self.block(self.entry)
            .params
            .iter()
            .map(|param| reached.contains(param))
            .collect()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PhysicalCapabilityFact {
    pub source: Var,
    pub capability: PhysicalCapability,
}

impl PhysicalCapabilityFact {
    pub fn map_vars(self, mut map: impl FnMut(Var) -> Var) -> Self {
        Self {
            source: map(self.source),
            capability: self.capability.map_vars(map),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PhysicalCapability {
    OwnedConsReuse { head: Var },
}

impl PhysicalCapability {
    pub fn map_vars(self, mut map: impl FnMut(Var) -> Var) -> Self {
        match self {
            PhysicalCapability::OwnedConsReuse { head } => PhysicalCapability::OwnedConsReuse { head: map(head) },
        }
    }
}

/// Side-tables that map IR positions back to source spans. Populated by
/// `ir_lower` as it goes; consumed by `ir_planner` / diagnostics renderers
/// to point at the right source byte range for a given Var or Stmt.
///
/// The IR types themselves stay narrow (`Prim`, `Stmt`, `Term` carry no
/// span fields). Spans live here so codegen-internal IR transformations
/// don't have to thread spans through every constructor.
#[derive(Debug, Default, Clone)]
pub struct SourceInfo {
    /// Indexed by `Var.0`: span of the source expression / pattern that
    /// introduced this Var. `Span::DUMMY` for compiler-introduced temps
    /// or any Var introduced before .20.4 hooks (e.g. ir_planner's
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
    ///
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
        self.var_span.get(v.0 as usize).copied().unwrap_or(Span::DUMMY)
    }

    pub fn fn_span_of(&self, f: FnId) -> Span {
        self.fn_span.get(f.0 as usize).copied().unwrap_or(Span::DUMMY)
    }
}

#[derive(Debug, Default, Clone)]
pub struct Module {
    /// Logical module path for this IR module. Root/top-level code uses "".
    pub module_path: String,
    pub fns: Vec<FnIr>,
    pub schemas: Vec<Schema>,
    pub source: SourceInfo,
    /// Atom names indexed by id. `atom_names[id]` is the source spelling of
    /// the atom interned at `Const::Atom(id)`. Populated by ir_lower from
    /// its per-module AtomTable. Every runtime path (JIT, interp, AOT)
    /// hands this to its Process so `any_value::debug::render` can print
    /// `:ok` instead of `:atom_1`. Closed by fz-ul4.25.
    pub atom_names: Vec<String>,
    /// O(1) index from FnId to position in `fns`. Kept in sync by
    /// `ModuleBuilder::add_fn`; never mutated after `build()`.
    pub fn_idx: HashMap<FnId, usize>,
    /// All `extern "C" fn` declarations. Stable: ExternId is a counter, not a vec index.
    pub externs: Vec<ExternDecl>,
    /// O(1) index from ExternId to position in `externs`. Mirrors fn_idx.
    pub extern_idx: HashMap<ExternId, usize>,
    /// First-class imported module calls. The terminator still carries a
    /// placeholder `FnId` until link/LTO resolution loads the provider
    /// implementation and rewrites the edge to a direct local call.
    pub external_call_edges: Vec<ExternalCallEdge>,
    pub protocol_call_targets: HashMap<FnId, ProtocolCallTarget>,
    pub protocol_registry: ProtocolRegistry,
    /// fz-jg5.12 (RED.9) — Fns marked as reduction boundaries. Populated
    /// by ir_lower from `@spec` declarations. The reducer treats these as
    /// firewalls: a declared spec is the user's signed contract that the
    /// body is a stable unit, so reduction does not cross into it (except
    /// for trivially-inlinable single-stmt bodies, which carry no risk).
    pub boundary_fns: HashSet<FnId>,
    /// fz-swt.8 — Inner-type map for opaque aliases declared anywhere
    /// in the program. Keyed by the module-qualified opaque tag (as
    /// stored on the opaque type token); value is the parsed body
    /// `T` following the `opaque` keyword. The planner reads this at
    /// `Prim::MapGet(handle, :value)` sites to type `handle.value` as
    /// `T` instead of falling back to the generic map-lookup result.
    /// Populated by `ir_lower::lower_program_full` from the resolved
    /// `Program.opaque_inners`.
    pub opaque_inners: HashMap<String, Ty>,
    /// fz-axu.2 (K1) — Inner-type map for `refines` brand declarations,
    /// parallel to `opaque_inners`. Keyed by the qualified brand tag
    /// (as stored on the brand type token); value is the parsed body
    /// `T` following the `refines` keyword. Populated by
    /// `ir_lower::lower_program_full` from the resolved
    /// `Program.brand_inners`.
    pub brand_inners: HashMap<String, Ty>,
    pub struct_schemas: BTreeMap<String, Vec<String>>,
    /// Resolved declared `@spec` overload sets keyed by IR function id. Used by
    /// call typing for source-level polymorphic contracts.
    pub declared_specs: HashMap<FnId, ResolvedSpecSet>,
    /// Function correspondence keyed by IR function id. Declared source
    /// functions contribute structural groups directly from `@spec`; CPS
    /// continuations contribute synthesized groups from lowering provenance.
    pub function_correspondence: HashMap<FnId, Vec<StructuralCorrespondenceGroup>>,
    /// Continuation provenance keyed by synthesized continuation FnId. This is
    /// the durable IR-owned record of how lowering split a non-tail call or
    /// matcher body, from which planner-facing correspondence can be derived
    /// and re-derived after result-flow rewrites.
    pub continuation_provenance: HashMap<FnId, ContinuationProvenance>,
}

/// Tarjan strongly-connected components over a fn call graph. Returns SCCs in
/// reverse-topological order (leaves first). Stable node iteration keeps the
/// numbering deterministic across runs.
fn tarjan_scc(graph: &HashMap<FnId, HashSet<FnId>>) -> Vec<Vec<FnId>> {
    struct State<'a> {
        graph: &'a HashMap<FnId, HashSet<FnId>>,
        index_of: HashMap<FnId, u32>,
        lowlink: HashMap<FnId, u32>,
        on_stack: HashSet<FnId>,
        stack: Vec<FnId>,
        next_idx: u32,
        sccs: Vec<Vec<FnId>>,
    }
    fn strong(s: &mut State, v: FnId) {
        s.index_of.insert(v, s.next_idx);
        s.lowlink.insert(v, s.next_idx);
        s.next_idx += 1;
        s.stack.push(v);
        s.on_stack.insert(v);
        if let Some(succs) = s.graph.get(&v) {
            let succs: Vec<FnId> = succs.iter().copied().collect();
            for w in succs {
                if !s.index_of.contains_key(&w) {
                    strong(s, w);
                    let wl = *s.lowlink.get(&w).unwrap();
                    let vl = *s.lowlink.get(&v).unwrap();
                    s.lowlink.insert(v, vl.min(wl));
                } else if s.on_stack.contains(&w) {
                    let wi = *s.index_of.get(&w).unwrap();
                    let vl = *s.lowlink.get(&v).unwrap();
                    s.lowlink.insert(v, vl.min(wi));
                }
            }
        }
        if s.index_of.get(&v) == s.lowlink.get(&v) {
            let mut comp = Vec::new();
            loop {
                let w = s.stack.pop().unwrap();
                s.on_stack.remove(&w);
                comp.push(w);
                if w == v {
                    break;
                }
            }
            s.sccs.push(comp);
        }
    }
    let mut s = State {
        graph,
        index_of: HashMap::new(),
        lowlink: HashMap::new(),
        on_stack: HashSet::new(),
        stack: Vec::new(),
        next_idx: 0,
        sccs: Vec::new(),
    };
    let mut nodes: Vec<FnId> = graph.keys().copied().collect();
    nodes.sort_by_key(|f| f.0);
    for v in nodes {
        if !s.index_of.contains_key(&v) {
            strong(&mut s, v);
        }
    }
    s.sccs
}

impl Module {
    #[cfg(test)]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn module_path(&self) -> &str {
        &self.module_path
    }

    /// A borrowed view of this module's brand/opaque inner-type maps, for the
    /// brand-blind value-equality decisions (`is_value_disjoint`).
    pub fn nominals(&self) -> Nominals<'_> {
        Nominals::new(&self.brand_inners, &self.opaque_inners)
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

    /// The set of fns that participate in recursion: every fn in a
    /// strongly-connected component larger than one, plus self-recursive
    /// singletons. The recursion call graph deliberately excludes the
    /// callee->continuation edge — a non-tail call's continuation belongs to
    /// the caller's control flow, not the callee's body, so including it would
    /// make plain sequential chains look recursive.
    ///
    /// One source of truth for "recursive fn": the planner widens recursive
    /// spec keys by this set, and type inference converges recursive
    /// activations' non-dispatch slots by it — the two must agree.
    pub fn recursive_fns(&self) -> HashSet<FnId> {
        let graph = self.recursion_call_graph();
        let mut recursive: HashSet<FnId> = HashSet::new();
        for scc in tarjan_scc(&graph) {
            if scc.len() > 1 {
                recursive.extend(scc);
            } else if let Some(fid) = scc.first()
                && graph.get(fid).is_some_and(|succs| succs.contains(fid))
            {
                recursive.insert(*fid);
            }
        }
        recursive
    }

    fn recursion_call_graph(&self) -> HashMap<FnId, HashSet<FnId>> {
        let mut graph: HashMap<FnId, HashSet<FnId>> = HashMap::new();
        for f in &self.fns {
            let edges = graph.entry(f.id).or_default();
            for block in &f.blocks {
                for Stmt::Let(_, prim) in &block.stmts {
                    if let Prim::MakeFnRef(_, target) | Prim::MakeClosure(_, target, _) = prim {
                        edges.insert(*target);
                    }
                }
                match &block.terminator {
                    Term::Call {
                        callee, continuation, ..
                    } => {
                        edges.insert(*callee);
                        edges.insert(continuation.fn_id);
                    }
                    Term::TailCall { callee, .. } => {
                        edges.insert(*callee);
                    }
                    Term::CallClosure { continuation, .. } => {
                        edges.insert(continuation.fn_id);
                    }
                    Term::ReceiveMatched { clauses, after, .. } => {
                        for clause in clauses {
                            edges.insert(clause.body);
                            if let Some(guard) = clause.guard {
                                edges.insert(guard);
                            }
                        }
                        if let Some(after) = after {
                            edges.insert(after.body);
                        }
                    }
                    Term::Goto(..)
                    | Term::If { .. }
                    | Term::TailCallClosure { .. }
                    | Term::Return(_)
                    | Term::Halt(_) => {}
                }
            }
        }
        graph
    }

    pub fn rewrite_external_calls_for_lto(
        &mut self,
        exports: &BTreeMap<ExportKey, FnId>,
    ) -> Result<usize, ExternalLinkError> {
        let edges = take(&mut self.external_call_edges);
        let mut rewritten = 0;
        for edge in edges {
            let Some(target) = exports.get(&edge.target).copied() else {
                self.external_call_edges.push(edge.clone());
                return Err(ExternalLinkError::MissingTarget(edge.target));
            };
            if !rewrite_external_callsite(self, &edge.callsite, target) {
                self.external_call_edges.push(edge.clone());
                return Err(ExternalLinkError::MissingCallsite(edge.callsite));
            }
            rewritten += 1;
        }
        Ok(rewritten)
    }

    pub fn interface_export_map(
        &self,
        interfaces: &BTreeMap<ModuleName, ModuleInterface>,
    ) -> BTreeMap<ExportKey, FnId> {
        let mut out = BTreeMap::new();
        for (module, interface) in interfaces {
            for export in &interface.exports {
                let name = format!("{}.{}", module, export.name);
                if let Some(f) = self
                    .fns
                    .iter()
                    .find(|f| f.name == name && f.block(f.entry).params.len() == export.arity)
                {
                    out.insert(ExportKey::new(module.clone(), export.name.clone(), export.arity), f.id);
                }
            }
            for protocol_impl in &interface.protocol_impls {
                for callback in &protocol_impl.callbacks {
                    let name = format!("{}.{}", callback.module, callback.name);
                    if let Some(f) = self
                        .fns
                        .iter()
                        .find(|f| f.name == name && f.block(f.entry).params.len() == callback.arity)
                    {
                        out.insert(callback.clone(), f.id);
                    }
                }
            }
        }
        out
    }
}

fn rewrite_external_callsite(m: &mut Module, callsite: &CallsiteId, target: FnId) -> bool {
    let Some(fn_idx) = m.fn_idx.get(&callsite.caller).copied() else {
        return false;
    };
    let Some(target_idx) = m.fn_idx.get(&target).copied() else {
        return false;
    };
    let target_arity = m.fns[target_idx].block(m.fns[target_idx].entry).params.len();
    for block in &mut m.fns[fn_idx].blocks {
        match &mut block.terminator {
            Term::Call {
                ident, callee, args, ..
            } if callsite.slot == EmitSlot::Direct && *ident == callsite.ident && args.len() == target_arity => {
                if *callee == target {
                    return false;
                }
                *callee = target;
                return true;
            }
            Term::TailCall {
                ident, callee, args, ..
            } if callsite.slot == EmitSlot::Direct && *ident == callsite.ident && args.len() == target_arity => {
                if *callee == target {
                    return false;
                }
                *callee = target;
                return true;
            }
            _ => {}
        }
    }
    false
}

pub(crate) fn rewrite_external_callsite_for_link(m: &mut Module, callsite: &CallsiteId, target: FnId) -> bool {
    rewrite_external_callsite(m, callsite, target)
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
    category: FnCategory,
    owner_module: String,
    ignored_params: HashSet<Var>,
    physical_entry_params: Vec<Var>,
    physical_capabilities: Vec<PhysicalCapabilityFact>,
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
            category: FnCategory::User,
            owner_module: String::new(),
            ignored_params: HashSet::new(),
            physical_entry_params: Vec::new(),
            physical_capabilities: Vec::new(),
        }
    }

    /// fz-f88.5 — set the origin category. Default is `User`.
    pub fn with_category(mut self, category: FnCategory) -> Self {
        self.category = category;
        self
    }

    pub fn with_owner_module(mut self, owner_module: impl Into<String>) -> Self {
        self.owner_module = owner_module.into();
        self
    }

    pub fn fresh_var(&mut self) -> Var {
        let v = Var(self.next_var);
        self.next_var += 1;
        v
    }

    pub fn mark_param_ignored(&mut self, v: Var) {
        self.ignored_params.insert(v);
    }

    fn is_entry_param(&self, param: Var) -> bool {
        self.entry
            .and_then(|entry| self.blocks.iter().find(|block| block.id == entry))
            .is_some_and(|entry| entry.params.contains(&param))
    }

    pub fn record_physical_entry_param(&mut self, param: Var) {
        if !self.physical_entry_params.contains(&param) {
            self.physical_entry_params.push(param);
        }
    }

    pub fn record_owned_cons_reuse_capability(&mut self, head: Var, source_cons: Var) {
        debug_assert!(
            self.is_entry_param(source_cons),
            "owned-cons reuse sources must be physical entry params"
        );
        if self.is_entry_param(source_cons) {
            self.record_physical_entry_param(source_cons);
        }
        if let Some(fact) = self
            .physical_capabilities
            .iter_mut()
            .find(|fact| matches!(fact.capability, PhysicalCapability::OwnedConsReuse { head: h } if h == head))
        {
            fact.source = source_cons;
            return;
        }
        self.physical_capabilities.push(PhysicalCapabilityFact {
            source: source_cons,
            capability: PhysicalCapability::OwnedConsReuse { head },
        });
    }

    pub fn owned_cons_reuse_source_for_head(&self, head: Var) -> Option<Var> {
        self.physical_capabilities
            .iter()
            .find_map(|fact| match fact.capability {
                PhysicalCapability::OwnedConsReuse { head: h } if h == head => Some(fact.source),
                _ => None,
            })
    }

    pub fn prim_for_var(&self, var: Var) -> Option<&Prim> {
        self.blocks.iter().find_map(|block| {
            block
                .stmts
                .iter()
                .find_map(|Stmt::Let(v, prim)| (*v == var).then_some(prim))
        })
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
        self.blocks.iter_mut().find(|b| b.id == id).expect("unknown block")
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
        let ignored_entry_params = self
            .blocks
            .iter()
            .find(|b| b.id == entry)
            .map(|b| b.params.iter().map(|p| self.ignored_params.contains(p)).collect())
            .unwrap_or_default();
        let mut f = FnIr {
            id: self.id,
            name: self.name,
            frame_schema_id: 0,
            blocks: self.blocks,
            entry,
            category: self.category,
            owner_module: self.owner_module,
            ignored_entry_params,
            physical_entry_params: self.physical_entry_params,
            physical_capabilities: self.physical_capabilities,
        };
        f.dedup_physical_facts();
        f
    }
}

pub struct ModuleBuilder {
    module_path: String,
    next_fn: u32,
    fns: Vec<FnIr>,
    fn_idx: HashMap<FnId, usize>,
    schemas: Vec<Schema>,
    pub external_call_edges: Vec<ExternalCallEdge>,
    pub protocol_call_targets: HashMap<FnId, ProtocolCallTarget>,
}

impl ModuleBuilder {
    pub fn new() -> Self {
        Self {
            module_path: String::new(),
            next_fn: 0,
            fns: Vec::new(),
            fn_idx: HashMap::new(),
            schemas: Vec::new(),
            external_call_edges: Vec::new(),
            protocol_call_targets: HashMap::new(),
        }
    }

    #[cfg(test)]
    pub fn with_module_path(mut self, module_path: impl Into<String>) -> Self {
        self.module_path = module_path.into();
        self
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

    #[cfg(test)]
    pub fn add_schema(&mut self, schema: Schema) -> u32 {
        let id = self.schemas.len() as u32;
        self.schemas.push(schema);
        id
    }

    pub fn build(self) -> Module {
        Module {
            module_path: self.module_path,
            fns: self.fns,
            fn_idx: self.fn_idx,
            schemas: self.schemas,
            source: SourceInfo::default(),
            atom_names: Vec::new(),
            externs: Vec::new(),
            extern_idx: HashMap::new(),
            external_call_edges: self.external_call_edges,
            protocol_call_targets: self.protocol_call_targets,
            protocol_registry: ProtocolRegistry::default(),
            boundary_fns: HashSet::new(),
            opaque_inners: HashMap::new(),
            brand_inners: HashMap::new(),
            struct_schemas: Default::default(),
            declared_specs: HashMap::new(),
            function_correspondence: HashMap::new(),
            continuation_provenance: HashMap::new(),
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

impl fmt::Display for InitTokenId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "tok{}", self.0)
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

fn fmt_extern_arg_list(args: &[ExternArg]) -> String {
    args.iter()
        .map(|arg| match arg.marshal {
            ExternMarshal::Fixed(_) => arg.var.to_string(),
            ExternMarshal::Ascribed(ty) => format!("{}::{:?}", arg.var, ty),
            ExternMarshal::Auto => format!("{}::auto", arg.var),
        })
        .collect::<Vec<_>>()
        .join(", ")
}

impl fmt::Display for Prim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Prim::Const(c) => write!(f, "const({})", c),
            Prim::BinOp(op, a, b) => write!(f, "{} {} {}", a, op, b),
            Prim::UnOp(op, a) => write!(f, "{} {}", op, a),
            Prim::Extern(_, e, args) => {
                write!(f, "extern#{}([{}])", e.0, fmt_extern_arg_list(args))
            }
            Prim::ListHead(l) => write!(f, "head({})", l),
            Prim::ListTail(l) => write!(f, "tail({})", l),
            Prim::IsEmptyList(l) => write!(f, "is_nil({})", l),
            Prim::IsListCons(l) => write!(f, "is_list_cons({})", l),
            Prim::MakeTuple(args) => write!(f, "tuple([{}])", fmt_var_list(args)),
            Prim::MakeStruct { module, fields } => {
                let fields = fields
                    .iter()
                    .map(|(name, var)| format!("{}: {}", name, var))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "struct({}, [{}])", module, fields)
            }
            Prim::DestTupleBegin { token, arity } => {
                write!(f, "dest_tuple_begin(arity={}, token={})", arity, token)
            }
            Prim::DestTupleSet {
                dest,
                token,
                index,
                value,
                next,
            } => write!(
                f,
                "dest_tuple_set({}, {}, field={}, value={}, next={})",
                dest, token, index, value, next
            ),
            Prim::DestFreeze { dest, token } => write!(f, "dest_freeze({}, {})", dest, token),
            Prim::TupleField(v, i) => write!(f, "tuple_field({}, {})", v, i),
            Prim::StructField(v, name) => write!(f, "struct_field({}, {})", v, name),
            Prim::MakeList(els, tail) => match tail {
                Some(t) => write!(f, "list([{}] | {})", fmt_var_list(els), t),
                None => write!(f, "list([{}])", fmt_var_list(els)),
            },
            Prim::DestListBegin { token } => write!(f, "dest_list_begin(token={})", token),
            Prim::DestListCons {
                token,
                head,
                tail,
                next,
            } => match tail {
                Some(tail) => write!(
                    f,
                    "dest_list_cons({}, head={}, tail={}, next={})",
                    token, head, tail, next
                ),
                None => write!(f, "dest_list_cons({}, head={}, tail=[], next={})", token, head, next),
            },
            Prim::DestListFreeze { list, token } => {
                write!(f, "dest_list_freeze({}, {})", list, token)
            }
            Prim::MakeFnRef(_ident, fid) => write!(f, "fn_ref({})", fid),
            Prim::MakeClosure(_ident, fid, captured) => {
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
            Prim::DestMapBegin { token, base, extra } => match base {
                Some(base) => write!(f, "dest_map_begin(token={}, base={}, extra={})", token, base, extra),
                None => write!(f, "dest_map_begin(token={}, extra={})", token, extra),
            },
            Prim::DestMapPut {
                map,
                token,
                key,
                value,
                next,
            } => write!(
                f,
                "dest_map_put({}, {}, key={}, value={}, next={})",
                map, token, key, value, next
            ),
            Prim::DestMapFreeze { map, token } => write!(f, "dest_map_freeze({}, {})", map, token),
            Prim::MapGet(m, k) => write!(f, "map_get({}, {})", m, k),
            Prim::MatcherMapGet(m, k) => write!(f, "matcher_map_get({}, {})", m, k),
            Prim::IsMatcherMapMiss(v) => write!(f, "is_matcher_map_miss({})", v),
            Prim::MakeBitstring(fields) => {
                write!(f, "bitstring([{}])", fields.len())
            }
            Prim::ConstBitstring(bytes, bit_len) => {
                write!(f, "const_bitstring(byte_len={}, bit_len={})", bytes.len(), bit_len)
            }
            Prim::BitReaderInit(v) => write!(f, "bit_reader_init({})", v),
            Prim::BitReadField { reader, .. } => write!(f, "bit_read_field({})", reader),
            Prim::BitReaderDone(v) => write!(f, "bit_reader_done({})", v),
            Prim::TypeTest(v, d) => {
                write!(f, "type_test({}, {})", v, ty_display(d))
            }
            Prim::Brand(v, name) => write!(f, "brand({}, {})", v, name),
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
            Term::If {
                cond, then_b, else_b, ..
            } => write!(f, "if {} then {} else {}", cond, then_b, else_b),
            Term::Call {
                callee,
                args,
                continuation,
                ..
            } => write!(f, "call {}([{}]) -> {}", callee, fmt_var_list(args), continuation),
            Term::TailCall { callee, args, .. } => {
                write!(f, "tail_call {}([{}])", callee, fmt_var_list(args))
            }
            Term::CallClosure {
                closure,
                args,
                continuation,
                ..
            } => write!(
                f,
                "call_closure {}([{}]) -> {}",
                closure,
                fmt_var_list(args),
                continuation
            ),
            Term::TailCallClosure { closure, args, .. } => {
                write!(f, "tail_call_closure {}([{}])", closure, fmt_var_list(args))
            }
            Term::Return(v) => write!(f, "return {}", v),
            Term::Halt(v) => write!(f, "halt {}", v),
            Term::ReceiveMatched {
                clauses,
                after,
                pinned,
                captures,
                ..
            } => {
                let pin_strs: Vec<String> = pinned.iter().map(|(n, v)| format!("^{}={}", n, v)).collect();
                write!(
                    f,
                    "receive_matched [{} clauses] pinned=[{}] caps=[{}]",
                    clauses.len(),
                    pin_strs.join(", "),
                    fmt_var_list(captures),
                )?;
                if let Some(a) = after {
                    write!(f, " after({} -> fn{})", a.timeout, a.body.0)?;
                }
                Ok(())
            }
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
        if !self.physical_entry_params.is_empty() {
            let mut params = self.physical_entry_params.clone();
            params.sort_by_key(|param| param.0);
            writeln!(f, "  semantic_params=[{}]", fmt_var_list(&self.semantic_entry_params()))?;
            for param in params {
                writeln!(f, "  physical_param {}", param)?;
            }
        }
        if !self.physical_capabilities.is_empty() {
            let mut facts = self.physical_capabilities.clone();
            facts.sort_by_key(|fact| fact.source.0);
            for fact in facts {
                writeln!(f, "  physical {}", fact)?;
            }
        }
        for b in &self.blocks {
            write!(f, "{}", b)?;
        }
        writeln!(f, "}}")
    }
}

impl fmt::Display for PhysicalCapabilityFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.source, self.capability)
    }
}

impl fmt::Display for PhysicalCapability {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PhysicalCapability::OwnedConsReuse { head } => {
                write!(f, "owned_cons_reuse(head={})", head)
            }
        }
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
mod fz_ir_test;
