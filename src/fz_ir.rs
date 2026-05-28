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
use crate::modules::identity::{ExportKey, ModuleName};
use fz_runtime::heap::Schema;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

/// fz-kgk — intrinsic identity for a callsite (call-shape terminator
/// or `Prim::MakeClosure` stmt).
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
/// - `fork_inlined(parent, into_fn)` — `ir_inline` clones a `Term`
///   into a *new caller's* body. The cloned callsite is genuinely
///   distinct; same span, fresh `Rc` → new identity.
/// - `synthesize_from_return(call_parent, span)` — `ir_inline` rewrites
///   a callee's `Return(v)` into `TailCall(K, [v, ...captures])` while
///   splicing. The new TailCall is a *new* callsite.
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

    pub fn fork_inlined(parent: &Self, _into_fn: FnId) -> Self {
        Self(Rc::new(CallsiteIdentInner {
            span: parent.0.span,
        }))
    }

    pub fn synthesize_from_return(_call_parent: &Self, span: Span) -> Self {
        Self(Rc::new(CallsiteIdentInner { span }))
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
    /// The continuation of `Term::Call` / `Term::CallClosure` /
    /// `Term::Receive` — i.e., (cont.fn_id, [slot0, captures...]).
    Cont,
    /// fz-try.11: `Term::CallClosure` / `Term::TailCallClosure` callsite.
    /// Purely structural — identifies *where* in the IR the closure
    /// dispatch happens, not which clause of the closure's arrow DNF
    /// resolves. Pre-fz-try.11 this was split into `CallClosureKnown`
    /// and `ClosureLit(c, s)`; the design wanted slots to be structural
    /// ("where") while the planner's dispatch target shapes the variation
    /// ("what").
    ClosureCall,
    /// `Prim::MakeClosure` stmt. Per fz-kgk, the per-stmt index is no
    /// longer needed — the `CallsiteIdent` on the Prim disambiguates
    /// multiple MakeClosures in the same block.
    MakeClosure,
}

/// fz-kgk — the identity of one callsite in the module.
///
/// `(caller, ident, slot)` uniquely names a place that can produce a
/// callee target. `ident` is the intrinsic identity carried on the
/// `Term` (or `Prim::MakeClosure`); see [`CallsiteIdent`] for the
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
                write!(
                    f,
                    "missing external callsite for caller {}",
                    callsite.caller
                )
            }
        }
    }
}

impl std::error::Error for ExternalLinkError {}

impl CallsiteId {
    pub fn new(caller: FnId, ident: &CallsiteIdent, slot: EmitSlot) -> Self {
        Self {
            caller,
            ident: ident.clone(),
            slot,
        }
    }
}

/// fz-9pr.16 — why the reducer left a callsite alone. Threaded through
/// every None-returning branch of `try_reduce_call` / `walk_block` so
/// `fz dump --emit outcomes` can answer "why didn't X fold?" without
/// a debugger.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StalledReason {
    /// At least one argument type was not a literal — the reducer
    /// can only fold under fully-concrete literal arg types. Specifically: the
    /// arg is genuine `Any` (widening fixpoint, missing-info default,
    /// etc.). Vars are surfaced as `UnresolvedTypeVar` instead.
    OpaqueArg,
    /// fz-try.10 — at least one argument type is a parametric type
    /// variable. Distinct
    /// from `OpaqueArg`: an unresolved type variable is a *parametric*
    /// claim ("specialize me at a call site"), not a *widening* one
    /// ("we don't know"). Surfaced separately so outcome rows can
    /// distinguish "this fold needs a concrete witness" from "this fold
    /// needs better type info."
    UnresolvedTypeVar,
    /// Per-top-level-callsite unroll budget hit before the recursive
    /// walk could find a literal return.
    BudgetExhausted,
    /// Callee body contains a non-reducible prim (Extern, MakeMap,
    /// MapUpdate, MakeBitstring, BitReader*, AllocStruct).
    NonReduciblePrim,
    /// Callee is in `module.boundary_fns` and the body isn't trivially
    /// inlinable — `@spec`'d fns are reduction firewalls.
    BoundaryFn,
    /// `Term::(Tail)CallClosure`, but the closure operand's type
    /// doesn't carry a `closure_lit` — no statically-known target.
    NoClosureLitTarget,
    /// Same-callee recursive call without provable structural
    /// argument decrease — would risk non-termination if walked.
    StructuralDecrease,
    /// Callee body shape rejects the walk: `Term::Halt`, `Term::Receive`,
    /// pathological Goto depth, parameter-arity mismatch, or a Return
    /// of a non-scalar-literal type (tuple / list / closure_lit return).
    CalleeBodyShape,
    /// Catch-all for paths not yet classified. Should be rare; expand
    /// the enum rather than reach for this.
    Other,
}

impl std::fmt::Display for StalledReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            StalledReason::OpaqueArg => "OpaqueArg",
            StalledReason::UnresolvedTypeVar => "UnresolvedTypeVar",
            StalledReason::BudgetExhausted => "BudgetExhausted",
            StalledReason::NonReduciblePrim => "NonReduciblePrim",
            StalledReason::BoundaryFn => "BoundaryFn",
            StalledReason::NoClosureLitTarget => "NoClosureLitTarget",
            StalledReason::StructuralDecrease => "StructuralDecrease",
            StalledReason::CalleeBodyShape => "CalleeBodyShape",
            StalledReason::Other => "Other",
        })
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
    pub ret_descr: crate::types::Ty,
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
    Extern(ExternId, Vec<ExternArg>),
    ListHead(Var),
    ListTail(Var),
    IsEmptyList(Var),
    /// Build a tuple (struct with the canonical tuple-of-arity-N schema).
    MakeTuple(Vec<Var>),
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
    /// Allocate a closure: a struct holding the IR fn id of the lambda body
    /// plus the captured environment locals.
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
    /// For structural types (ints, tuples, lists, etc.) this is a real runtime
    /// tag check. For opaque types, the check is resolved to a constant by
    /// the planner (opaque types have no runtime tag) — the branch is then
    /// eliminated by DCE.
    TypeTest(Var, Box<crate::types::Ty>),

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
/// - The dead-branch fold (`ir_branch_fold`, fz-fyq.4) acts on any origin
///   once the planner publishes the branch as dead.
///
/// On the term itself, not in a side-table: `ir_inline::splice_callee_into_caller`
/// renumbers BlockIds when splicing, so a `(FnId, BlockId)`-keyed side-table
/// loses every callee origin at inline time. The post-type chain in
/// `ir_codegen::compile` runs `inline_single_use_conts`, so inlining is the
/// happy path. Survival is structural when the data lives on the term.
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
        ident: CallsiteIdent,
        continuation: Cont,
    },
    /// fz-yxs — selective `receive do … after … end` (see
    /// `docs/receive-matched.md §7`). The cached Matcher is the executable
    /// route. Clause bodies receive bound pattern vars (source order)
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
        /// Cached AST-free matcher for interpreter and native receive probes.
        matcher: std::sync::Arc<crate::matcher::Matcher>,
        after: Option<ReceiveAfter>,
        /// Outer-scope vars referenced by `^name` patterns across all
        /// clauses, paired with their source names so backends can
        /// resolve `^name` lookups when materialising the matcher.
        /// Deduplicated by name at lowering time.
        pinned: Vec<(String, Var)>,
        captures: Vec<Var>,
    },
}

/// fz-yxs — one arm of a `Term::ReceiveMatched`.
#[derive(Debug, Clone)]
pub struct ReceiveClause {
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
            | Term::Receive { ident, .. }
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
            | Term::Receive { ident, .. }
            | Term::ReceiveMatched { ident, .. } => *ident = new_ident,
            _ => {}
        }
    }
}

impl Prim {
    /// fz-kgk — convenience constructor for the only Prim variant
    /// that is a callsite.
    pub fn make_closure(span: Span, fn_id: FnId, captured: Vec<Var>) -> Self {
        Prim::MakeClosure(CallsiteIdent::from_source(span), fn_id, captured)
    }

    /// fz-rrh — overwrite the `CallsiteIdent` on a `MakeClosure` prim
    /// with a fresh one keyed by `span`. No-op for other prims and
    /// for DUMMY spans. Mirror of `Term::set_source_span`.
    pub fn set_source_span(&mut self, span: Span) {
        if span.is_dummy() {
            return;
        }
        if let Prim::MakeClosure(ident, _, _) = self {
            *ident = CallsiteIdent::from_source(span);
        }
    }
}

pub(crate) fn visit_prim_vars(prim: &Prim, mut visit: impl FnMut(Var)) {
    match prim {
        Prim::Const(_)
        | Prim::DestTupleBegin { .. }
        | Prim::DestListBegin { .. }
        | Prim::ConstBitstring(_, _) => {}
        Prim::BinOp(_, a, b) | Prim::MapGet(a, b) | Prim::MatcherMapGet(a, b) => {
            visit(*a);
            visit(*b);
        }
        Prim::UnOp(_, v)
        | Prim::ListHead(v)
        | Prim::ListTail(v)
        | Prim::IsEmptyList(v)
        | Prim::TupleField(v, _)
        | Prim::IsMatcherMapMiss(v)
        | Prim::BitReaderInit(v)
        | Prim::BitReaderDone(v)
        | Prim::Brand(v, _)
        | Prim::TypeTest(v, _) => visit(*v),
        Prim::Extern(_, args) => {
            for arg in args {
                visit(arg.var);
            }
        }
        Prim::MakeTuple(args) => {
            for v in args {
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
        Prim::DestMapPut {
            map, key, value, ..
        } => {
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

pub(crate) fn prim_uses_var(prim: &Prim, needle: Var) -> bool {
    let mut found = false;
    visit_prim_vars(prim, |v| found |= v == needle);
    found
}

pub(crate) fn visit_term_vars(term: &Term, mut visit: impl FnMut(Var)) {
    match term {
        Term::Goto(_, args) | Term::TailCall { args, .. } | Term::TailCallClosure { args, .. } => {
            for v in args {
                visit(*v);
            }
        }
        Term::If { cond, .. } | Term::Return(cond) | Term::Halt(cond) => visit(*cond),
        Term::Call {
            args, continuation, ..
        }
        | Term::CallClosure {
            args, continuation, ..
        } => {
            for v in args {
                visit(*v);
            }
            for v in &continuation.captured {
                visit(*v);
            }
        }
        Term::Receive { continuation, .. } => {
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

pub(crate) fn term_uses_var(term: &Term, needle: Var) -> bool {
    let mut found = false;
    visit_term_vars(term, |v| found |= v == needle);
    found
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
    /// CPS continuation: `k_N` or `k_receive_N`.
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
    pub physical_entry_params: Vec<PhysicalEntryParam>,
    /// FIP-style reuse credits available inside this function body.
    ///
    /// Lowering records these when a destructured list head and its original
    /// source cons cell are carried together into a generated helper body.
    /// Codegen may consume a compatible credit to rebuild a cons by reusing the
    /// source cell or falling back to allocation when the runtime alias bit is
    /// set.
    pub owned_cons_reuse_credits: Vec<OwnedConsReuseCredit>,
}

impl FnIr {
    pub fn semantic_key(&self, input_tys: Vec<crate::types::Ty>) -> Vec<crate::types::KeySlot> {
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
        self.physical_entry_params
            .iter()
            .any(|physical| physical.param == param)
    }

    pub fn block(&self, id: BlockId) -> &Block {
        self.blocks
            .iter()
            .find(|b| b.id == id)
            .expect("unknown block")
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OwnedConsReuseCredit {
    pub head: Var,
    pub source_cons: Var,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PhysicalEntryParam {
    pub param: Var,
    pub capability: PhysicalCapability,
}

impl PhysicalEntryParam {
    pub fn map_vars(self, mut map: impl FnMut(Var) -> Var) -> Self {
        Self {
            param: map(self.param),
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
            PhysicalCapability::OwnedConsReuse { head } => {
                PhysicalCapability::OwnedConsReuse { head: map(head) }
            }
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
    pub protocol_registry: crate::protocols::ProtocolRegistry,
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
    pub opaque_inners: HashMap<String, crate::types::Ty>,
    /// fz-axu.2 (K1) — Inner-type map for `refines` brand declarations,
    /// parallel to `opaque_inners`. Keyed by the qualified brand tag
    /// (as stored on the brand type token); value is the parsed body
    /// `T` following the `refines` keyword. Populated by
    /// `ir_lower::lower_program_full` from the resolved
    /// `Program.brand_inners`.
    pub brand_inners: HashMap<String, crate::types::Ty>,
    /// Resolved declared `@spec`s keyed by IR function id. Used by call
    /// typing for source-level polymorphic contracts.
    pub declared_specs: HashMap<FnId, crate::type_expr::ResolvedSpec>,
}

impl Module {
    #[cfg(test)]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn module_path(&self) -> &str {
        &self.module_path
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

    pub fn rewrite_external_calls_for_lto(
        &mut self,
        exports: &BTreeMap<ExportKey, FnId>,
    ) -> Result<usize, ExternalLinkError> {
        let edges = std::mem::take(&mut self.external_call_edges);
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
        interfaces: &BTreeMap<ModuleName, crate::modules::interface::ModuleInterface>,
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
                    out.insert(
                        ExportKey::new(module.clone(), export.name.clone(), export.arity),
                        f.id,
                    );
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
    let target_arity = m.fns[target_idx]
        .block(m.fns[target_idx].entry)
        .params
        .len();
    for block in &mut m.fns[fn_idx].blocks {
        match &mut block.terminator {
            Term::Call {
                ident,
                callee,
                args,
                ..
            } if callsite.slot == EmitSlot::Direct
                && *ident == callsite.ident
                && args.len() == target_arity =>
            {
                *callee = target;
                return true;
            }
            Term::TailCall {
                ident,
                callee,
                args,
                ..
            } if callsite.slot == EmitSlot::Direct
                && *ident == callsite.ident
                && args.len() == target_arity =>
            {
                *callee = target;
                return true;
            }
            _ => {}
        }
    }
    false
}

pub(crate) fn rewrite_external_callsite_for_link(
    m: &mut Module,
    callsite: &CallsiteId,
    target: FnId,
) -> bool {
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
    ignored_params: std::collections::HashSet<Var>,
    physical_entry_params: Vec<PhysicalEntryParam>,
    owned_cons_reuse_credits: Vec<OwnedConsReuseCredit>,
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
            ignored_params: std::collections::HashSet::new(),
            physical_entry_params: Vec::new(),
            owned_cons_reuse_credits: Vec::new(),
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

    pub fn record_physical_entry_param(&mut self, param: Var, capability: PhysicalCapability) {
        if let Some(physical) = self
            .physical_entry_params
            .iter_mut()
            .find(|physical| physical.param == param)
        {
            physical.capability = capability;
            return;
        }
        self.physical_entry_params
            .push(PhysicalEntryParam { param, capability });
    }

    pub fn record_owned_cons_physical_entry_param(&mut self, head: Var, source_cons: Var) {
        self.record_physical_entry_param(source_cons, PhysicalCapability::OwnedConsReuse { head });
    }

    pub fn record_owned_cons_reuse_credit(&mut self, head: Var, source_cons: Var) {
        if self.is_entry_param(source_cons) {
            self.record_owned_cons_physical_entry_param(head, source_cons);
        }
        if let Some(credit) = self
            .owned_cons_reuse_credits
            .iter_mut()
            .find(|credit| credit.head == head)
        {
            credit.source_cons = source_cons;
            return;
        }
        self.owned_cons_reuse_credits
            .push(OwnedConsReuseCredit { head, source_cons });
    }

    pub fn owned_cons_reuse_source_for_head(&self, head: Var) -> Option<Var> {
        self.owned_cons_reuse_credits
            .iter()
            .find_map(|credit| (credit.head == head).then_some(credit.source_cons))
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
        let ignored_entry_params = self
            .blocks
            .iter()
            .find(|b| b.id == entry)
            .map(|b| {
                b.params
                    .iter()
                    .map(|p| self.ignored_params.contains(p))
                    .collect()
            })
            .unwrap_or_default();
        FnIr {
            id: self.id,
            name: self.name,
            frame_schema_id: 0,
            blocks: self.blocks,
            entry,
            category: self.category,
            owner_module: self.owner_module,
            ignored_entry_params,
            physical_entry_params: self.physical_entry_params,
            owned_cons_reuse_credits: self.owned_cons_reuse_credits,
        }
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
            protocol_registry: crate::protocols::ProtocolRegistry::default(),
            boundary_fns: HashSet::new(),
            opaque_inners: HashMap::new(),
            brand_inners: HashMap::new(),
            declared_specs: HashMap::new(),
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
    vars.iter()
        .map(|v| v.to_string())
        .collect::<Vec<_>>()
        .join(", ")
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
            Prim::Extern(e, args) => {
                write!(f, "extern#{}([{}])", e.0, fmt_extern_arg_list(args))
            }
            Prim::ListHead(l) => write!(f, "head({})", l),
            Prim::ListTail(l) => write!(f, "tail({})", l),
            Prim::IsEmptyList(l) => write!(f, "is_nil({})", l),
            Prim::MakeTuple(args) => write!(f, "tuple([{}])", fmt_var_list(args)),
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
                None => write!(
                    f,
                    "dest_list_cons({}, head={}, tail=[], next={})",
                    token, head, next
                ),
            },
            Prim::DestListFreeze { list, token } => {
                write!(f, "dest_list_freeze({}, {})", list, token)
            }
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
                Some(base) => write!(
                    f,
                    "dest_map_begin(token={}, base={}, extra={})",
                    token, base, extra
                ),
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
            Prim::TypeTest(v, d) => {
                write!(
                    f,
                    "type_test({}, {})",
                    v,
                    crate::concrete_types::ty_display(d)
                )
            }
            Prim::Brand(v, name) => write!(f, "brand({}, {})", v, name),
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
            Term::If {
                cond,
                then_b,
                else_b,
                ..
            } => write!(f, "if {} then {} else {}", cond, then_b, else_b),
            Term::Call {
                callee,
                args,
                continuation,
                ..
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
            Term::Receive { continuation, .. } => write!(f, "receive -> {}", continuation),
            Term::ReceiveMatched {
                clauses,
                after,
                pinned,
                captures,
                ..
            } => {
                let pin_strs: Vec<String> = pinned
                    .iter()
                    .map(|(n, v)| format!("^{}={}", n, v))
                    .collect();
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
            params.sort_by_key(|physical| physical.param.0);
            writeln!(
                f,
                "  semantic_params=[{}]",
                fmt_var_list(&self.semantic_entry_params())
            )?;
            for physical in params {
                writeln!(f, "  physical {}", physical)?;
            }
        }
        for b in &self.blocks {
            write!(f, "{}", b)?;
        }
        writeln!(f, "}}")
    }
}

impl fmt::Display for PhysicalEntryParam {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.param, self.capability)
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
        b.set_terminator(entry, Term::if_user(cond, then_b, else_b));
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
    fn physical_entry_params_are_not_semantic_key_inputs() {
        use crate::types::Types;

        let mut b = FnBuilder::new(FnId(0), "with_physical");
        let head = b.fresh_var();
        let source = b.fresh_var();
        let value = b.fresh_var();
        let entry = b.block(vec![source, value]);
        b.record_owned_cons_physical_entry_param(head, source);
        b.set_terminator(entry, Term::Return(value));
        let fn_ir = b.build();

        assert_eq!(
            fn_ir.physical_entry_params,
            vec![PhysicalEntryParam {
                param: source,
                capability: PhysicalCapability::OwnedConsReuse { head },
            }]
        );
        assert_eq!(fn_ir.semantic_entry_params(), vec![value]);

        let mut t = crate::types::ConcreteTypes;
        let key = fn_ir.semantic_key(vec![t.any(), t.int()]);
        assert!(key[0].is_none());
        assert!(key[1].is_some());
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
            Term::If { then_b, else_b, .. } => {
                assert_ne!(then_b, else_b);
                assert_eq!(then_b, BlockId(1));
                assert_eq!(else_b, BlockId(2));
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
    fn lto_rewrites_external_call_edge_to_direct_fn_id() {
        let ident = CallsiteIdent::synthetic();
        let mut caller = FnBuilder::new(FnId(0), "caller");
        let entry = caller.block(vec![]);
        caller.set_terminator(
            entry,
            Term::TailCall {
                ident: ident.clone(),
                callee: FnId(999),
                args: Vec::new(),
                is_back_edge: false,
            },
        );
        let mut target = FnBuilder::new(FnId(1), "A.f");
        let target_entry = target.block(vec![]);
        target.set_terminator(target_entry, Term::Halt(Var(0)));
        let mut mb = ModuleBuilder::new();
        mb.add_fn(caller.build());
        mb.add_fn(target.build());
        let mut module = mb.build();
        let export = ExportKey::new(
            crate::modules::identity::ModuleName::from_segments(vec!["A".to_string()]),
            "f",
            0,
        );
        module.external_call_edges.push(ExternalCallEdge {
            callsite: CallsiteId::new(FnId(0), &ident, EmitSlot::Direct),
            target: export.clone(),
        });
        let exports = [(export, FnId(1))].into_iter().collect();

        assert_eq!(module.rewrite_external_calls_for_lto(&exports), Ok(1));
        assert!(module.external_call_edges.is_empty());
        match &module.fn_by_id(FnId(0)).block(BlockId(0)).terminator {
            Term::TailCall { callee, .. } => assert_eq!(*callee, FnId(1)),
            other => panic!("expected TailCall, got {:?}", other),
        }
    }

    #[test]
    fn lto_reports_missing_external_call_target() {
        let ident = CallsiteIdent::synthetic();
        let mut caller = FnBuilder::new(FnId(0), "caller");
        let entry = caller.block(vec![]);
        caller.set_terminator(
            entry,
            Term::TailCall {
                ident: ident.clone(),
                callee: FnId(999),
                args: Vec::new(),
                is_back_edge: false,
            },
        );
        let mut mb = ModuleBuilder::new();
        mb.add_fn(caller.build());
        let mut module = mb.build();
        let export = ExportKey::new(
            crate::modules::identity::ModuleName::from_segments(vec!["Missing".to_string()]),
            "f",
            0,
        );
        module.external_call_edges.push(ExternalCallEdge {
            callsite: CallsiteId::new(FnId(0), &ident, EmitSlot::Direct),
            target: export.clone(),
        });
        let exports = BTreeMap::new();

        assert_eq!(
            module.rewrite_external_calls_for_lto(&exports),
            Err(ExternalLinkError::MissingTarget(export))
        );
        assert!(!module.external_call_edges.is_empty());
    }

    #[test]
    fn lto_export_map_comes_from_validated_interfaces() {
        let mut target = FnBuilder::new(FnId(7), "Math.add");
        let target_entry = target.block(vec![Var(0), Var(1)]);
        target.set_terminator(target_entry, Term::Halt(Var(0)));
        let mut mb = ModuleBuilder::new();
        mb.add_fn(target.build());
        let module = mb.build();

        let math = crate::modules::identity::ModuleName::from_segments(vec!["Math".to_string()]);
        let mut interfaces = BTreeMap::new();
        interfaces.insert(
            math.clone(),
            crate::modules::interface::ModuleInterface {
                name: math.clone(),
                abi_version: crate::modules::interface::FZ_INTERFACE_ABI_VERSION,
                imports: Vec::new(),
                exports: vec![crate::modules::interface::InterfaceFn {
                    name: "add".to_string(),
                    arity: 2,
                    spec: Some(crate::modules::interface::InterfaceSpec {
                        params: vec![
                            "Ident(\"integer\")".to_string(),
                            "Ident(\"integer\")".to_string(),
                        ],
                        result: "Ident(\"integer\")".to_string(),
                    }),
                    name_span: Span::DUMMY,
                }],
                types: Vec::new(),
                protocols: Vec::new(),
                protocol_impls: Vec::new(),
                docs: None,
                fingerprint_inputs: Vec::new(),
            },
        );

        let key = ExportKey::new(math, "add", 2);
        assert_eq!(
            module.interface_export_map(&interfaces).get(&key),
            Some(&FnId(7))
        );
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
                kind: FieldKind::AnyValue,
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
                ident: CallsiteIdent::synthetic(),
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
                ident: CallsiteIdent::synthetic(),
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
        let one = b.let_(entry, Prim::Const(Const::Int(1)));
        let l = b.let_(entry, Prim::MakeList(vec![one], None));
        let h = b.let_(entry, Prim::ListHead(l));
        let _t = b.let_(entry, Prim::ListTail(l));
        let _z = b.let_(entry, Prim::IsEmptyList(l));
        b.set_terminator(entry, Term::Return(h));
        let s = format!("{}", b.build());
        assert!(s.contains("list([v0])"));
        assert!(s.contains("head(v1)"));
        assert!(s.contains("tail(v1)"));
        assert!(s.contains("is_nil(v1)"));
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
