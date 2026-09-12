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
use crate::dispatch_matrix::pattern::PatternDispatchPlan;
use crate::modules::identity::{Mfa, ModuleName};
use crate::runtime_type_predicate::RuntimeTypePredicate;
use crate::source::Span;
use fz_runtime::heap::Schema;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
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

#[derive(Debug, Clone, PartialEq)]
pub enum BitSizeIr {
    Literal(u32),
    Var(Var),
}

#[derive(Debug, Clone, PartialEq)]
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
    pub target: Mfa,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum DirectCallTarget {
    Local(FnId),
    ProviderBoundary(Mfa),
}

impl DirectCallTarget {
    pub fn local_fn_id(&self) -> Option<FnId> {
        match self {
            Self::Local(fn_id) => Some(*fn_id),
            Self::ProviderBoundary(_) => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProtocolCallTarget {
    pub protocol: ModuleName,
    pub callback: String,
    pub arity: usize,
}

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OwnershipMode {
    Transfer,
    Share,
}

/// The actual operand of an edge that may split a usable reference.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OwnershipUse<T> {
    pub value: T,
    pub mode: OwnershipMode,
}

impl<T> OwnershipUse<T> {
    pub fn transfer(value: T) -> Self {
        Self {
            value,
            mode: OwnershipMode::Transfer,
        }
    }

    pub fn share(value: T) -> Self {
        Self {
            value,
            mode: OwnershipMode::Share,
        }
    }
}

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

    pub fn auto(var: Var) -> Self {
        Self {
            var,
            marshal: ExternMarshal::Auto,
        }
    }
}

/// The calling convention an `extern` declaration names.
///
/// `C` is a plain C symbol: it is called with exactly the declared arguments,
/// and a `binary` parameter arrives as a `*const u8` into the bytes.
///
/// `Fz` is an fz runtime helper: it receives the current `*mut Process` as an
/// implicit first argument -- everything that allocates on the process heap
/// needs one -- and a `binary` parameter arrives as the tagged value ref the
/// runtime itself works in.
///
/// The convention is DECLARED, so adding an allocating primitive is a
/// declaration plus a Rust function. It used to be keyed by symbol name, which
/// meant one hand-written rung in native codegen and another in the
/// interpreter for every such primitive, and no way for either to know it had
/// missed one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ExternAbi {
    C,
    Fz,
}

impl ExternAbi {
    /// Every convention that exists. `parse` and the diagnostic that lists the
    /// alternatives both read this, so a new convention is one entry.
    pub const ALL: &'static [Self] = &[Self::C, Self::Fz];

    /// The name as written in the declaration. Anything else is a diagnostic
    /// there, never a silent fall back to C.
    pub fn parse(abi: &str) -> Option<Self> {
        Self::ALL.iter().copied().find(|candidate| candidate.as_str() == abi)
    }

    pub fn takes_process(self) -> bool {
        matches!(self, Self::Fz)
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Self::C => "C",
            Self::Fz => "fz",
        }
    }
}

impl std::fmt::Display for ExternAbi {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// One resolved `extern` declaration stored in `Module.externs`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternDecl {
    pub id: ExternId,
    pub fz_name: String,
    /// C symbol name (same as fz_name for v1; override possible later).
    pub symbol: String,
    pub params: Vec<ExternTy>,
    pub variadic: bool,
    pub ret: ExternTy,
    pub abi: ExternAbi,
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
    /// The `==` OPERATOR, which compares numbers by value: `1 == 1.0` is true,
    /// and so are `[1] == [1.0]` and `%{a: 1} == %{a: 1.0}`.
    Eq,
    Neq,
    /// STRUCTURAL IDENTITY -- the `===` operator, and the question every kind of
    /// MATCHING asks. `1` and `1.0` are different values, so
    /// `case 1.0 do 1 -> ... end` must not match.
    ///
    /// Separate from `Eq` because they are two questions, not one question with
    /// a flag. They used to share `Eq`, with a `widen_numerics` boolean that
    /// each lowering call site set from what it happened to know about its
    /// caller -- so a guard, which reached the matching lowering, answered
    /// `same?(1, 1.0)` as `:different` where Elixir says `:equal` (fz-5xp.24).
    Identical,
    NotIdentical,
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

#[derive(Debug, Clone, PartialEq)]
pub enum Prim {
    Const(Const),
    BinOp(BinOp, Var, Var),
    UnOp(UnOp, Var),
    /// Publish an ownership-splitting edge; scalar lanes are unchanged.
    Share(Var),
    Extern(CallsiteIdent, ExternId, Vec<ExternArg>),
    Intrinsic(fz_runtime::intrinsic::Intrinsic, Vec<Var>),
    ListHead(Var),
    ListTail(Var),
    IsEmptyList(Var),
    IsListCons(Var),
    /// Build a tuple (struct with the canonical tuple-of-arity-N schema).
    MakeTuple(Vec<Var>),
    /// Build a named struct using a source `defstruct` schema.
    MakeStruct {
        module: fz_runtime::module_name::ModuleName,
        fields: Vec<(String, Var)>,
    },
    /// Project the i-th element of a tuple.
    TupleField(Var, u32),
    /// Project a named field from a schema-backed struct.
    StructField(Var, String),
    /// Build a list [v1, v2, ... | optional_tail]; tail defaults to Nil.
    MakeList(Vec<Var>, Option<Var>, Option<ListRetention<Var>>),
    /// Build a thin function reference: callable code identity with no
    /// environment payload.
    MakeFnRef(CallsiteIdent, FnId),
    /// Allocate a closure: callable code identity plus the captured
    /// environment locals.
    MakeClosure(CallsiteIdent, FnId, Vec<Var>),
    /// Allocate an unpublished map destination. `base` seeds the destination
    /// with an existing immutable map before `extra` additional entries are set.
    DestMapBegin {
        token: InitTokenId,
        base: Option<Var>,
        extra: usize,
    },
    /// Set one key/value pair in an unpublished map destination.
    DestMapPut {
        map: Var,
        token: InitTokenId,
        key: Var,
        value: Var,
        next: InitTokenId,
    },
    /// Sort/dedup a map destination and publish the immutable map.
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
    /// Runtime-membership check over the first-class runtime-observable
    /// predicate layer. Semantic dispatch/refinement stays in `Ty`; direct
    /// runtime tests and cached receive dispatch lower through this explicit
    /// predicate seam because the runtime sees tags/shapes, not full semantic
    /// types.
    RuntimeTypeTest(Var, Box<RuntimeTypePredicate>),
    /// Read one captured value back out of a closure object.
    ///
    /// Captures retain lexical source order. The slot's runtime kind describes
    /// its storage; callers project the complete value to their required ABI.
    ClosureCapture {
        closure: Var,
        index: u32,
    },
}

impl Prim {
    /// Insert every `Var` this prim reads into `used`. The single exhaustive
    /// source of truth for prim operand vars — backward slices (dispatch-mask
    /// analysis) and liveness (`ir_dce`) both rely on it, so the compiler-
    /// enforced exhaustive match guarantees no operand is ever silently missed.
    pub fn collect_used_vars(&self, used: &mut HashSet<Var>) {
        match self {
            Prim::Const(_) | Prim::MakeFnRef(_, _) => {}
            Prim::ConstBitstring(_, _) => {}
            Prim::BinOp(_, a, b) => {
                used.insert(*a);
                used.insert(*b);
            }
            Prim::Share(a)
            | Prim::UnOp(_, a)
            | Prim::ListHead(a)
            | Prim::ListTail(a)
            | Prim::IsEmptyList(a)
            | Prim::IsListCons(a) => {
                used.insert(*a);
            }
            Prim::Intrinsic(_, args) => used.extend(args.iter().copied()),
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
            Prim::TupleField(a, _) | Prim::StructField(a, _) => {
                used.insert(*a);
            }
            Prim::MakeList(els, tail, retention) => {
                for v in els {
                    used.insert(*v);
                }
                if let Some(t) = tail {
                    used.insert(*t);
                }
                if let Some(retention) = retention {
                    used.insert(retention.source);
                }
            }
            Prim::MakeClosure(_, _, caps) => {
                for v in caps {
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
            Prim::RuntimeTypeTest(v, _) => {
                used.insert(*v);
            }
            Prim::ClosureCapture { closure, .. } => {
                used.insert(*closure);
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Let(Var, Prim),
}

/// First-class continuation: an IR fn to invoke with the given captured vars
/// (plus the value(s) being returned to it, supplied by the caller at runtime).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Cont {
    pub fn_id: FnId,
    pub captured: Vec<Var>,
}

/// fz-fyq.2 — which branch of a `Term::If` is provably never taken.
///
/// Published per `(FnId, BlockId)` by frontends that prove a conditional arm dead.
/// Cross-spec consensus: a branch is `Dead` only if every live spec of the
/// enclosing fn agreed the scrutinee narrows to `none` on that side. A
/// branch dead under some specs and live under others is source-reachable
/// and must not appear here (e.g. `sum`'s `[]` arm — dead in the narrow
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
}

#[derive(Debug, Clone, PartialEq)]
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
        callee: DirectCallTarget,
        args: Vec<Var>,
        continuation: Cont,
    },
    TailCall {
        ident: CallsiteIdent,
        callee: DirectCallTarget,
        args: Vec<Var>,
        /// True when the callee is in the same SCC as the caller — i.e., this
        /// call is on a loop back-edge. Set by ir_lower via the SCC map from
        /// ir_planner. Self-recursion is the degenerate SCC-of-one case; mutual
        /// recursion (f→g→f) is covered automatically. Back-edge sites get
        /// the yield-check inline check in JIT/AOT codegen and in the interp.
        is_back_edge: bool,
    },
    /// Invoke a closure value (Var holding a Value::IrClosure).
    ///
    /// Logical call arguments stay in `args` order. The closure environment is
    /// carried separately by the closure value itself and is loaded from `self`
    /// by the callee's entry harness; captures are not prepended to the
    /// user-visible argument list.
    ///
    /// The call is opaque by construction: it dispatches through the
    /// closure's published callable boundary. Calls whose callee grounds to
    /// an exact target are lowered as `Call`/`TailCall` direct edges by the
    /// producer that makes that decision -- they never reach this form.
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
    /// Native/codegen-facing return whose payload is already split into the
    /// transport lanes required by the current function's return seam.
    ReturnLanes(Vec<Var>),
    Halt(Var),
    /// fz-yxs — selective `receive do … after … end`. The cached dispatch
    /// plan is the executable route. Winning edges supply semantic and physical
    /// parameters by identity, followed by shared `captures`.
    ///
    /// `pinned` carries the outer-scope vars referenced via `^name`
    /// inside any clause's pattern;
    /// `captures` carries the outer-scope vars threaded into every
    /// body/guard/after fn so they can keep evaluating in scope.
    ReceiveMatched {
        ident: CallsiteIdent,
        clauses: Vec<ReceiveClause>,
        /// Cached AST-free dispatch plan for interpreter and native receive probes.
        dispatch: Arc<PatternDispatchPlan<RuntimeTypePredicate>>,
        after: Option<ReceiveAfter>,
        /// Pinned inputs followed by prepared keys, indexed by the owning
        /// plan's PinnedValueId and prepared-key ordinal respectively.
        pinned: Vec<Var>,
        captures: Vec<Var>,
    },
}

/// fz-yxs — one arm of a `Term::ReceiveMatched`.
#[derive(Debug, Clone, PartialEq)]
pub struct ReceiveClause {
    /// Intrinsic identity for this clause outcome site. Planner discovery,
    /// reachability, and codegen use this instead of reconstructing a fresh
    /// ident from `span`.
    pub ident: CallsiteIdent,
    /// Winning plan outcome and its exact subject-to-body-parameter edge.
    pub outcome: crate::dispatch_matrix::OutcomeId,
    pub arguments: Vec<(crate::dispatch_matrix::SubjectId, Var)>,
    /// Optional guard fn. Params = outcome arguments ++ captures. Returns
    /// bool. Pure-codegen restricted (verified by ir_planner via F3).
    pub guard: Option<FnId>,
    /// Clause body fn. Params = outcome arguments ++ captures. The body reaches the
    /// enclosing receive join via explicit continuation handoff.
    pub body: FnId,
    /// Span of the whole `pattern when guard -> body` clause.
    pub span: Span,
}

/// fz-yxs — optional `after timeout -> body` tail clause.
#[derive(Debug, Clone, PartialEq)]
pub struct ReceiveAfter {
    /// Intrinsic identity for this after-outcome site.
    pub ident: CallsiteIdent,
    /// Timeout value, computed into a Var before the ReceiveMatched
    /// term. Interpreted at runtime as milliseconds, or the atom
    /// `:infinity` for "no timer".
    pub timeout: Var,
    /// After body fn. Params = captures only (no message). The body reaches
    /// the enclosing receive join via explicit continuation handoff.
    pub body: FnId,
    /// Span of the `after … -> …` clause.
    pub span: Span,
}

/// Default optimizer boundary for selective-receive outcome closures.
///
/// A receive matcher may classify, extract, and materialize the winning
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
}

#[derive(Debug, Clone, PartialEq)]
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
    /// CPS continuation: `k_N`.
    CpsCont,
    /// Control-flow continuation: `if_then` / `if_else` /
    /// `case_clause_N` / `cond_arm_N` / `with_else_N`.
    ControlFlowCont,
}

#[derive(Debug, Clone, PartialEq)]
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
}

impl FnIr {
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

    pub fn dedup_physical_entry_params(&mut self) {
        let mut entry_seen = HashSet::new();
        self.physical_entry_params.retain(|param| entry_seen.insert(*param));
    }

    pub fn block(&self, id: BlockId) -> &Block {
        self.blocks.iter().find(|b| b.id == id).expect("unknown block")
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ListRetention<V> {
    pub source: V,
    pub permission: ListRewritePermission,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ListRewritePermission {
    RetainOnly,
    Rewrite,
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
    pub protocol_call_targets: HashMap<FnId, ProtocolCallTarget>,
    pub struct_schemas: BTreeMap<fz_runtime::module_name::ModuleName, Vec<String>>,
}

impl Module {
    pub fn extern_by_id(&self, eid: ExternId) -> &ExternDecl {
        &self.externs[*self.extern_idx.get(&eid).expect("unknown extern id")]
    }

    pub fn fn_by_id(&self, id: FnId) -> &FnIr {
        &self.fns[*self.fn_idx.get(&id).expect("unknown fn id")]
    }

    pub fn external_call_edges(&self) -> Vec<ExternalCallEdge> {
        let mut out = Vec::new();
        for function in &self.fns {
            for block in &function.blocks {
                match &block.terminator {
                    Term::Call {
                        ident,
                        callee: DirectCallTarget::ProviderBoundary(target),
                        ..
                    }
                    | Term::TailCall {
                        ident,
                        callee: DirectCallTarget::ProviderBoundary(target),
                        ..
                    } => out.push(ExternalCallEdge {
                        callsite: CallsiteId::new(function.id, ident, EmitSlot::Direct),
                        target: target.clone(),
                    }),
                    _ => {}
                }
            }
        }
        out
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
    category: FnCategory,
    owner_module: String,
    ignored_params: HashSet<Var>,
    physical_entry_params: Vec<Var>,
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
        }
    }

    /// fz-f88.5 — set the origin category. Default is `User`.
    pub fn with_category(mut self, category: FnCategory) -> Self {
        self.category = category;
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

    pub fn record_physical_entry_param(&mut self, param: Var) {
        if !self.physical_entry_params.contains(&param) {
            self.physical_entry_params.push(param);
        }
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
        };
        f.dedup_physical_entry_params();
        f
    }
}

pub struct ModuleBuilder {
    module_path: String,
    next_fn: u32,
    fns: Vec<FnIr>,
    fn_idx: HashMap<FnId, usize>,
    schemas: Vec<Schema>,
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
            protocol_call_targets: HashMap::new(),
        }
    }

    pub fn fresh_fn_id(&mut self) -> FnId {
        let id = FnId(self.next_fn);
        self.next_fn += 1;
        id
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
            protocol_call_targets: self.protocol_call_targets,
            struct_schemas: Default::default(),
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
            BinOp::Identical => "===",
            BinOp::NotIdentical => "!==",
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
            Prim::Share(value) => write!(f, "share({value})"),
            Prim::Intrinsic(identity, args) => write!(f, "intrinsic {identity:?}({})", fmt_var_list(args)),
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
            Prim::TupleField(v, i) => write!(f, "tuple_field({}, {})", v, i),
            Prim::StructField(v, name) => write!(f, "struct_field({}, {})", v, name),
            Prim::MakeList(els, tail, retention) => {
                match tail {
                    Some(t) => write!(f, "list([{}] | {})", fmt_var_list(els), t)?,
                    None => write!(f, "list([{}])", fmt_var_list(els))?,
                }
                if let Some(retention) = retention {
                    write!(f, " retain {} {:?}", retention.source, retention.permission)?;
                }
                Ok(())
            }
            Prim::MakeFnRef(_ident, fid) => write!(f, "fn_ref({})", fid),
            Prim::MakeClosure(_ident, fid, captured) => {
                write!(f, "closure({}, captured=[{}])", fid, fmt_var_list(captured))
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
            Prim::RuntimeTypeTest(v, d) => {
                write!(f, "runtime_type_test({}, {})", v, d)
            }
            Prim::ClosureCapture { closure, index } => write!(f, "closure_capture({closure}, {index})"),
        }
    }
}

impl fmt::Display for Cont {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "cont({}, captured=[{}])", self.fn_id, fmt_var_list(&self.captured))
    }
}

impl fmt::Display for DirectCallTarget {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Local(fn_id) => write!(f, "{}", fn_id),
            Self::ProviderBoundary(target) => write!(f, "{}", target),
        }
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
            Term::ReturnLanes(lanes) => write!(f, "return_lanes [{}]", fmt_var_list(lanes)),
            Term::Halt(v) => write!(f, "halt {}", v),
            Term::ReceiveMatched {
                clauses,
                after,
                pinned,
                captures,
                ..
            } => {
                let pin_strs: Vec<String> = pinned
                    .iter()
                    .enumerate()
                    .map(|(i, v)| format!("p{}={}", i, v))
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
            params.sort_by_key(|param| param.0);
            writeln!(f, "  semantic_params=[{}]", fmt_var_list(&self.semantic_entry_params()))?;
            for param in params {
                writeln!(f, "  physical_param {}", param)?;
            }
        }
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
mod fz_ir_test;
