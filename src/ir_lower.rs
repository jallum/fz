//! AST -> fz-IR translator (core).
//!
//! Scope (per fz-ul4.11.16):
//! - Expr: literals, Var, BinOp, UnOp, Block, If, Match, List, Tuple, Call,
//!   Lambda. Multi-clause fn dispatch.
//! - Patterns: Wildcard, Var, literals, Tuple, List, As.
//! - Out of scope (returns LowerError::Unsupported): Case, Cond, With, Map,
//!   MapUpdate, Index, Bitstring expr/pattern, VecLit, Map patterns, Quote/
//!   Unquote at IR translation. These land in fz-ul4.11.17.
//!
//! CPS-split: every non-tail Call closes the current fn with Term::Call and
//! starts a fresh continuation FnIr. The continuation's entry block params
//! are [result_var, ...captured_vars]. Captured = all in-scope locals at the
//! call site (conservative; .11.6 liveness narrows later). Tail-position
//! calls use Term::TailCall.
//!
//! ## Unique-cont invariant (fz-uwq.1)
//!
//! "Fresh continuation per call site" is load-bearing, not just convenient.
//! Every `Cont.fn_id` referenced by a `Term::Call` / `Term::CallClosure` /
//! `Term::Receive` must be unique across the whole module — no two
//! call-shaped terminators may share a continuation fn. The post-type
//! `inline_single_use_conts` pass relies on this to safely inline `K`
//! into its single caller; the fz-uwq epic moves that pass pre-typer,
//! which keeps the same dependency. `debug_assert_unique_conts` at the
//! end of `lower_program_full` pins the invariant down so a regression
//! in this file (or a future corner case) panics in debug rather than
//! corrupting downstream passes.

#![allow(dead_code)]

use crate::ast::{
    BinOp as AstBinOp, BitField as AstBitField, BitSize as AstBitSize, Expr, FnClause, FnDef, Item,
    MatchClause, Pattern, Program, Spanned, UnOp as AstUnOp, WithBinding,
};
use crate::diag::Span;
use crate::fz_ir::{
    BinOp, BitFieldIr, BitSizeIr, BlockId, Const, Cont, ExternDecl, ExternId, ExternTy, FnBuilder,
    FnId, Module, ModuleBuilder, Prim, SourceInfo, Term, UnOp, Var,
};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq)]
pub enum LowerError {
    Unsupported {
        span: Span,
        what: String,
    },
    Unbound {
        span: Span,
        name: String,
    },
    ArityMismatch {
        span: Span,
        name: String,
        expected: usize,
        got: usize,
    },
    PostExpansionNode {
        span: Span,
        what: String,
    },
    /// A back-edge tail call has more than 8 arguments, exceeding the
    /// mid_flight_roots slab limit. Emit a structured diagnostic at the
    /// declaration, not a runtime assert.
    BackEdgeTooManyArgs {
        span: Span,
        fn_name: String,
        callee_name: String,
        arg_count: usize,
    },
    /// fz-axu.24 (M3) — a `Prim::Brand(_, T)` mint reaches the
    /// pre-erasure visibility pass from a fn that doesn't own brand
    /// `T`. `T` is the qualified brand tag; `owner_module` is the
    /// module that declared it; `using_module` is the module path of
    /// the fn doing the mint. v1 only emits Brand prims for the
    /// built-in `utf8` (no owner), so this fires only when user-
    /// declared brands acquire a mint syntax. The plumbing is here.
    BrandMintVisibility {
        span: Span,
        brand: String,
        owner_module: String,
        using_module: String,
    },
}

impl LowerError {
    pub fn to_diagnostic(&self) -> crate::diag::Diagnostic {
        use crate::diag::{Diagnostic, codes};
        match self {
            LowerError::Unsupported { span, what } => Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("unsupported: {}", what),
                *span,
            ),
            LowerError::Unbound { span, name } => {
                Diagnostic::error(codes::LOWER_UNBOUND, format!("unbound: {}", name), *span)
            }
            LowerError::ArityMismatch {
                span,
                name,
                expected,
                got,
            } => Diagnostic::error(
                codes::LOWER_ARITY_MISMATCH,
                format!(
                    "arity mismatch for {}: expected {}, got {}",
                    name, expected, got
                ),
                *span,
            ),
            LowerError::PostExpansionNode { span, what } => Diagnostic::error(
                codes::LOWER_POST_EXPANSION_LEFTOVER,
                format!("post-expansion node leaked: {}", what),
                *span,
            ),
            LowerError::BackEdgeTooManyArgs {
                span,
                fn_name,
                callee_name,
                arg_count,
            } => Diagnostic::error(
                codes::LOWER_BACK_EDGE_TOO_MANY_ARGS,
                format!(
                    "back-edge call from `{}` to `{}` passes {} arguments (max 8 at a yield point)",
                    fn_name, callee_name, arg_count
                ),
                *span,
            ),
            LowerError::BrandMintVisibility {
                span,
                brand,
                owner_module,
                using_module,
            } => Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!(
                    "brand `{}` can only be minted from inside module `{}`; \
                     minted from `{}` here",
                    brand,
                    owner_module,
                    if using_module.is_empty() {
                        "<top-level>"
                    } else {
                        using_module.as_str()
                    },
                ),
                *span,
            ),
        }
    }
}

impl std::fmt::Display for LowerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.to_diagnostic().message)
    }
}

impl std::error::Error for LowerError {}

/// Atom interner: maps atom names to stable u32 ids.
/// Per-CompiledModule atom table built during AST → IR lowering.
///
/// fz-ul4.19.6 policy (atom-table cross-process semantics):
/// - Atom ids are assigned here, per Module. All Processes that run from
///   the same CompiledModule see the same atom ids (atoms are embedded as
///   u32 literals in compiled code; the ids ARE the atoms at runtime).
/// - Two CompiledModules built from different source produce independent
///   atom-id spaces. Cross-module sends (a future feature) would require
///   atom-id translation; not needed for v1.
pub struct AtomTable {
    map: HashMap<String, u32>,
}

impl Default for AtomTable {
    fn default() -> Self {
        Self::new()
    }
}

impl AtomTable {
    /// fz-yan.1 — reserve compile-time atom IDs for `nil`, `true`,
    /// `false`. These three are language keywords that desugar to
    /// atom literals (post-fz-yan); reserving them at construction
    /// time gives every module the same well-known IDs:
    ///
    ///   nil   → atom id 0  → NIL_ATOM_ID   (runtime/codegen NIL_BITS)
    ///   true  → atom id 1  → TRUE_ATOM_ID  (runtime/codegen TRUE_BITS)
    ///   false → atom id 2  → FALSE_ATOM_ID (runtime/codegen FALSE_BITS)
    ///
    /// User-source atoms (and runtime-reserved ones like
    /// `match_error` / `function_clause`) get ids ≥ 3.
    pub fn new() -> Self {
        let mut t = Self {
            map: HashMap::new(),
        };
        // Order matters: nil=0, true=1, false=2.
        let nil = t.intern("nil");
        let tr = t.intern("true");
        let fa = t.intern("false");
        debug_assert_eq!(nil, fz_runtime::fz_value::NIL_ATOM_ID);
        debug_assert_eq!(tr, fz_runtime::fz_value::TRUE_ATOM_ID);
        debug_assert_eq!(fa, fz_runtime::fz_value::FALSE_ATOM_ID);
        t
    }

    pub fn intern(&mut self, name: &str) -> u32 {
        if let Some(&id) = self.map.get(name) {
            return id;
        }
        let id = self.map.len() as u32;
        self.map.insert(name.to_string(), id);
        id
    }

    /// Return atom names in id order: id N -> names[N].
    pub fn names(&self) -> Vec<String> {
        let mut out = vec![String::new(); self.map.len()];
        for (k, &id) in &self.map {
            out[id as usize] = k.clone();
        }
        out
    }
}

/// Name → ExternId index, built during the zeroth lowering pass.
pub struct ExternTable {
    map: HashMap<String, ExternId>,
}

impl ExternTable {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
        }
    }
    fn insert(&mut self, name: String, id: ExternId) {
        self.map.insert(name, id);
    }
    pub fn lookup(&self, name: &str) -> Option<ExternId> {
        self.map.get(name).copied()
    }
}

/// Map a single token identifier to an `ExternTy`. Used when resolving the
/// return-type annotation in an `extern "C" fn` declaration.
/// fz-y3k — split an extern's fz-visible name into the C symbol it resolves
/// to. A `lib::name` prefix is fz-side documentation/namespacing only; the
/// linker sees just the bare suffix. fz-axu — externs declared inside a
/// `defmodule Foo do ... end` get auto-qualified by the resolver to
/// `Foo.name` (with a `.`), which is also fz-side decoration; strip
/// either separator to recover the C symbol. Single-segment names
/// round-trip.
fn extern_symbol_from_name(fz_name: &str) -> &str {
    if let Some((_, sym)) = fz_name.rsplit_once("::") {
        return sym;
    }
    if let Some((_, sym)) = fz_name.rsplit_once('.') {
        return sym;
    }
    fz_name
}

fn extern_ty_from_name(name: &str) -> Option<ExternTy> {
    match name {
        "any" | "atom" | "bool" => Some(ExternTy::Any),
        "integer" => Some(ExternTy::I64),
        "float" => Some(ExternTy::F64),
        "nil" => Some(ExternTy::Unit),
        "never" => Some(ExternTy::Never),
        // fz-0cv — binary marshal classes; one fz binary arg → one
        // `*const u8` C arg. See [[fz-9ss]] for the runtime helpers.
        "binary" => Some(ExternTy::Binary),
        "cstring" => Some(ExternTy::CString),
        _ => None,
    }
}

/// Map of source-fn name -> primary FnId (the entry IR fn for a multi-clause source fn).
type FnMap = HashMap<(String, usize), FnId>;

pub struct LowerCtx {
    pub atoms: AtomTable,
    pub externs: ExternTable,
    /// Accumulated ExternDecls; moved into Module.externs after build.
    pub extern_decls: Vec<ExternDecl>,
    /// Monotonic counter for minting stable ExternIds. Mirrors mb.next_fn.
    next_extern: u32,
    pub mb: ModuleBuilder,
    pub fns: FnMap,
    /// Currently-being-built fn.
    cur: Option<FnBuilder>,
    /// FnId of the fn currently being built. Mirrors `cur` so methods that
    /// record into `source` can key on `(FnId, …)` without unwrapping the
    /// builder.
    cur_fn_id: Option<FnId>,
    /// Currently-active block within `cur`.
    cur_block: Option<BlockId>,
    /// Locals env: source name -> IR Var.
    env: HashMap<String, Var>,
    /// Order of names in env (for stable captured-list building).
    env_order: Vec<String>,
    /// True after an expression sets a terminator on the current block
    /// itself (TailCall, etc.). Caller should NOT overwrite with Return.
    terminated: bool,
    next_temp: u32,
    /// Accumulating side-tables for source positions. Promoted into
    /// `Module.source` at module-build time. Var spans/names indexed
    /// by `(FnId, Var)`; stmt/term spans by their containing block.
    var_meta: HashMap<(FnId, Var), (Span, String)>,
    stmt_spans: HashMap<(FnId, BlockId), Vec<Span>>,
    term_spans: HashMap<(FnId, BlockId), Span>,
    fn_spans: HashMap<FnId, Span>,
    /// fz-ul4.29.9 — synthesized `fz_spawn_thunk(c)` fn; lazily built on
    /// the first `spawn(x)` lowering. Cached so subsequent spawns reuse
    /// the same FnId and produce a single `MakeClosure(thunk, [x])`
    /// shape in stub generation.
    spawn_thunk_id: Option<FnId>,
    /// fz-eol — lazily synthesized top-level fn wrappers around extern
    /// calls, keyed by ExternId. `&libc::close/1` produces a closure
    /// pointing at the wrapper. The wrapper is a true top-level fn (not
    /// a lambda) so it has *zero captures*, which is what
    /// `static_closure_targets` requires for the AOT dtor table.
    /// (Why not desugar to a lambda? The lambda lifter today captures
    /// every in-scope local indiscriminately — see `lower_lambda` —
    /// which would push the closure past the n_caps==0 filter.)
    extern_wrappers: HashMap<ExternId, FnId>,
    /// fz-ext.7 — FnIds below this threshold belong to the runtime.fz
    /// prelude. `build_source_info` ignores their var_meta entries so
    /// prelude spans (relative to runtime.fz bytes) don't overwrite
    /// user-program spans (which share the same per-fn Var numbering).
    pub prelude_fn_id_cutoff: u32,
    /// fz-ty1.3 — Type env built from runtime.fz @type declarations.
    /// Available to downstream passes (e.g. lower_extern_ret_ty) for
    /// resolving opaque type names declared in the prelude.
    pub prelude_type_env: crate::type_expr::ModuleTypeEnv,
    /// fz-ty1.9 — Merged type env: prelude + all user-module @type aliases.
    /// Used by `emit_param_type_guards` to resolve annotation tokens in
    /// `fn f(x :: T)` parameter heads.
    pub combined_type_env: crate::type_expr::ModuleTypeEnv,
    /// fz-jg5.12 (RED.9) — FnIds of user fns that carry an `@spec`. Copied
    /// into `Module.boundary_fns` after build. The reducer treats these as
    /// firewalls so a declared spec is honored as a contract.
    pub boundary_fns: HashSet<crate::fz_ir::FnId>,
    /// fz-fyq.1 — `BranchOrigin` tag for any `Term::If` synthesized in the
    /// current lowering scope. Defaults to `User`; entry points that
    /// initiate generated dispatch (fn-clause selection, pattern-bind,
    /// param guards) save the previous value, set their origin for the
    /// scope, and restore on exit. Matrix helpers and `lower_pattern_bind`
    /// read this when emitting their Ifs.
    pub branch_origin: crate::fz_ir::BranchOrigin,
    /// fz-puj.49 (X1A) — snapshot of user FnDefs by (name, arity) for
    /// AST-level β-reduction in guards. Populated at lower_program entry
    /// before any clause is lowered. Holds clones to avoid threading
    /// `&Program` through every lowering helper. Only fns that satisfy
    /// the "pure callee" shape (single clause, no guard, all-Var params,
    /// pure body — see `is_pure_user_fn_for_guard_inline`) are usable as
    /// inline substitutions; the rest are kept here so the diagnostic
    /// can explain *why* a particular call wasn't inlined.
    pub fn_defs_by_arity: HashMap<(String, usize), FnDef>,
}

impl LowerCtx {
    pub fn new() -> Self {
        Self {
            atoms: AtomTable::default(),
            externs: ExternTable::new(),
            extern_decls: Vec::new(),
            next_extern: 0,
            mb: ModuleBuilder::new(),
            fns: HashMap::new(),
            cur: None,
            cur_fn_id: None,
            cur_block: None,
            env: HashMap::new(),
            env_order: Vec::new(),
            terminated: false,
            next_temp: 0,
            var_meta: HashMap::new(),
            stmt_spans: HashMap::new(),
            term_spans: HashMap::new(),
            fn_spans: HashMap::new(),
            spawn_thunk_id: None,
            extern_wrappers: HashMap::new(),
            prelude_fn_id_cutoff: 0,
            prelude_type_env: crate::type_expr::ModuleTypeEnv::new(),
            combined_type_env: crate::type_expr::ModuleTypeEnv::new(),
            boundary_fns: HashSet::new(),
            branch_origin: crate::fz_ir::BranchOrigin::User,
            fn_defs_by_arity: HashMap::new(),
        }
    }

    /// Helper: emit an If terminator on the current block using the active
    /// `branch_origin`. Lowering paths that synthesize Ifs use this rather
    /// than constructing `Term::If` directly, so origin propagation is
    /// uniform.
    pub fn set_if_term(&mut self, cond: crate::fz_ir::Var, then_b: BlockId, else_b: BlockId) {
        let origin = self.branch_origin;
        self.set_term(crate::fz_ir::Term::If {
            cond,
            then_b,
            else_b,
            origin,
        });
    }

    /// fz-ul4.29.9 — return the FnId of the program-wide `fz_spawn_thunk`,
    /// synthesizing it on first request. Body: a single block taking one
    /// param `c`, terminated by `TailCallClosure(c, [])`. The thunk is
    /// added to the module immediately so downstream passes (typer,
    /// codegen) see it like any other fn.
    ///
    /// Inserted because `Runtime::spawn_closure` invokes the spawn-
    /// target's stub synchronously to materialize an initial frame —
    /// running a native-ABI body there would execute it inside the
    /// parent's quantum (see fz-ul4.29.8's design). The thunk is itself
    /// parking-reachable (TailCallClosure) so it stays uniform-ABI, and
    /// its stub produces a frame for the trampoline to dispatch in the
    /// child's quantum. The wrapped user closure can then take either
    /// the uniform or native path safely.
    fn ensure_spawn_thunk(&mut self) -> FnId {
        if let Some(id) = self.spawn_thunk_id {
            return id;
        }
        let id = self.mb.fresh_fn_id();
        // fz_spawn_thunk is a runtime helper synthesized at lowering time —
        // conceptually part of the prelude, just constructed in Rust rather
        // than parsed from runtime.fz.
        let mut tb = FnBuilder::new(id, "fz_spawn_thunk".to_string())
            .with_category(crate::fz_ir::FnCategory::Prelude);
        let c = tb.fresh_var();
        let entry = tb.block(vec![c]);
        tb.set_terminator(
            entry,
            Term::TailCallClosure {
                ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
                closure: c,
                args: vec![],
            },
        );
        let built = tb.build();
        // Save/restore current builder context: synthesis can happen mid-
        // expression lowering inside another fn.
        self.mb.add_fn(built);
        self.spawn_thunk_id = Some(id);
        id
    }

    /// fz-eol — get-or-build a top-level fn that forwards its args to the
    /// named extern. Used by `&libc::close/1` (and any `&<extern>/<arity>`)
    /// so the resulting closure has a real `FnId` and *zero captures* —
    /// `&name/arity` requires a top-level fn to point at, and only zero-cap
    /// closure targets get static-singleton allocation. The wrapper body
    /// is just `Prim::Extern(eid, params); Return`. See [[fz-9rs]] for the
    /// underlying lifter limitation that prevents the simpler "desugar to
    /// lambda" approach.
    fn ensure_extern_wrapper(&mut self, eid: ExternId) -> FnId {
        if let Some(id) = self.extern_wrappers.get(&eid) {
            return *id;
        }
        let decl = self
            .extern_decls
            .iter()
            .find(|d| d.id == eid)
            .expect("ensure_extern_wrapper: eid not in extern_decls")
            .clone();
        let id = self.mb.fresh_fn_id();
        // Name carries the fz-visible name verbatim (with `::` if any) so
        // dumps render `&libc::close/1` recognisably.
        let name = format!("__extern_wrap__{}", decl.fz_name);
        let mut tb = FnBuilder::new(id, name).with_category(crate::fz_ir::FnCategory::Prelude);
        let params: Vec<Var> = (0..decl.params.len()).map(|_| tb.fresh_var()).collect();
        let entry = tb.block(params.clone());
        let returns_value = !matches!(
            decl.ret,
            crate::fz_ir::ExternTy::Unit | crate::fz_ir::ExternTy::Never
        );
        let ret_var = if returns_value {
            tb.let_(entry, Prim::Extern(eid, params))
        } else {
            let _ = tb.let_(entry, Prim::Extern(eid, params));
            tb.let_(entry, Prim::Const(Const::Nil))
        };
        tb.set_terminator(entry, Term::Return(ret_var));
        self.mb.add_fn(tb.build());
        self.extern_wrappers.insert(eid, id);
        id
    }

    /// Park a temporary in env under a fresh "_tN" name so it survives any
    /// CPS-split triggered by subsequent lowering. After the split, look it
    /// up by the same name to get its rebound continuation-local Var.
    fn park(&mut self, v: Var) -> String {
        let name = format!("_t{}", self.next_temp);
        self.next_temp += 1;
        self.bind(&name, v);
        name
    }

    fn unpark(&self, name: &str) -> Var {
        self.env.get(name).copied().expect("unpark: missing temp")
    }

    fn unbind(&mut self, name: &str) {
        self.env.remove(name);
        if let Some(i) = self.env_order.iter().position(|n| n == name) {
            self.env_order.remove(i);
        }
    }

    fn bind(&mut self, name: &str, v: Var) {
        if !self.env.contains_key(name) {
            self.env_order.push(name.to_string());
        }
        self.env.insert(name.to_string(), v);
    }

    fn lookup(&self, name: &str) -> Option<Var> {
        self.env.get(name).copied()
    }

    fn captured_snapshot(&self) -> Vec<(String, Var)> {
        let mut out = Vec::with_capacity(self.env_order.len());
        for n in &self.env_order {
            if let Some(v) = self.env.get(n) {
                out.push((n.clone(), *v));
            }
        }
        out
    }

    fn cur_mut(&mut self) -> &mut FnBuilder {
        self.cur.as_mut().expect("no current fn")
    }

    fn cur_block(&self) -> BlockId {
        self.cur_block.expect("no current block")
    }

    fn let_(&mut self, prim: Prim) -> Var {
        self.let_at(prim, Span::DUMMY)
    }

    /// Emit `let v = prim` and record the source span the prim came from.
    /// The resulting Var's metadata defaults to `(span, "")` — anonymous
    /// temp. Callers that bind the Var to a source name follow up with
    /// `name_var(v, name, name_span)`.
    fn let_at(&mut self, mut prim: Prim, span: Span) -> Var {
        // fz-rrh — same pattern as set_term_at: hoist the source span
        // into the prim's intrinsic ident (only `Prim::MakeClosure`
        // is a callsite; other prims are no-op).
        prim.set_source_span(span);
        let blk = self.cur_block();
        let fn_id = self.cur_fn_id.expect("no current fn");
        let v = self.cur_mut().let_(blk, prim);
        // Var defaults: capture span; name follow-up via name_var.
        self.var_meta.insert((fn_id, v), (span, String::new()));
        // Append stmt span aligned with the block's stmt index.
        self.stmt_spans.entry((fn_id, blk)).or_default().push(span);
        v
    }

    /// Attach a source name to an existing IR Var. Used when a pattern
    /// binds a name — the Var existed before (came from a param or a
    /// projection prim); we record the name + the pattern's span as
    /// the var's defining-site info.
    fn name_var(&mut self, v: Var, name: &str, span: Span) {
        let fn_id = self.cur_fn_id.expect("no current fn");
        let entry = self
            .var_meta
            .entry((fn_id, v))
            .or_insert((Span::DUMMY, String::new()));
        if entry.0.is_dummy() {
            entry.0 = span;
        }
        if entry.1.is_empty() {
            entry.1 = name.to_string();
        }
    }

    fn set_term(&mut self, term: Term) {
        self.set_term_at(term, Span::DUMMY);
    }

    fn set_term_at(&mut self, mut term: Term, span: Span) {
        // fz-rrh — hoist the source span into the term's intrinsic
        // CallsiteIdent. Most ir_lower constructions used DUMMY at the
        // struct-literal site because the span isn't typed-in scope at
        // every Term::* literal; setting it here means every
        // set_term_at caller gets pristine spans on the ident for
        // free. No-op when span is DUMMY (synthetic).
        term.set_source_span(span);
        let blk = self.cur_block();
        let fn_id = self.cur_fn_id.expect("no current fn");
        self.cur_mut().set_terminator(blk, term);
        if !span.is_dummy() {
            self.term_spans.insert((fn_id, blk), span);
        }
    }
}

impl Default for LowerCtx {
    fn default() -> Self {
        Self::new()
    }
}

const RUNTIME_FZ: &str = include_str!("runtime.fz");

/// fz-axu.27 (M6) — return the prelude as a flat `Program` whose
/// `module_type_envs[""]`, `opaque_inners`, and `brand_inners` are all
/// populated. `flatten_modules` only walks `defmodule`-nested
/// declarations, so root-scope `@type` aliases (like `@type utf8 ::
/// refines binary` at the top of runtime.fz) are harvested separately
/// from attrs and merged into the flat program.
fn parse_runtime_prelude<T: crate::types::Types<Ty = crate::types::Ty>>(t: &mut T) -> Program {
    let toks = crate::lexer::Lexer::new(RUNTIME_FZ)
        .tokenize()
        .expect("runtime.fz lex error (bug in built-in prelude)");
    let (items, attrs) = crate::parser::Parser::new(toks)
        .parse_prelude()
        .expect("runtime.fz parse error (bug in built-in prelude)");
    let (root_env, root_o_inners, root_b_inners) =
        crate::type_expr::build_module_type_env_for(t, &attrs, "")
            .expect("runtime.fz @type error (bug in built-in prelude)");
    let staged = crate::ast::Program {
        items,
        module_docs: Default::default(),
        module_type_envs: Default::default(),
        opaque_inners: Default::default(),
        brand_inners: Default::default(),
    };
    let mut flat = crate::resolve::flatten_modules(t, staged)
        .expect("runtime.fz module flatten error (bug in built-in prelude)");
    // Merge root-scope aliases into the flattened program.
    flat.module_type_envs
        .entry(String::new())
        .or_default()
        .extend(root_env);
    flat.opaque_inners.extend(root_o_inners);
    flat.brand_inners.extend(root_b_inners);
    flat
}

pub fn lower_program<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    prog: &Program,
) -> Result<Module, LowerError> {
    let (m, _) = lower_program_full(t, prog)?;
    Ok(m)
}

pub fn lower_program_full<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    prog: &Program,
) -> Result<(Module, AtomTable), LowerError> {
    let mut ctx = LowerCtx::new();

    // Prepend the built-in runtime.fz prelude so its externs and wrapper fns
    // are visible to every user program without an explicit import.
    let prelude = parse_runtime_prelude(t);
    let prelude_type_env = prelude
        .module_type_envs
        .get("")
        .cloned()
        .unwrap_or_default();
    ctx.prelude_type_env = prelude_type_env.clone();
    // Build the combined type env: prelude aliases + all user-module aliases.
    let mut combined = prelude_type_env;
    for module_env in prog.module_type_envs.values() {
        combined.extend(module_env.iter().map(|(k, v)| (k.clone(), v.clone())));
    }
    ctx.combined_type_env = combined;
    let runtime_item_count = prelude.items.len();
    let all_items: Vec<Rc<Item>> = prelude
        .items
        .iter()
        .cloned()
        .chain(prog.items.iter().cloned())
        .collect();

    // Snapshot user FnDefs (non-extern, non-prelude) by (name, arity) for
    // guard helpers. Receive guards lower helper calls through Matcher
    // dispatch; non-receive dispatch still uses the legacy AST inliner until
    // the general matcher fallback is removed.
    for item in all_items.iter().skip(runtime_item_count) {
        if let Item::Fn(fn_def) = item.as_ref()
            && fn_def.extern_abi.is_none()
        {
            let arity = fn_def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
            ctx.fn_defs_by_arity
                .entry((fn_def.name.clone(), arity))
                .or_insert_with(|| fn_def.clone());
        }
    }

    // Registration pass: assign ExternIds and FnIds in a single sweep.
    // Prelude items come first; recording prelude_fn_id_cutoff after them
    // lets build_source_info ignore prelude var spans (both halves restart
    // Var numbering at 0, so user spans must not be overwritten).
    for item in all_items.iter().take(runtime_item_count) {
        if let Item::Fn(fn_def) = item.as_ref() {
            if fn_def.extern_abi.is_some() {
                let eid = ExternId(ctx.next_extern);
                ctx.next_extern += 1;
                let params: Vec<ExternTy> = fn_def
                    .extern_params
                    .iter()
                    .map(|name| extern_ty_from_name(name).unwrap_or(ExternTy::Any))
                    .collect();
                let (ret, ret_descr) = lower_extern_ret_ty(t, fn_def, &ctx.prelude_type_env)?;
                ctx.extern_decls.push(ExternDecl {
                    id: eid,
                    fz_name: fn_def.name.clone(),
                    symbol: extern_symbol_from_name(&fn_def.name).to_string(),
                    params,
                    ret,
                    ret_descr,
                });
                ctx.externs.insert(fn_def.name.clone(), eid);
            } else {
                let arity = fn_def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
                let id = ctx.mb.fresh_fn_id();
                ctx.fns.insert((fn_def.name.clone(), arity), id);
            }
        }
    }
    // fz-qbg.2 — Lower prelude bodies *before* registering user FnIds.
    // Prelude lowering may mint continuation fns (multi-clause prelude
    // fns like `print` and `vec_get` now route each clause through a
    // body cont fn). Doing user registration AFTER prelude body lowering
    // keeps user FnIds contiguous and all >= prelude_fn_id_cutoff —
    // so `build_source_info` correctly excludes every prelude-origin
    // FnId (source plus minted conts) from the user var-meta table.
    for item in all_items.iter().take(runtime_item_count) {
        if let Item::Fn(fn_def) = item.as_ref()
            && fn_def.extern_abi.is_none()
        {
            lower_fn(&mut ctx, t, fn_def, crate::fz_ir::FnCategory::Prelude)?;
        }
    }
    ctx.prelude_fn_id_cutoff = ctx.mb.next_fn_id();

    for item in all_items.iter().skip(runtime_item_count) {
        match item.as_ref() {
            Item::Fn(fn_def) => {
                if fn_def.extern_abi.is_some() {
                    let eid = ExternId(ctx.next_extern);
                    ctx.next_extern += 1;
                    let params: Vec<ExternTy> = fn_def
                        .extern_params
                        .iter()
                        .map(|name| extern_ty_from_name(name).unwrap_or(ExternTy::Any))
                        .collect();
                    let (ret, ret_descr) = lower_extern_ret_ty(t, fn_def, &ctx.prelude_type_env)?;
                    ctx.extern_decls.push(ExternDecl {
                        id: eid,
                        fz_name: fn_def.name.clone(),
                        symbol: extern_symbol_from_name(&fn_def.name).to_string(),
                        params,
                        ret,
                        ret_descr,
                    });
                    ctx.externs.insert(fn_def.name.clone(), eid);
                } else {
                    let arity = fn_def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
                    let id = ctx.mb.fresh_fn_id();
                    ctx.fns.insert((fn_def.name.clone(), arity), id);
                    // fz-jg5.12 (RED.9): a user fn with an @spec is a
                    // reduction boundary — the spec is a signed contract.
                    if fn_def
                        .attrs
                        .iter()
                        .any(|a| matches!(a, crate::ast::Attribute::Spec(_)))
                    {
                        ctx.boundary_fns.insert(id);
                    }
                }
            }
            Item::Module(m) => {
                return Err(LowerError::Unsupported {
                    span: m.span,
                    what: "Item::Module should be flattened by resolve before lowering".into(),
                });
            }
            Item::Alias { span, .. } | Item::Import { span, .. } => {
                return Err(LowerError::Unsupported {
                    span: *span,
                    what: "alias/import should be consumed by resolve before lowering".into(),
                });
            }
            Item::MacroCall { name, span, .. } => {
                return Err(LowerError::PostExpansionNode {
                    span: *span,
                    what: format!("MacroCall({})", name),
                });
            }
        }
    }

    // Second pass: lower user fn bodies. (Prelude bodies were already
    // lowered above, before user FnId registration — see the fz-qbg.2
    // note for why.)
    for item in all_items.iter().skip(runtime_item_count) {
        if let Item::Fn(fn_def) = item.as_ref()
            && fn_def.extern_abi.is_none()
        {
            lower_fn(&mut ctx, t, fn_def, crate::fz_ir::FnCategory::User)?;
        }
    }

    // Take the module out first; `ctx.mb` is moved but `ctx` itself is
    // still usable for source-info collection.
    let mb = std::mem::take(&mut ctx.mb);
    let mut module = mb.build();
    module.source = build_source_info(&module, &ctx);
    module.atom_names = ctx.atoms.names();
    module.externs = std::mem::take(&mut ctx.extern_decls);
    for (i, e) in module.externs.iter().enumerate() {
        module.extern_idx.insert(e.id, i);
    }
    module.boundary_fns = std::mem::take(&mut ctx.boundary_fns);
    // fz-swt.8 — carry the resolver's opaque-inner-type map onto the
    // Module so the typer can resolve `handle.value` accesses to T.
    // fz-axu.27 (M6) — prelude inners (utf8 brand, pid opaque, ...) live
    // in the flat-prelude Program, merged here alongside user inners.
    module.opaque_inners = prog.opaque_inners.clone();
    module.opaque_inners.extend(prelude.opaque_inners.clone());
    module.brand_inners = prog.brand_inners.clone();
    module.brand_inners.extend(prelude.brand_inners.clone());
    // fz-02r.4 — annotate TailCall back-edges from the structural SCC.
    annotate_back_edges(&mut module, &ctx.fn_spans)?;
    // fz-axu.24 (M3) — brand-mint visibility. Must run before erasure
    // because erasure drops the Brand prims this pass needs to see.
    // Built-in brands (utf8, ...) have no module owner and pass
    // trivially; the gate fires when user-declared brands acquire a
    // mint syntax and a foreign module tries to use it.
    check_brand_visibility(t, &module, &ctx.stmt_spans, &ctx.fn_spans)?;
    // fz-axu.23 (M2) — brand erasure is the final lowering phase. The
    // Module returned from lower_program_full has the invariant: no
    // Prim::Brand survives in any FnIr. Downstream passes (typer,
    // reducer, codegen, interp, DCE) can treat that as a precondition,
    // and their Brand match arms become `unreachable!()` rather than
    // silent identity-fallbacks.
    crate::ir_brand_erase::erase_brands(&mut module);
    // fz-uwq.1 — verify the unique-cont invariant the post-type pipeline
    // depends on. See `debug_assert_unique_conts` for the contract.
    debug_assert_unique_conts(&module);
    Ok((module, ctx.atoms))
}

/// fz-uwq.1 — verify the **unique-cont invariant**: every `Cont.fn_id`
/// referenced by a `Term::Call` / `Term::CallClosure` / `Term::Receive`
/// appears as the continuation of **exactly one** such terminator across
/// the whole module.
///
/// ## Why this is load-bearing
///
/// `ir_codegen::compile` runs `inline_single_use_conts` before codegen,
/// and the fz-uwq epic moves that pass to run **pre-typer**. The pass
/// is safe to inline a continuation fn `K` into its caller only when `K`
/// is referenced exactly once as a continuation — otherwise inlining
/// would either duplicate `K`'s body across two call sites (losing
/// sharing the source author may rely on) or leave a dangling reference.
///
/// The lowerer guarantees uniqueness structurally: `lower_expr` and
/// friends mint a **fresh** continuation FnIr for each non-tail call
/// they CPS-split. No path in `ir_lower` produces two terminators that
/// share the same `Cont.fn_id`. This assertion pins the structural
/// guarantee down so a future change to the lowerer (or a corner case
/// not yet exercised) cannot silently break the downstream pipeline.
///
/// See `docs/dispatch-as-typer-output.md` (Worry 1) for the stress-test
/// that named this invariant.
///
/// Debug-build only — the check is O(blocks) but redundant in release
/// when the lowerer is correct. If it ever fires in debug, the lowerer
/// is wrong (or a new corner case needs the invariant documented away).
/// fz-axu.24 (M3) — brand-mint visibility pass. Walks every Prim::Brand
/// stmt in every fn and applies `check_brand_mint_visibility`, using
/// the containing fn's name to derive the using_module (everything
/// before the final `.` in the qualified fn name; "" for top-level
/// fns). Built-in brands like `utf8` carry no `::` qualifier and pass
/// trivially.
///
/// Runs between annotate_back_edges and erase_brands — must see Brand
/// prims, which erase_brands removes.
fn check_brand_visibility<T: crate::types::Types>(
    _t: &mut T,
    module: &Module,
    stmt_spans: &HashMap<(FnId, BlockId), Vec<Span>>,
    fn_spans: &HashMap<FnId, Span>,
) -> Result<(), LowerError> {
    for f in &module.fns {
        let using_module = f.name.rfind('.').map(|i| &f.name[..i]).unwrap_or("");
        for block in &f.blocks {
            let spans = stmt_spans.get(&(f.id, block.id));
            for (i, stmt) in block.stmts.iter().enumerate() {
                let crate::fz_ir::Stmt::Let(_, prim) = stmt;
                if let crate::fz_ir::Prim::Brand(_, brand_tag) = prim
                    && let Err(e) =
                        crate::types::check_brand_mint_visibility(brand_tag, using_module)
                {
                    let span = spans
                        .and_then(|v| v.get(i).copied())
                        .or_else(|| fn_spans.get(&f.id).copied())
                        .unwrap_or(crate::diag::Span::DUMMY);
                    return Err(LowerError::BrandMintVisibility {
                        span,
                        brand: e.opaque,
                        owner_module: e.owner_module,
                        using_module: e.using_module,
                    });
                }
            }
        }
    }
    Ok(())
}

fn debug_assert_unique_conts(module: &Module) {
    if !cfg!(debug_assertions) {
        return;
    }
    use crate::fz_ir::FnId;
    let mut seen: HashMap<FnId, (FnId, BlockId)> = HashMap::new();
    for f in &module.fns {
        for b in &f.blocks {
            let cont_fn = match &b.terminator {
                Term::Call { continuation, .. }
                | Term::CallClosure { continuation, .. }
                | Term::Receive {
                    continuation,
                    ident: _,
                } => continuation.fn_id,
                _ => continue,
            };
            if let Some(prev) = seen.insert(cont_fn, (f.id, b.id)) {
                panic!(
                    "fz-uwq.1 invariant violated: cont fn {:?} referenced by two terminators: \
                     {:?}:{:?} and {:?}:{:?}. The lowerer must mint a fresh continuation \
                     FnIr per call site; sharing breaks inline_single_use_conts.",
                    cont_fn, prev.0, prev.1, f.id, b.id
                );
            }
        }
    }
}

/// Parse `extern_ret_tokens` into an ExternTy (wire format) and semantic type
/// (semantic type for the type system).
///
/// `type_env` is consulted for named type references (e.g. `pid`).
fn lower_extern_ret_ty<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    fn_def: &FnDef,
    type_env: &crate::type_expr::ModuleTypeEnv,
) -> Result<(ExternTy, crate::types::Ty), LowerError> {
    use crate::lexer::Tok;
    let tokens = &fn_def.extern_ret_tokens.0;

    // Try to resolve via parse_type_expr first (handles named types like `pid`).
    if !tokens.is_empty()
        && let Ok((ty, _)) = crate::type_expr::parse_type_expr(t, tokens, type_env)
    {
        let wire = ty_to_extern_ty(t, &ty);
        return Ok((wire, ty));
    }

    // Fallback: first-meaningful-token heuristic for tokens that don't
    // parse as a full type expression (e.g. bare `unit` which is not a
    // built-in fz type name).
    let ty = tokens.iter().find_map(|t| match &t.tok {
        Tok::Nil => Some(ExternTy::Unit),
        Tok::True | Tok::False => Some(ExternTy::Any),
        Tok::Ident(n) | Tok::Upper(n) => extern_ty_from_name(n.as_str()),
        _ => None,
    });
    ty.map(|wire| (wire, t.any()))
        .ok_or_else(|| LowerError::Unsupported {
            span: fn_def.name_span,
            what: format!(
                "unrecognised return type in `extern fn {}` (expected any/nil/never/float/pid/…)",
                fn_def.name
            ),
        })
}

/// Derive a coarse C-ABI wire type from a semantic Ty.
///
/// Opaque types erase to Any (they are fz tagged values at runtime).
/// Float-only types get the F64 wire. Nil-only → Unit. Never → Never.
/// Everything else → Any (opaque u64 fz value).
fn ty_to_extern_ty<T: crate::types::Types>(t: &mut T, d: &T::Ty) -> ExternTy {
    if t.is_empty(d) {
        return ExternTy::Never;
    }
    if t.is_nil(d) {
        return ExternTy::Unit;
    }
    if t.is_floating(d) {
        return ExternTy::F64;
    }
    if t.is_integer(d) {
        return ExternTy::I64;
    }
    ExternTy::Any
}

fn concrete_any_tuple(arity: usize) -> crate::types::Ty {
    use crate::types::Types;

    let mut t = crate::types::ConcreteTypes;
    let elems: Vec<crate::types::Ty> = (0..arity).map(|_| t.any()).collect();
    t.tuple(&elems)
}

fn concrete_any_map() -> crate::types::Ty {
    use crate::types::Types;

    let mut t = crate::types::ConcreteTypes;
    t.map_top()
}

/// Post-lowering pass: compute the SCC of the fn-level call graph and set
/// `is_back_edge` on every `Term::TailCall` whose callee is in the same SCC
/// as the caller (i.e., the call is on a loop back-edge). Also emits
/// `LowerError::BackEdgeTooManyArgs` when a back-edge tail call passes >8 args.
fn annotate_back_edges(
    module: &mut Module,
    fn_spans: &HashMap<FnId, crate::diag::Span>,
) -> Result<(), LowerError> {
    use std::collections::{HashMap as HM, HashSet};

    // Build call graph: FnId → set of FnIds it tail-calls.
    let mut graph: HM<FnId, HashSet<FnId>> = HM::new();
    for f in &module.fns {
        let entry = graph.entry(f.id).or_default();
        for block in &f.blocks {
            if let Term::TailCall { callee, .. } = &block.terminator {
                entry.insert(*callee);
            }
        }
    }

    // Tarjan SCC on the call graph.
    let scc_of = {
        let mut index_counter = 0usize;
        let mut stack: Vec<FnId> = Vec::new();
        let mut on_stack: HashSet<FnId> = HashSet::new();
        let mut index: HM<FnId, usize> = HM::new();
        let mut lowlink: HM<FnId, usize> = HM::new();
        let mut scc_of: HM<FnId, usize> = HM::new();
        let mut scc_count = 0usize;
        let all_fns: Vec<FnId> = module.fns.iter().map(|f| f.id).collect();

        fn strongconnect(
            v: FnId,
            graph: &HM<FnId, HashSet<FnId>>,
            index_counter: &mut usize,
            stack: &mut Vec<FnId>,
            on_stack: &mut HashSet<FnId>,
            index: &mut HM<FnId, usize>,
            lowlink: &mut HM<FnId, usize>,
            scc_of: &mut HM<FnId, usize>,
            scc_count: &mut usize,
        ) {
            let v_index = *index_counter;
            index.insert(v, v_index);
            lowlink.insert(v, v_index);
            *index_counter += 1;
            stack.push(v);
            on_stack.insert(v);

            if let Some(neighbors) = graph.get(&v) {
                let neighbors: Vec<FnId> = neighbors.iter().copied().collect();
                for w in neighbors {
                    if !index.contains_key(&w) {
                        strongconnect(
                            w,
                            graph,
                            index_counter,
                            stack,
                            on_stack,
                            index,
                            lowlink,
                            scc_of,
                            scc_count,
                        );
                        let w_ll = lowlink[&w];
                        let v_ll = lowlink.get_mut(&v).unwrap();
                        if w_ll < *v_ll {
                            *v_ll = w_ll;
                        }
                    } else if on_stack.contains(&w) {
                        let w_idx = index[&w];
                        let v_ll = lowlink.get_mut(&v).unwrap();
                        if w_idx < *v_ll {
                            *v_ll = w_idx;
                        }
                    }
                }
            }

            if lowlink[&v] == index[&v] {
                let scc_id = *scc_count;
                *scc_count += 1;
                loop {
                    let w = stack.pop().unwrap();
                    on_stack.remove(&w);
                    scc_of.insert(w, scc_id);
                    if w == v {
                        break;
                    }
                }
            }
        }

        for fid in &all_fns {
            if !index.contains_key(fid) {
                strongconnect(
                    *fid,
                    &graph,
                    &mut index_counter,
                    &mut stack,
                    &mut on_stack,
                    &mut index,
                    &mut lowlink,
                    &mut scc_of,
                    &mut scc_count,
                );
            }
        }
        scc_of
    };

    // Annotate each TailCall. Build a map from FnId to fn name for error messages.
    let fn_name_of: HM<FnId, String> = module.fns.iter().map(|f| (f.id, f.name.clone())).collect();

    for f in &mut module.fns {
        let caller_scc = scc_of.get(&f.id).copied().unwrap_or(usize::MAX);
        let caller_name = fn_name_of.get(&f.id).cloned().unwrap_or_default();
        let caller_span = fn_spans
            .get(&f.id)
            .copied()
            .unwrap_or(crate::diag::Span::DUMMY);
        for block in &mut f.blocks {
            if let Term::TailCall {
                ident: _,
                callee,
                args,
                is_back_edge,
            } = &mut block.terminator
            {
                let callee_scc = scc_of.get(callee).copied().unwrap_or(usize::MAX);
                if callee_scc == caller_scc {
                    *is_back_edge = true;
                    if args.len() > 8 {
                        let callee_name = fn_name_of.get(callee).cloned().unwrap_or_default();
                        return Err(LowerError::BackEdgeTooManyArgs {
                            span: caller_span,
                            fn_name: caller_name.clone(),
                            callee_name,
                            arg_count: args.len(),
                        });
                    }
                }
            }
        }
    }
    Ok(())
}

/// Collect the per-fn metadata accumulated on `ctx` into `Module.source`.
/// Var spans/names indexed by Var.0; per-block stmt/term spans flow through
/// unchanged; per-fn spans indexed by FnId.0.
fn build_source_info(module: &Module, ctx: &LowerCtx) -> SourceInfo {
    let max_fn_id = module.fns.iter().map(|f| f.id.0).max().unwrap_or(0);
    let mut fn_span = vec![Span::DUMMY; (max_fn_id as usize) + 1];
    for (fid, sp) in &ctx.fn_spans {
        let idx = fid.0 as usize;
        if idx < fn_span.len() {
            fn_span[idx] = *sp;
        }
    }
    // Var spans/names: pick the maximum Var across user-program fns only.
    // Each fn's Vars restart at 0, so we maintain one global table indexed
    // by Var.0. Prelude fns (FnId < prelude_fn_id_cutoff) are excluded:
    // their spans are byte offsets into runtime.fz, not the user source,
    // and would overwrite user-program entries that share the same Var.0.
    let cutoff = ctx.prelude_fn_id_cutoff;
    let max_var = ctx
        .var_meta
        .keys()
        .filter(|(fid, _)| fid.0 >= cutoff)
        .map(|(_, v)| v.0)
        .max()
        .unwrap_or(0);
    let n = (max_var as usize) + 1;
    let mut var_span = vec![Span::DUMMY; n];
    let mut var_name = vec![String::new(); n];
    for ((fid, v), (sp, name)) in &ctx.var_meta {
        if fid.0 < cutoff {
            continue; // skip prelude fn metadata
        }
        let idx = v.0 as usize;
        if idx < n {
            if var_span[idx].is_dummy() {
                var_span[idx] = *sp;
            }
            if var_name[idx].is_empty() {
                var_name[idx] = name.clone();
            }
        }
    }
    SourceInfo {
        var_span,
        var_name,
        stmt_spans: ctx.stmt_spans.clone(),
        term_span: ctx.term_spans.clone(),
        fn_span,
    }
}

fn lower_fn<T: crate::types::Types<Ty = crate::types::Ty>>(
    ctx: &mut LowerCtx,
    t: &mut T,
    fn_def: &FnDef,
    category: crate::fz_ir::FnCategory,
) -> Result<(), LowerError> {
    if fn_def.is_macro {
        // Macros are consumed by expansion before lowering.
        return Ok(());
    }
    let arity = fn_def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
    let fn_id = *ctx
        .fns
        .get(&(fn_def.name.clone(), arity))
        .ok_or_else(|| LowerError::Unbound {
            span: fn_def.name_span,
            name: format!("fn {}/{}", fn_def.name, arity),
        })?;

    let mut builder = FnBuilder::new(fn_id, fn_def.name.clone()).with_category(category);
    // Mint param vars for the entry block.
    let param_vars: Vec<Var> = (0..arity).map(|_| builder.fresh_var()).collect();
    let entry = builder.block(param_vars.clone());
    ctx.cur = Some(builder);
    ctx.cur_fn_id = Some(fn_id);
    ctx.fn_spans.insert(fn_id, fn_def.span);
    ctx.cur_block = Some(entry);
    ctx.env.clear();
    ctx.env_order.clear();

    // Pre-record param var metadata. The pattern walker overwrites with
    // the pattern's binding-site info if the pattern is `Var(n)`; here we
    // default to the clause's first param-pattern span so even
    // wildcard / tuple-destructured params have *some* source position.
    for (i, pv) in param_vars.iter().enumerate() {
        let pat_span = fn_def
            .clauses
            .first()
            .and_then(|c| c.params.get(i))
            .map(|p| p.span)
            .unwrap_or(Span::DUMMY);
        ctx.var_meta.insert((fn_id, *pv), (pat_span, String::new()));
    }

    ctx.terminated = false;
    if fn_def.clauses.len() == 1 {
        let clause = &fn_def.clauses[0];
        // Bind params via patterns; on fail, halt with :match_error.
        // Seal fail_block FIRST so CPS-split during body lowering can't orphan it.
        let fail_block = ctx.cur_mut().block(vec![]);
        ctx.cur_block = Some(fail_block);
        let me = ctx.atoms.intern("match_error");
        let mev = ctx.let_(Prim::Const(Const::Atom(me)));
        ctx.set_term(Term::Halt(mev));
        ctx.cur_block = Some(entry);

        let prev_origin = ctx.branch_origin;
        ctx.branch_origin = crate::fz_ir::BranchOrigin::ClauseDispatch;
        for (pv, pat) in param_vars.iter().zip(&clause.params) {
            lower_pattern_bind(ctx, *pv, pat, fail_block)?;
            // Record the pattern's span on the param Var if not yet named
            // by the pattern walker (e.g. tuple-destructured params).
            ctx.name_var(*pv, "", pat.span);
        }
        ctx.branch_origin = crate::fz_ir::BranchOrigin::ParamGuard;
        emit_param_type_guards(ctx, t, clause, &param_vars, fail_block)?;
        ctx.branch_origin = crate::fz_ir::BranchOrigin::ClauseDispatch;
        if let Some(g) = &clause.guard {
            let guard_var = lower_expr(ctx, g, false)?;
            let body_b = ctx.cur_mut().block(vec![]);
            ctx.set_if_term(guard_var, body_b, fail_block);
            ctx.cur_block = Some(body_b);
            ctx.terminated = false;
        }
        ctx.branch_origin = prev_origin;
        let result = lower_expr(ctx, &clause.body, /* is_tail */ true)?;
        if !ctx.terminated {
            ctx.set_term(Term::Return(result));
        }
    } else {
        lower_multi_clause(ctx, t, fn_def, &param_vars, entry)?;
    }

    let built = ctx.cur.take().unwrap().build();
    ctx.mb.add_fn(built);
    ctx.cur_block = None;
    Ok(())
}

/// fz-ty1.9 — Emit TypeTest guards for `fn f(x :: T)` parameter annotations.
/// For each param that has a type annotation, emit a `TypeTest(pv, descr)`
/// stmt and branch: pass → continue to next block, fail → `on_fail` block.
fn emit_param_type_guards<T: crate::types::Types<Ty = crate::types::Ty>>(
    ctx: &mut LowerCtx,
    t: &mut T,
    clause: &FnClause,
    param_vars: &[Var],
    on_fail: BlockId,
) -> Result<(), LowerError> {
    debug_assert_eq!(
        param_vars.len(),
        clause.param_annotations.len(),
        "param/annotation length mismatch"
    );
    for (pv, type_toks_opt) in param_vars.iter().zip(&clause.param_annotations) {
        let toks = match type_toks_opt {
            Some(tt) => &tt.0,
            None => continue,
        };
        let ty = match crate::type_expr::parse_type_expr(t, toks, &ctx.combined_type_env) {
            Ok((ty, _)) => ty,
            Err(_) => continue,
        };
        let tt_var = ctx.let_(crate::fz_ir::Prim::TypeTest(*pv, Box::new(ty)));
        let pass_b = ctx.cur_mut().block(vec![]);
        ctx.set_if_term(tt_var, pass_b, on_fail);
        ctx.cur_block = Some(pass_b);
        ctx.terminated = false;
    }
    Ok(())
}

/// fz-qbg.2 — detect whether a clause body's lowering would CPS-split.
/// A body lowered at `is_tail=true` cps-splits iff it contains a `Receive`
/// call OR a `Call` in non-tail position (i.e., as an argument / operand
/// to something else). Bodies that are "safe" stay block-inline; only
/// CPS-splitting bodies pay for a per-clause continuation fn.
fn body_might_cps_split(body: &Spanned<Expr>) -> bool {
    fn is_receive_call(e: &Spanned<Expr>) -> bool {
        if let Expr::Call(target, _) = &e.node
            && let Expr::Var(name) = &target.node
        {
            return name == "receive";
        }
        false
    }
    // walk(e, in_tail): true ⇒ this subexpression's lowering would
    // cps_split somewhere.
    fn walk(e: &Spanned<Expr>, in_tail: bool) -> bool {
        // receive() always cps-splits, regardless of position.
        if is_receive_call(e) {
            return true;
        }
        match &e.node {
            // Leaves never cps-split.
            Expr::Int(_)
            | Expr::Float(_)
            | Expr::Binary(_)
            | Expr::Atom(_)
            | Expr::Bool(_)
            | Expr::Nil
            | Expr::Var(_)
            | Expr::FnRef { .. }
            | Expr::Lambda(_, _)
            | Expr::Quote(_)
            | Expr::Unquote(_) => false,
            // Calls: at tail, the top-level call becomes a TailCall (no
            // cps-split). Non-tail Calls cps-split. Args + target are
            // always non-tail.
            Expr::Call(target, args) => {
                if !in_tail {
                    return true;
                }
                walk(target, false) || args.iter().any(|a| walk(a, false))
            }
            // Operators and projections: operands are always non-tail.
            Expr::BinOp(_, l, r) => walk(l, false) || walk(r, false),
            Expr::UnOp(_, inner) => walk(inner, false),
            Expr::Index(m, k) => walk(m, false) || walk(k, false),
            // Control flow: cond/subject non-tail; arms inherit parent's tail.
            Expr::If(cond, then_e, else_opt) => {
                walk(cond, false)
                    || walk(then_e, in_tail)
                    || else_opt.as_ref().is_some_and(|e| walk(e, in_tail))
            }
            Expr::Case(subject, clauses) => {
                subject.as_ref().is_some_and(|subject| walk(subject, false))
                    || clauses.iter().any(|c| {
                        c.guard.as_ref().is_some_and(|g| walk(g, false)) || walk(&c.body, in_tail)
                    })
            }
            // fz-5vj — `receive do … end` always cps-splits (the park
            // itself is an escape point per docs/receive-matched.md §4).
            Expr::Receive { .. } => true,
            Expr::Cond(arms) => arms
                .iter()
                .any(|(test, body)| walk(test, false) || walk(body, in_tail)),
            // `with` has CPS-split potential in any binding expr; play
            // conservative.
            Expr::With(_, _, _) => true,
            // Block: last expr inherits tail, others are non-tail.
            Expr::Block(exprs) => {
                let last_idx = exprs.len().saturating_sub(1);
                exprs
                    .iter()
                    .enumerate()
                    .any(|(i, e)| walk(e, in_tail && i == last_idx))
            }
            Expr::Match(_, e) => walk(e, false),
            // Collections: every element is non-tail.
            Expr::List(elems, tail) => {
                elems.iter().any(|e| walk(e, false))
                    || tail.as_ref().is_some_and(|t| walk(t, false))
            }
            Expr::Tuple(elems) | Expr::VecLit(_, elems) => elems.iter().any(|e| walk(e, false)),
            Expr::Map(entries) => entries
                .iter()
                .any(|(k, v)| walk(k, false) || walk(v, false)),
            Expr::MapUpdate(base, entries) => {
                walk(base, false)
                    || entries
                        .iter()
                        .any(|(k, v)| walk(k, false) || walk(v, false))
            }
            Expr::Bitstring(fields) => fields.iter().any(|f| walk(&f.value, false)),
        }
    }
    walk(body, /* in_tail */ true)
}

// fz-ul4.43.D.1 — Pattern matrix lowering (re-applied for diagnostic).
use crate::pattern_matrix::{BodyId, Matrix, Row};

type BodyCb<'a> = &'a mut dyn FnMut(
    &mut LowerCtx,
    BodyId,
    Vec<(String, Var)>,
    Vec<(Var, crate::types::Ty)>,
    Option<crate::ast::Spanned<crate::ast::Expr>>,
    BlockId,
) -> Result<(), LowerError>;

type FailCb<'a> = &'a mut dyn FnMut(&mut LowerCtx) -> Result<(), LowerError>;

#[derive(Default)]
struct MatcherLowerState {
    bitstring_fields: std::collections::HashMap<(crate::matcher::SubjectRef, u32), Var>,
    direct_bindings: std::collections::HashMap<String, Var>,
}

fn lower_matrix_to_current_fn(
    ctx: &mut LowerCtx,
    matrix: Matrix,
    fail_block: BlockId,
    body_cb: BodyCb<'_>,
) -> Result<(), LowerError> {
    let mut guard_stack = Vec::new();
    let mut guard_resolver = |name: &str, arity: usize, args: Vec<crate::matcher::GuardExpr>| {
        lower_guard_helper_call_to_dispatch(ctx, name, arity, args, &mut guard_stack)
    };
    let matcher = crate::pattern_matrix::compile_matcher_subset_with_guard_resolver(
        matrix,
        &mut guard_resolver,
    )
    .map_err(|err| LowerError::Unsupported {
        span: Span::DUMMY,
        what: format!("matcher cannot be lowered inline: {:?}", err),
    })?;
    let mut state = MatcherLowerState::default();
    lower_matcher_node(ctx, &matcher, matcher.root, fail_block, body_cb, &mut state)
}

fn lower_matcher_node(
    ctx: &mut LowerCtx,
    matcher: &crate::matcher::Matcher,
    node_id: crate::matcher::NodeId,
    fail_block: BlockId,
    body_cb: BodyCb<'_>,
    state: &mut MatcherLowerState,
) -> Result<(), LowerError> {
    let Some(node) = matcher.node(node_id).cloned() else {
        return Err(LowerError::Unsupported {
            span: Span::DUMMY,
            what: format!("matcher node {:?} is out of bounds", node_id),
        });
    };
    match node {
        crate::matcher::MatcherNode::Fail { .. } => {
            if !ctx.terminated {
                ctx.set_term(Term::Goto(fail_block, vec![]));
            }
            Ok(())
        }
        crate::matcher::MatcherNode::Leaf(leaf) => {
            let bindings = leaf
                .bindings
                .into_iter()
                .map(|binding| {
                    Ok((
                        binding.name,
                        materialize_matcher_subject(ctx, matcher, &binding.source, state)?,
                    ))
                })
                .collect::<Result<Vec<_>, LowerError>>()?;
            body_cb(ctx, leaf.body_id, bindings, Vec::new(), None, fail_block)?;
            Ok(())
        }
        crate::matcher::MatcherNode::Switch {
            subject,
            kind,
            cases,
            default,
            ..
        } => lower_matcher_switch(
            ctx, matcher, subject, kind, cases, default, fail_block, body_cb, state,
        ),
        crate::matcher::MatcherNode::Test {
            test,
            on_true,
            on_false,
            ..
        } => lower_matcher_test(
            ctx, matcher, test, on_true, on_false, fail_block, body_cb, state,
        ),
        crate::matcher::MatcherNode::Guard {
            expr,
            on_true,
            on_false,
            ..
        } => {
            let guard = lower_matcher_guard_expr(ctx, matcher, &expr, state)?;
            let false_b = ctx.cur_mut().block(vec![]);
            let true_b = ctx.cur_mut().block(vec![]);
            ctx.set_if_term(guard, true_b, false_b);
            ctx.cur_block = Some(true_b);
            ctx.terminated = false;
            let mut true_state = clone_matcher_lower_state(state);
            lower_matcher_node(ctx, matcher, on_true, fail_block, body_cb, &mut true_state)?;
            ctx.cur_block = Some(false_b);
            ctx.terminated = false;
            lower_matcher_node(ctx, matcher, on_false, fail_block, body_cb, state)
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn lower_matcher_switch(
    ctx: &mut LowerCtx,
    matcher: &crate::matcher::Matcher,
    subject: crate::matcher::SubjectRef,
    kind: crate::matcher::SwitchKind,
    cases: Vec<(crate::matcher::SwitchKey, crate::matcher::NodeId)>,
    default: crate::matcher::NodeId,
    fail_block: BlockId,
    body_cb: BodyCb<'_>,
    state: &mut MatcherLowerState,
) -> Result<(), LowerError> {
    let subject_v = materialize_matcher_subject(ctx, matcher, &subject, state)?;
    for (key, case) in cases {
        let Some((test, branch_on_true)) =
            lower_matcher_switch_test(ctx, subject_v, kind.clone(), key)?
        else {
            continue;
        };
        let (match_b, next_b) = if branch_on_true {
            let next_b = ctx.cur_mut().block(vec![]);
            let match_b = ctx.cur_mut().block(vec![]);
            (match_b, next_b)
        } else {
            let match_b = ctx.cur_mut().block(vec![]);
            let next_b = ctx.cur_mut().block(vec![]);
            (match_b, next_b)
        };
        if branch_on_true {
            ctx.set_if_term(test, match_b, next_b);
        } else {
            ctx.set_if_term(test, next_b, match_b);
        }
        ctx.cur_block = Some(match_b);
        ctx.terminated = false;
        let mut case_state = clone_matcher_lower_state(state);
        lower_matcher_node(ctx, matcher, case, fail_block, body_cb, &mut case_state)?;
        ctx.cur_block = Some(next_b);
        ctx.terminated = false;
    }
    lower_matcher_node(ctx, matcher, default, fail_block, body_cb, state)
}

#[allow(clippy::too_many_arguments)]
fn lower_matcher_test(
    ctx: &mut LowerCtx,
    matcher: &crate::matcher::Matcher,
    test: crate::matcher::MatcherTest,
    on_true: crate::matcher::NodeId,
    on_false: crate::matcher::NodeId,
    fail_block: BlockId,
    body_cb: BodyCb<'_>,
    state: &mut MatcherLowerState,
) -> Result<(), LowerError> {
    if let crate::matcher::MatcherTest::Bitstring { subject, fields } = test {
        let true_b = ctx.cur_mut().block(vec![]);
        let false_b = ctx.cur_mut().block(vec![]);
        let mut true_state = clone_matcher_lower_state(state);
        lower_matcher_bitstring_test(
            ctx,
            matcher,
            &subject,
            &fields,
            true_b,
            false_b,
            &mut true_state,
        )?;
        ctx.cur_block = Some(true_b);
        ctx.terminated = false;
        lower_matcher_node(ctx, matcher, on_true, fail_block, body_cb, &mut true_state)?;
        ctx.cur_block = Some(false_b);
        ctx.terminated = false;
        return lower_matcher_node(ctx, matcher, on_false, fail_block, body_cb, state);
    }

    let test_var = lower_matcher_bool_test(ctx, matcher, &test, state)?;
    let false_b = ctx.cur_mut().block(vec![]);
    let true_b = ctx.cur_mut().block(vec![]);
    ctx.set_if_term(test_var, true_b, false_b);
    ctx.cur_block = Some(true_b);
    ctx.terminated = false;
    let mut true_state = clone_matcher_lower_state(state);
    lower_matcher_node(ctx, matcher, on_true, fail_block, body_cb, &mut true_state)?;
    ctx.cur_block = Some(false_b);
    ctx.terminated = false;
    lower_matcher_node(ctx, matcher, on_false, fail_block, body_cb, state)
}

fn clone_matcher_lower_state(state: &MatcherLowerState) -> MatcherLowerState {
    MatcherLowerState {
        bitstring_fields: state.bitstring_fields.clone(),
        direct_bindings: state.direct_bindings.clone(),
    }
}

fn materialize_matcher_subject(
    ctx: &mut LowerCtx,
    matcher: &crate::matcher::Matcher,
    subject: &crate::matcher::SubjectRef,
    state: &mut MatcherLowerState,
) -> Result<Var, LowerError> {
    match subject {
        crate::matcher::SubjectRef::Input(id) => matcher
            .inputs
            .get(id.0 as usize)
            .and_then(|input| input.var)
            .ok_or_else(|| LowerError::Unsupported {
                span: Span::DUMMY,
                what: format!("inline matcher input {:?} has no IR var", id),
            }),
        crate::matcher::SubjectRef::TupleField { tuple, index } => {
            let tuple = materialize_matcher_subject(ctx, matcher, tuple, state)?;
            Ok(ctx.let_(Prim::TupleField(tuple, *index)))
        }
        crate::matcher::SubjectRef::ListHead(list) => {
            let list = materialize_matcher_subject(ctx, matcher, list, state)?;
            Ok(ctx.let_(Prim::ListHead(list)))
        }
        crate::matcher::SubjectRef::ListTail(list) => {
            let list = materialize_matcher_subject(ctx, matcher, list, state)?;
            Ok(ctx.let_(Prim::ListTail(list)))
        }
        crate::matcher::SubjectRef::MapValue { map, key } => {
            let map = materialize_matcher_subject(ctx, matcher, map, state)?;
            let key = lower_matcher_const(ctx, matcher, key)?;
            Ok(ctx.let_(Prim::MapGet(map, key)))
        }
        crate::matcher::SubjectRef::BitstringField { bitstring, index } => state
            .bitstring_fields
            .get(&((**bitstring).clone(), *index))
            .copied()
            .ok_or_else(|| LowerError::Unsupported {
                span: Span::DUMMY,
                what: format!("bitstring field {:?}/{} not available", bitstring, index),
            }),
    }
}

fn lower_matcher_const(
    ctx: &mut LowerCtx,
    matcher: &crate::matcher::Matcher,
    value: &crate::matcher::MatcherConst,
) -> Result<Var, LowerError> {
    Ok(match value {
        crate::matcher::MatcherConst::Int(n) => ctx.let_(Prim::Const(Const::Int(*n))),
        crate::matcher::MatcherConst::FloatBits(bits) => {
            ctx.let_(Prim::Const(Const::Float(f64::from_bits(*bits))))
        }
        crate::matcher::MatcherConst::AtomName(name) => {
            let atom = ctx.atoms.intern(name);
            ctx.let_(Prim::Const(Const::Atom(atom)))
        }
        crate::matcher::MatcherConst::Bool(true) => ctx.let_(Prim::Const(Const::True)),
        crate::matcher::MatcherConst::Bool(false) => ctx.let_(Prim::Const(Const::False)),
        crate::matcher::MatcherConst::Nil => ctx.let_(Prim::Const(Const::Nil)),
        crate::matcher::MatcherConst::Utf8Binary(bytes) => {
            let bit_len = (bytes.len() * 8) as u64;
            let bs = ctx.let_(Prim::ConstBitstring(bytes.clone(), bit_len));
            ctx.let_(Prim::Brand(bs, "utf8".to_string()))
        }
        crate::matcher::MatcherConst::PreparedKey(index) => {
            let key = matcher.prepared_keys.get(*index as usize).ok_or_else(|| {
                LowerError::Unsupported {
                    span: Span::DUMMY,
                    what: format!("prepared matcher key {} is out of bounds", index),
                }
            })?;
            lower_matcher_const(ctx, matcher, key)?
        }
        crate::matcher::MatcherConst::EmptyList => {
            return Err(LowerError::Unsupported {
                span: Span::DUMMY,
                what: format!("matcher const {:?} cannot be materialized inline", value),
            });
        }
    })
}

fn lower_matcher_pinned_var(
    ctx: &LowerCtx,
    matcher: &crate::matcher::Matcher,
    pinned: crate::matcher::PinnedId,
) -> Result<Var, LowerError> {
    let pinned = matcher
        .pinned
        .get(pinned.0 as usize)
        .ok_or_else(|| LowerError::Unsupported {
            span: Span::DUMMY,
            what: format!("matcher pinned slot {:?} out of bounds", pinned),
        })?;
    if let Some(input) = pinned.var {
        if let Some(var) = matcher
            .inputs
            .get(input.0 as usize)
            .and_then(|input| input.var)
        {
            return Ok(var);
        }
    }
    ctx.lookup(&pinned.name).ok_or_else(|| LowerError::Unbound {
        span: pinned.span,
        name: format!("pinned matcher var {}", pinned.name),
    })
}

fn lower_matcher_bool_test(
    ctx: &mut LowerCtx,
    matcher: &crate::matcher::Matcher,
    test: &crate::matcher::MatcherTest,
    state: &mut MatcherLowerState,
) -> Result<Var, LowerError> {
    Ok(match test {
        crate::matcher::MatcherTest::EqConst { subject, value } => {
            let subject = materialize_matcher_subject(ctx, matcher, subject, state)?;
            match value {
                crate::matcher::MatcherConst::EmptyList => ctx.let_(Prim::IsEmptyList(subject)),
                _ => {
                    let lit = lower_matcher_const(ctx, matcher, value)?;
                    ctx.let_(Prim::BinOp(BinOp::Eq, subject, lit))
                }
            }
        }
        crate::matcher::MatcherTest::EqPinned { subject, pinned } => {
            let subject = materialize_matcher_subject(ctx, matcher, subject, state)?;
            let pinned_var = lower_matcher_pinned_var(ctx, matcher, *pinned)?;
            ctx.let_(Prim::BinOp(BinOp::Eq, subject, pinned_var))
        }
        crate::matcher::MatcherTest::TupleArity { subject, arity } => {
            let subject = materialize_matcher_subject(ctx, matcher, subject, state)?;
            let tuple_ty = concrete_any_tuple(*arity as usize);
            ctx.let_(Prim::TypeTest(subject, Box::new(tuple_ty)))
        }
        crate::matcher::MatcherTest::ListCons { subject } => {
            let subject = materialize_matcher_subject(ctx, matcher, subject, state)?;
            let is_empty = ctx.let_(Prim::IsEmptyList(subject));
            let false_v = ctx.let_(Prim::Const(Const::False));
            ctx.let_(Prim::BinOp(BinOp::Eq, is_empty, false_v))
        }
        crate::matcher::MatcherTest::MapKind { subject } => {
            let subject = materialize_matcher_subject(ctx, matcher, subject, state)?;
            ctx.let_(Prim::TypeTest(subject, Box::new(concrete_any_map())))
        }
        crate::matcher::MatcherTest::Type { subject, ty } => {
            let subject = materialize_matcher_subject(ctx, matcher, subject, state)?;
            ctx.let_(Prim::TypeTest(subject, Box::new(ty.clone())))
        }
        crate::matcher::MatcherTest::MapHasKey { subject, key } => {
            let subject = materialize_matcher_subject(ctx, matcher, subject, state)?;
            let key = lower_matcher_const(ctx, matcher, key)?;
            let value = ctx.let_(Prim::MapGet(subject, key));
            let nil = ctx.let_(Prim::Const(Const::Nil));
            ctx.let_(Prim::BinOp(BinOp::Neq, value, nil))
        }
        crate::matcher::MatcherTest::Bitstring { .. } => {
            return Err(LowerError::Unsupported {
                span: Span::DUMMY,
                what: format!("matcher test {:?} needs specialized lowering", test),
            });
        }
    })
}

fn lower_matcher_switch_test(
    ctx: &mut LowerCtx,
    subject: Var,
    kind: crate::matcher::SwitchKind,
    key: crate::matcher::SwitchKey,
) -> Result<Option<(Var, bool)>, LowerError> {
    Ok(Some(match (kind, key) {
        (crate::matcher::SwitchKind::TupleArity, crate::matcher::SwitchKey::Arity(arity)) => {
            let tuple_ty = concrete_any_tuple(arity as usize);
            (ctx.let_(Prim::TypeTest(subject, Box::new(tuple_ty))), true)
        }
        (crate::matcher::SwitchKind::Atom, crate::matcher::SwitchKey::AtomName(name)) => {
            let atom = ctx.atoms.intern(&name);
            let lit = ctx.let_(Prim::Const(Const::Atom(atom)));
            (ctx.let_(Prim::BinOp(BinOp::Eq, subject, lit)), true)
        }
        (crate::matcher::SwitchKind::Int, crate::matcher::SwitchKey::Int(n)) => {
            let lit = ctx.let_(Prim::Const(Const::Int(n)));
            (ctx.let_(Prim::BinOp(BinOp::Eq, subject, lit)), true)
        }
        (crate::matcher::SwitchKind::Float, crate::matcher::SwitchKey::FloatBits(bits)) => {
            let lit = ctx.let_(Prim::Const(Const::Float(f64::from_bits(bits))));
            (ctx.let_(Prim::BinOp(BinOp::Eq, subject, lit)), true)
        }
        (crate::matcher::SwitchKind::Bool, crate::matcher::SwitchKey::Bool(b)) => {
            let lit = ctx.let_(Prim::Const(if b { Const::True } else { Const::False }));
            (ctx.let_(Prim::BinOp(BinOp::Eq, subject, lit)), true)
        }
        (crate::matcher::SwitchKind::Nil, crate::matcher::SwitchKey::Nil)
        | (crate::matcher::SwitchKind::ListCons, crate::matcher::SwitchKey::Nil) => {
            let lit = ctx.let_(Prim::Const(Const::Nil));
            (ctx.let_(Prim::BinOp(BinOp::Eq, subject, lit)), true)
        }
        (crate::matcher::SwitchKind::Binary, crate::matcher::SwitchKey::Utf8Binary(bytes)) => {
            let bit_len = (bytes.len() * 8) as u64;
            let bs = ctx.let_(Prim::ConstBitstring(bytes, bit_len));
            let lit = ctx.let_(Prim::Brand(bs, "utf8".to_string()));
            (ctx.let_(Prim::BinOp(BinOp::Eq, subject, lit)), true)
        }
        (crate::matcher::SwitchKind::ListCons, crate::matcher::SwitchKey::EmptyList) => {
            (ctx.let_(Prim::IsEmptyList(subject)), true)
        }
        (crate::matcher::SwitchKind::ListCons, crate::matcher::SwitchKey::Cons) => {
            (ctx.let_(Prim::IsEmptyList(subject)), false)
        }
        _ => return Ok(None),
    }))
}

fn lower_matcher_bitstring_test(
    ctx: &mut LowerCtx,
    matcher: &crate::matcher::Matcher,
    subject: &crate::matcher::SubjectRef,
    fields: &[crate::matcher::MatcherBitField],
    success_block: BlockId,
    fail_block: BlockId,
    state: &mut MatcherLowerState,
) -> Result<(), LowerError> {
    let subject_v = materialize_matcher_subject(ctx, matcher, subject, state)?;
    let mut reader = ctx.let_(Prim::BitReaderInit(subject_v));
    for (index, field) in fields.iter().enumerate() {
        let size = lower_matcher_bit_size(ctx, &field.size, state)?;
        let result = ctx.let_(Prim::BitReadField {
            reader,
            ty: matcher_bit_type_to_ast(field.ty),
            size,
            endian: matcher_endian_to_ast(field.endian),
            signed: field.signed,
            unit: field.unit,
            is_last: index + 1 == fields.len(),
        });
        let ok = ctx.let_(Prim::TupleField(result, 0));
        let cont_b = ctx.cur_mut().block(vec![]);
        ctx.set_if_term(ok, cont_b, fail_block);
        ctx.cur_block = Some(cont_b);
        ctx.terminated = false;
        let extracted = ctx.let_(Prim::TupleField(result, 1));
        reader = ctx.let_(Prim::TupleField(result, 2));
        state
            .bitstring_fields
            .insert((subject.clone(), index as u32), extracted);
        for name in &field.direct_bindings {
            state.direct_bindings.insert(name.clone(), extracted);
        }
    }
    let done = ctx.let_(Prim::BitReaderDone(reader));
    ctx.set_if_term(done, success_block, fail_block);
    Ok(())
}

fn lower_matcher_bit_size(
    ctx: &LowerCtx,
    size: &Option<crate::matcher::MatcherBitSize>,
    state: &MatcherLowerState,
) -> Result<Option<BitSizeIr>, LowerError> {
    Ok(match size {
        None => None,
        Some(crate::matcher::MatcherBitSize::Literal(n)) => Some(BitSizeIr::Literal(*n)),
        Some(crate::matcher::MatcherBitSize::BindingName(name)) => {
            let v = state
                .direct_bindings
                .get(name)
                .copied()
                .or_else(|| ctx.lookup(name))
                .ok_or_else(|| LowerError::Unbound {
                    span: Span::DUMMY,
                    name: format!("bit size var {}", name),
                })?;
            Some(BitSizeIr::Var(v))
        }
    })
}

fn lower_matcher_guard_expr(
    ctx: &mut LowerCtx,
    matcher: &crate::matcher::Matcher,
    expr: &crate::matcher::GuardExpr,
    state: &mut MatcherLowerState,
) -> Result<Var, LowerError> {
    use crate::matcher::{GuardBinOp, GuardExpr, GuardUnaryOp};
    Ok(match expr {
        GuardExpr::Const(c) => lower_matcher_const(ctx, matcher, c)?,
        GuardExpr::Subject(subject) => materialize_matcher_subject(ctx, matcher, subject, state)?,
        GuardExpr::Pinned(pinned) => lower_matcher_pinned_var(ctx, matcher, *pinned)?,
        GuardExpr::Unary { op, expr } => {
            let v = lower_matcher_guard_expr(ctx, matcher, expr, state)?;
            match op {
                GuardUnaryOp::Not => ctx.let_(Prim::UnOp(UnOp::Not, v)),
                GuardUnaryOp::Neg => ctx.let_(Prim::UnOp(UnOp::Neg, v)),
            }
        }
        GuardExpr::Binary { op, lhs, rhs } => {
            let lhs = lower_matcher_guard_expr(ctx, matcher, lhs, state)?;
            let rhs = lower_matcher_guard_expr(ctx, matcher, rhs, state)?;
            let op = match op {
                GuardBinOp::Add => BinOp::Add,
                GuardBinOp::Sub => BinOp::Sub,
                GuardBinOp::Mul => BinOp::Mul,
                GuardBinOp::Div => BinOp::Div,
                GuardBinOp::Rem => BinOp::Mod,
                GuardBinOp::Eq => BinOp::Eq,
                GuardBinOp::Neq => BinOp::Neq,
                GuardBinOp::Lt => BinOp::Lt,
                GuardBinOp::LtEq => BinOp::Le,
                GuardBinOp::Gt => BinOp::Gt,
                GuardBinOp::GtEq => BinOp::Ge,
                GuardBinOp::And => BinOp::And,
                GuardBinOp::Or => BinOp::Or,
            };
            ctx.let_(Prim::BinOp(op, lhs, rhs))
        }
        GuardExpr::Dispatch { inputs, dispatch } => {
            lower_matcher_guard_dispatch(ctx, matcher, inputs, dispatch, state)?
        }
    })
}

fn lower_matcher_guard_dispatch(
    ctx: &mut LowerCtx,
    outer_matcher: &crate::matcher::Matcher,
    inputs: &[crate::matcher::GuardExpr],
    dispatch: &crate::matcher::GuardDispatch,
    outer_state: &mut MatcherLowerState,
) -> Result<Var, LowerError> {
    if inputs.len() != dispatch.matcher.inputs.len() {
        return Err(LowerError::Unsupported {
            span: Span::DUMMY,
            what: format!(
                "guard dispatch input arity mismatch: {} args for {} inputs",
                inputs.len(),
                dispatch.matcher.inputs.len()
            ),
        });
    }

    let mut matcher = dispatch.matcher.clone();
    for (input, expr) in matcher.inputs.iter_mut().zip(inputs) {
        input.var = Some(lower_matcher_guard_expr(
            ctx,
            outer_matcher,
            expr,
            outer_state,
        )?);
    }

    let dispatch_block = ctx.cur_block;
    let dispatch_terminated = ctx.terminated;
    let result = ctx.cur_mut().fresh_var();
    let join_block = ctx.cur_mut().block(vec![result]);
    let fail_block = ctx.cur_mut().block(vec![]);
    ctx.cur_block = Some(fail_block);
    ctx.terminated = false;
    let false_v = ctx.let_(Prim::Const(Const::False));
    ctx.set_term(Term::Goto(join_block, vec![false_v]));

    ctx.cur_block = dispatch_block;
    ctx.terminated = dispatch_terminated;

    let mut state = MatcherLowerState::default();
    lower_guard_dispatch_node(
        ctx,
        &matcher,
        &dispatch.bodies,
        matcher.root,
        fail_block,
        join_block,
        &mut state,
    )?;
    ctx.cur_block = Some(join_block);
    ctx.terminated = false;
    Ok(result)
}

fn lower_guard_dispatch_node(
    ctx: &mut LowerCtx,
    matcher: &crate::matcher::Matcher,
    bodies: &[crate::matcher::GuardExpr],
    node_id: crate::matcher::NodeId,
    fail_block: BlockId,
    join_block: BlockId,
    state: &mut MatcherLowerState,
) -> Result<(), LowerError> {
    let Some(node) = matcher.node(node_id).cloned() else {
        return Err(LowerError::Unsupported {
            span: Span::DUMMY,
            what: format!("guard dispatch matcher node {:?} is out of bounds", node_id),
        });
    };
    match node {
        crate::matcher::MatcherNode::Fail { .. } => {
            if !ctx.terminated {
                ctx.set_term(Term::Goto(fail_block, vec![]));
            }
            Ok(())
        }
        crate::matcher::MatcherNode::Leaf(leaf) => {
            let body =
                bodies
                    .get(leaf.body_id as usize)
                    .ok_or_else(|| LowerError::Unsupported {
                        span: leaf.span,
                        what: format!("guard dispatch body {} is out of bounds", leaf.body_id),
                    })?;
            let value = lower_matcher_guard_expr(ctx, matcher, body, state)?;
            ctx.set_term(Term::Goto(join_block, vec![value]));
            ctx.terminated = true;
            Ok(())
        }
        crate::matcher::MatcherNode::Switch {
            subject,
            kind,
            cases,
            default,
            ..
        } => {
            let subject_v = materialize_matcher_subject(ctx, matcher, &subject, state)?;
            for (key, case) in cases {
                let Some((test, branch_on_true)) =
                    lower_matcher_switch_test(ctx, subject_v, kind.clone(), key)?
                else {
                    continue;
                };
                let (match_b, next_b) = if branch_on_true {
                    let next_b = ctx.cur_mut().block(vec![]);
                    let match_b = ctx.cur_mut().block(vec![]);
                    (match_b, next_b)
                } else {
                    let match_b = ctx.cur_mut().block(vec![]);
                    let next_b = ctx.cur_mut().block(vec![]);
                    (match_b, next_b)
                };
                if branch_on_true {
                    ctx.set_if_term(test, match_b, next_b);
                } else {
                    ctx.set_if_term(test, next_b, match_b);
                }
                ctx.cur_block = Some(match_b);
                ctx.terminated = false;
                let mut case_state = clone_matcher_lower_state(state);
                lower_guard_dispatch_node(
                    ctx,
                    matcher,
                    bodies,
                    case,
                    fail_block,
                    join_block,
                    &mut case_state,
                )?;
                ctx.cur_block = Some(next_b);
                ctx.terminated = false;
            }
            lower_guard_dispatch_node(ctx, matcher, bodies, default, fail_block, join_block, state)
        }
        crate::matcher::MatcherNode::Test {
            test,
            on_true,
            on_false,
            ..
        } => lower_guard_dispatch_test(
            ctx, matcher, bodies, test, on_true, on_false, fail_block, join_block, state,
        ),
        crate::matcher::MatcherNode::Guard {
            expr,
            on_true,
            on_false,
            ..
        } => {
            let guard = lower_matcher_guard_expr(ctx, matcher, &expr, state)?;
            let false_b = ctx.cur_mut().block(vec![]);
            let true_b = ctx.cur_mut().block(vec![]);
            ctx.set_if_term(guard, true_b, false_b);
            ctx.cur_block = Some(true_b);
            ctx.terminated = false;
            let mut true_state = clone_matcher_lower_state(state);
            lower_guard_dispatch_node(
                ctx,
                matcher,
                bodies,
                on_true,
                fail_block,
                join_block,
                &mut true_state,
            )?;
            ctx.cur_block = Some(false_b);
            ctx.terminated = false;
            lower_guard_dispatch_node(
                ctx, matcher, bodies, on_false, fail_block, join_block, state,
            )
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn lower_guard_dispatch_test(
    ctx: &mut LowerCtx,
    matcher: &crate::matcher::Matcher,
    bodies: &[crate::matcher::GuardExpr],
    test: crate::matcher::MatcherTest,
    on_true: crate::matcher::NodeId,
    on_false: crate::matcher::NodeId,
    fail_block: BlockId,
    join_block: BlockId,
    state: &mut MatcherLowerState,
) -> Result<(), LowerError> {
    if let crate::matcher::MatcherTest::Bitstring { subject, fields } = test {
        let true_b = ctx.cur_mut().block(vec![]);
        let false_b = ctx.cur_mut().block(vec![]);
        let mut true_state = clone_matcher_lower_state(state);
        lower_matcher_bitstring_test(
            ctx,
            matcher,
            &subject,
            &fields,
            true_b,
            false_b,
            &mut true_state,
        )?;
        ctx.cur_block = Some(true_b);
        ctx.terminated = false;
        lower_guard_dispatch_node(
            ctx,
            matcher,
            bodies,
            on_true,
            fail_block,
            join_block,
            &mut true_state,
        )?;
        ctx.cur_block = Some(false_b);
        ctx.terminated = false;
        return lower_guard_dispatch_node(
            ctx, matcher, bodies, on_false, fail_block, join_block, state,
        );
    }

    let test_var = lower_matcher_bool_test(ctx, matcher, &test, state)?;
    let false_b = ctx.cur_mut().block(vec![]);
    let true_b = ctx.cur_mut().block(vec![]);
    ctx.set_if_term(test_var, true_b, false_b);
    ctx.cur_block = Some(true_b);
    ctx.terminated = false;
    let mut true_state = clone_matcher_lower_state(state);
    lower_guard_dispatch_node(
        ctx,
        matcher,
        bodies,
        on_true,
        fail_block,
        join_block,
        &mut true_state,
    )?;
    ctx.cur_block = Some(false_b);
    ctx.terminated = false;
    lower_guard_dispatch_node(
        ctx, matcher, bodies, on_false, fail_block, join_block, state,
    )
}

fn matcher_bit_type_to_ast(ty: crate::matcher::MatcherBitType) -> crate::ast::BitType {
    match ty {
        crate::matcher::MatcherBitType::Integer => crate::ast::BitType::Integer,
        crate::matcher::MatcherBitType::Float => crate::ast::BitType::Float,
        crate::matcher::MatcherBitType::Binary => crate::ast::BitType::Binary,
        crate::matcher::MatcherBitType::Bits => crate::ast::BitType::Bits,
        crate::matcher::MatcherBitType::Utf8 => crate::ast::BitType::Utf8,
        crate::matcher::MatcherBitType::Utf16 => crate::ast::BitType::Utf16,
        crate::matcher::MatcherBitType::Utf32 => crate::ast::BitType::Utf32,
    }
}

fn matcher_endian_to_ast(endian: crate::matcher::MatcherEndian) -> crate::ast::Endian {
    match endian {
        crate::matcher::MatcherEndian::Big => crate::ast::Endian::Big,
        crate::matcher::MatcherEndian::Little => crate::ast::Endian::Little,
        crate::matcher::MatcherEndian::Native => crate::ast::Endian::Native,
    }
}

fn peel_as_pat(p: &Spanned<Pattern>) -> &Spanned<Pattern> {
    let mut cur = p;
    while let Pattern::As(_, inner) = &cur.node {
        cur = inner;
    }
    cur
}
fn collect_one(p: &Pattern, v: Var, out: &mut Vec<(String, Var)>) {
    match p {
        Pattern::Var(name) => out.push((name.clone(), v)),
        Pattern::As(name, inner) => {
            out.push((name.clone(), v));
            collect_one(&inner.node, v, out);
        }
        _ => {}
    }
}

fn bind_param_topname(ctx: &mut LowerCtx, pv: Var, pat: &Spanned<Pattern>) {
    let mut cur = pat;
    while let Pattern::As(name, inner) = &cur.node {
        ctx.bind(name, pv);
        cur = inner;
    }
    if let Pattern::Var(name) = &cur.node {
        ctx.bind(name, pv);
    }
}

fn lower_multi_clause<T: crate::types::Types<Ty = crate::types::Ty>>(
    ctx: &mut LowerCtx,
    t: &mut T,
    fn_def: &FnDef,
    param_vars: &[Var],
    entry: BlockId,
) -> Result<(), LowerError> {
    // fz-qbg.2 — per-clause body continuation fns, mirroring fz-duq's
    // if/case/cond/with shape. The try_blocks + fail_block cascade stays
    // intra-fn (pattern bind and guard tests can't CPS-split — they only
    // emit TypeTest / projection / If). After pattern bind succeeds, the
    // try_block TailCalls a per-clause body cont fn (`fn_clause_N`) with
    // the post-pattern env (outer + pattern bindings). The body lowers in
    // that cont fn so any internal CPS-split stays confined to that
    // clause's lineage; the source-level fn's outer FnIr is fully
    // populated (try cascade + arm TailCalls) before any body lowers.
    //
    // Why the typer cooperates now: fz-qbg.1 made the typer's call graph
    // structural rather than any-key-spec-gated. With that, outer ↔
    // fn_clause_N edges show up in the SCC, widening fires at the
    // per-SCC fixpoint, and the recursive callsite's broadened key
    // (e.g. `[int, int]` for `count`'s tail) lands in the spec set.

    // fz-puj.52.7 — internal dispatch lowers the Matcher inline
    // into the user fn again. The production matcher-fn shape made
    // dispatch visible as ordinary spec-producing fns, duplicating specs
    // for every key. Receive remains the ABI-driven matcher-fn case.
    let fail_block = ctx.cur_mut().block(vec![]);
    ctx.cur_block = Some(fail_block);
    let fc = ctx.atoms.intern("function_clause");
    let v = ctx.let_(Prim::Const(Const::Atom(fc)));
    ctx.set_term(Term::Halt(v));

    let matrix_entry = ctx.cur_mut().block(vec![]);
    ctx.cur_mut()
        .set_terminator(entry, Term::Goto(matrix_entry, vec![]));
    ctx.cur_block = Some(matrix_entry);
    ctx.terminated = false;

    let mut rows: Vec<Row> = Vec::with_capacity(fn_def.clauses.len());
    for (i, c) in fn_def.clauses.iter().enumerate() {
        let mut preconditions: Vec<(Var, crate::types::Ty)> = Vec::new();
        for (pv, tok_opt) in param_vars.iter().zip(&c.param_annotations) {
            if let Some(toks) = tok_opt
                && let Ok((ty, _)) =
                    crate::type_expr::parse_type_expr(t, &toks.0, &ctx.combined_type_env)
            {
                preconditions.push((*pv, ty));
            }
        }
        rows.push(Row {
            patterns: c.params.clone(),
            preconditions,
            bindings: Vec::new(),
            guard: c.guard.clone(),
            body_id: i as BodyId,
        });
    }
    let matrix = Matrix {
        subjects: param_vars.to_vec(),
        rows,
    };

    let mut clause_conts: Vec<Option<ContFn>> = (0..fn_def.clauses.len()).map(|_| None).collect();
    let prev_origin = ctx.branch_origin;
    ctx.branch_origin = crate::fz_ir::BranchOrigin::ClauseDispatch;
    {
        let fn_def_ref = fn_def;
        let param_vars_ref = param_vars;
        let clause_conts_ref = &mut clause_conts;
        let mut cb = |ctx: &mut LowerCtx,
                      body_id: BodyId,
                      bindings: Vec<(String, Var)>,
                      preconditions: Vec<(Var, crate::types::Ty)>,
                      guard: Option<crate::ast::Spanned<crate::ast::Expr>>,
                      fall_block: BlockId|
         -> Result<(), LowerError> {
            let i = body_id as usize;
            let clause = &fn_def_ref.clauses[i];
            ctx.env.clear();
            ctx.env_order.clear();
            for (pv, pat) in param_vars_ref.iter().zip(&clause.params) {
                bind_param_topname(ctx, *pv, pat);
            }
            for (name, var) in &bindings {
                ctx.bind(name, *var);
            }
            for (pv, ty) in &preconditions {
                let tt = ctx.let_(Prim::TypeTest(*pv, Box::new(ty.clone())));
                let pass_b = ctx.cur_mut().block(vec![]);
                ctx.set_if_term(tt, pass_b, fall_block);
                ctx.cur_block = Some(pass_b);
                ctx.terminated = false;
            }
            if let Some(g) = &guard {
                let guard_var = lower_expr(ctx, g, false)?;
                let body_b = ctx.cur_mut().block(vec![]);
                ctx.set_if_term(guard_var, body_b, fall_block);
                ctx.cur_block = Some(body_b);
                ctx.terminated = false;
            }
            let cont = mint_cont_fn(
                ctx,
                format!("fn_clause_{}", i),
                clause.span,
                crate::fz_ir::FnCategory::MultiClauseCont,
            );
            let captures = ctx.captured_snapshot();
            let capture_vars: Vec<Var> = captures.iter().map(|(_, v)| *v).collect();
            ctx.set_term(Term::TailCall {
                ident: crate::fz_ir::CallsiteIdent::from_source(clause.span),
                callee: cont.id,
                args: capture_vars,
                is_back_edge: false,
            });
            ctx.terminated = true;
            clause_conts_ref[i] = Some(cont);
            Ok(())
        };
        let result = lower_matrix_to_current_fn(ctx, matrix, fail_block, &mut cb);
        ctx.branch_origin = prev_origin;
        result?;
    }

    for (i, clause) in fn_def.clauses.iter().enumerate() {
        let Some(cont) = clause_conts[i].clone() else {
            continue;
        };
        let _ = switch_to_cont_fn(ctx, &cont, 0);
        let result = lower_expr(ctx, &clause.body, /* is_tail */ true)?;
        if !ctx.terminated {
            ctx.set_term(Term::Return(result));
            ctx.terminated = true;
        }
    }

    Ok(())
}

fn lower_expr(ctx: &mut LowerCtx, e: &Spanned<Expr>, is_tail: bool) -> Result<Var, LowerError> {
    let sp = e.span;
    match &e.node {
        Expr::Int(n) => Ok(ctx.let_at(Prim::Const(Const::Int(*n)), sp)),
        Expr::Float(x) => Ok(ctx.let_at(Prim::Const(Const::Float(*x)), sp)),
        Expr::Binary(bytes) => {
            // fz-axu.11 (L3) — every `"…"` literal lowers to a
            // `utf8`-branded const bitstring. UTF-8 validity is a lexer
            // invariant (see read_quoted_binary_bytes in src/lexer.rs); raw
            // bytes flow through `<<…>>` syntax instead.
            let bit_len = (bytes.len() * 8) as u64;
            let bs = ctx.let_at(Prim::ConstBitstring(bytes.clone(), bit_len), sp);
            Ok(ctx.let_at(Prim::Brand(bs, "utf8".to_string()), sp))
        }
        Expr::Atom(s) => {
            let id = ctx.atoms.intern(s);
            Ok(ctx.let_at(Prim::Const(Const::Atom(id)), sp))
        }
        Expr::Bool(true) => Ok(ctx.let_at(Prim::Const(Const::True), sp)),
        Expr::Bool(false) => Ok(ctx.let_at(Prim::Const(Const::False), sp)),
        Expr::Nil => Ok(ctx.let_at(Prim::Const(Const::Nil), sp)),

        Expr::Var(name) => {
            if let Some(v) = ctx.lookup(name) {
                return Ok(v);
            }
            // Fall back: bare top-level fn name used as a value -> 0-captured
            // closure pointing at the fn's IR id. With no explicit arity in
            // the bare-name form, picks the first matching name (overloads
            // disambiguate via the explicit `&name/arity` form — see the
            // `Expr::FnRef` arm).
            if let Some((_, fn_id)) = ctx
                .fns
                .iter()
                .find(|((n, _), _)| n == name)
                .map(|(k, v)| (k.clone(), *v))
            {
                return Ok(ctx.let_at(Prim::make_closure(sp, fn_id, vec![]), sp));
            }
            Err(LowerError::Unbound {
                span: sp,
                name: name.clone(),
            })
        }

        // fz-swt.5: `&name/arity` — explicit, arity-aware fn reference.
        // Direct (name, arity) lookup in the same fn map Call uses, so an
        // overloaded name resolves unambiguously to the requested clause.
        Expr::FnRef { name, arity } => {
            if let Some(&fn_id) = ctx.fns.get(&(name.clone(), *arity)) {
                return Ok(ctx.let_at(Prim::make_closure(sp, fn_id, vec![]), sp));
            }
            // fz-eol — `&libc::close/1`: synthesize (and cache) a top-level
            // wrapper fn that forwards its args to the named extern, then
            // return a closure pointing at that wrapper.
            if let Some(eid) = ctx.externs.lookup(name) {
                let decl = ctx
                    .extern_decls
                    .iter()
                    .find(|d| d.id == eid)
                    .expect("extern table out of sync with extern_decls");
                if decl.params.len() == *arity {
                    let fn_id = ctx.ensure_extern_wrapper(eid);
                    return Ok(ctx.let_at(Prim::make_closure(sp, fn_id, vec![]), sp));
                }
            }
            Err(LowerError::Unbound {
                span: sp,
                name: format!("fn {}/{}", name, arity),
            })
        }

        Expr::BinOp(op, a, b) => {
            let va_raw = lower_expr(ctx, a, false)?;
            let park_a = ctx.park(va_raw);
            let vb = lower_expr(ctx, b, false)?;
            let va = ctx.unpark(&park_a);
            ctx.unbind(&park_a);
            let irop = lower_binop(*op, sp)?;
            Ok(ctx.let_at(Prim::BinOp(irop, va, vb), sp))
        }
        Expr::UnOp(op, x) => {
            let v = lower_expr(ctx, x, false)?;
            let irop = match op {
                AstUnOp::Neg => UnOp::Neg,
                AstUnOp::Not => UnOp::Not,
            };
            Ok(ctx.let_at(Prim::UnOp(irop, v), sp))
        }

        Expr::Block(exprs) => {
            if exprs.is_empty() {
                return Ok(ctx.let_(Prim::Const(Const::Nil)));
            }
            let last = exprs.len() - 1;
            let saved_env = ctx.env.clone();
            let saved_order = ctx.env_order.clone();
            let mut result = Var(0);
            for (i, ex) in exprs.iter().enumerate() {
                let tail = is_tail && i == last;
                result = lower_expr(ctx, ex, tail)?;
            }
            // Block scope ends: restore env so block-bound vars don't leak.
            // (Match expressions inside a block do bind into the surrounding
            // scope per fz semantics, so we keep new bindings in saved scope.
            // Actually: fz match expressions bind to the enclosing scope
            // for the rest of that scope. Simplest semantics: blocks DO
            // propagate bindings outward, so we don't restore.)
            let _ = saved_env;
            let _ = saved_order;
            Ok(result)
        }

        Expr::If(cond, then_e, else_opt) => lower_if(ctx, cond, then_e, else_opt, is_tail, sp),

        Expr::Match(pat, expr) => {
            let v = lower_expr(ctx, expr, false)?;
            let fail_block = ctx.cur_mut().block(vec![]);
            let prev_origin = ctx.branch_origin;
            ctx.branch_origin = crate::fz_ir::BranchOrigin::PatternBind;
            let res = lower_pattern_bind(ctx, v, pat, fail_block);
            ctx.branch_origin = prev_origin;
            res?;
            // After match, control is in current_block; result is the matched value.
            // Set fail block (only reached on dynamic mismatch).
            let saved = ctx.cur_block();
            ctx.cur_block = Some(fail_block);
            let me = ctx.atoms.intern("match_error");
            let mev = ctx.let_(Prim::Const(Const::Atom(me)));
            ctx.set_term(Term::Halt(mev));
            ctx.cur_block = Some(saved);
            Ok(v)
        }

        Expr::List(elems, tail) => {
            let parks = lower_seq(ctx, elems)?;
            let tail_park = if let Some(t) = tail {
                let v = lower_expr(ctx, t, false)?;
                Some(ctx.park(v))
            } else {
                None
            };
            let vs: Vec<Var> = parks.iter().map(|n| ctx.unpark(n)).collect();
            let tail_v = tail_park.as_ref().map(|n| ctx.unpark(n));
            for n in &parks {
                ctx.unbind(n);
            }
            if let Some(n) = &tail_park {
                ctx.unbind(n);
            }
            Ok(ctx.let_(Prim::MakeList(vs, tail_v)))
        }
        Expr::Tuple(elems) => {
            let parks = lower_seq(ctx, elems)?;
            let vs: Vec<Var> = parks.iter().map(|n| ctx.unpark(n)).collect();
            for n in &parks {
                ctx.unbind(n);
            }
            Ok(ctx.let_(Prim::MakeTuple(vs)))
        }

        Expr::Call(target, args) => {
            // Lower arg exprs first; park each so they survive subsequent splits.
            let parks = lower_seq(ctx, args)?;
            let arg_vars: Vec<Var> = parks.iter().map(|n| ctx.unpark(n)).collect();
            for n in &parks {
                ctx.unbind(n);
            }
            // Resolve callee.
            let callee_name = match &target.node {
                Expr::Var(n) => n.clone(),
                _ => {
                    return Err(LowerError::Unsupported {
                        span: target.span,
                        what: "Call target other than Var (deferred)".into(),
                    });
                }
            };
            // Local closure value? (Shadows fn lookup if a local of the same name exists.)
            if let Some(local_var) = ctx.lookup(&callee_name) {
                if is_tail {
                    ctx.set_term_at(
                        Term::TailCallClosure {
                            ident: crate::fz_ir::CallsiteIdent::from_source(sp),
                            closure: local_var,
                            args: arg_vars,
                        },
                        sp,
                    );
                    ctx.terminated = true;
                    return Ok(Var(0));
                } else {
                    return cps_split_call_closure(ctx, local_var, arg_vars, sp);
                }
            }
            // fz-ul4.19.3: `receive(...)` is a Term, not a Prim — it's a
            // scheduler-mediated yield point. After CPS-style splitting,
            // it has the same continuation shape as Term::Call but no
            // callee fn.
            if callee_name == "receive" {
                if !arg_vars.is_empty() {
                    return Err(LowerError::Unsupported {
                        span: sp,
                        what: format!("receive/{} not supported (use receive/0)", arg_vars.len()),
                    });
                }
                if is_tail {
                    // Tail receive: the received message becomes the fn's
                    // return value. Lower as receive into a synthetic
                    // continuation that just Returns its arg.
                    return cps_split_receive(ctx, sp, /* tail */ true);
                }
                return cps_split_receive(ctx, sp, /* tail */ false);
            }
            // fz-ul4.29.9 / fz-ext.7 — spawn is special: wrap the closure arg
            // in fz_spawn_thunk before dispatching to fz_spawn / fz_spawn_opt.
            // This must be checked before the generic ExternTable lookup so that
            // `spawn` (user-facing name) resolves to the thunk-wrapped fz_spawn
            // extern, not a non-existent user fn.
            if callee_name == "spawn" && (arg_vars.len() == 1 || arg_vars.len() == 2) {
                let thunk_id = ctx.ensure_spawn_thunk();
                let wrapper = ctx.let_at(Prim::make_closure(sp, thunk_id, vec![arg_vars[0]]), sp);
                let mut new_args = vec![wrapper];
                new_args.extend_from_slice(&arg_vars[1..]);
                let sym = if arg_vars.len() == 1 {
                    "fz_spawn"
                } else {
                    "fz_spawn_opt"
                };
                let eid = ctx
                    .externs
                    .lookup(sym)
                    .expect("fz_spawn/fz_spawn_opt must be in runtime.fz");
                return Ok(ctx.let_at(Prim::Extern(eid, new_args), sp));
            }
            // Extern (runtime.fz / user-declared `extern "C" fn`)?
            if let Some(eid) = ctx.externs.lookup(&callee_name) {
                return Ok(ctx.let_at(Prim::Extern(eid, arg_vars), sp));
            }
            let arity = arg_vars.len();
            let callee =
                *ctx.fns
                    .get(&(callee_name.clone(), arity))
                    .ok_or_else(|| LowerError::Unbound {
                        span: target.span,
                        name: format!("fn {}/{}", callee_name, arity),
                    })?;
            if is_tail {
                ctx.set_term_at(
                    Term::TailCall {
                        ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
                        callee,
                        args: arg_vars,
                        is_back_edge: false, // annotate_back_edges fills this in post-lowering
                    },
                    sp,
                );
                ctx.terminated = true;
                Ok(Var(0))
            } else {
                cps_split_call(ctx, callee, arg_vars, sp)
            }
        }

        Expr::Lambda(params, body) => lower_lambda(ctx, params, body, sp),

        Expr::Case(Some(subject), clauses) => lower_case(ctx, subject, clauses, is_tail, sp),
        Expr::Case(None, _) => Err(LowerError::Unsupported {
            span: sp,
            what: "headless case must appear on the right side of a pipe".into(),
        }),
        Expr::Cond(arms) => lower_cond(ctx, arms, is_tail, sp),
        Expr::With(bindings, body, else_clauses) => {
            lower_with(ctx, bindings, body, else_clauses, is_tail, sp)
        }
        // fz-yxs — selective receive: lower into Term::ReceiveMatched with
        // per-clause body/guard fns and an optional after body fn.
        Expr::Receive { clauses, after } => {
            lower_receive(ctx, clauses, after.as_deref(), is_tail, sp)
        }
        Expr::Map(entries) => lower_map(ctx, entries),
        Expr::MapUpdate(base, entries) => lower_map_update(ctx, base, entries),
        Expr::Index(map, key) => lower_index(ctx, map, key),
        Expr::Bitstring(fields) => lower_bitstring_expr(ctx, fields),
        Expr::VecLit(kind, els) => lower_vec_lit(ctx, *kind, els, sp),
        Expr::Quote(_) => Err(LowerError::PostExpansionNode {
            span: sp,
            what: "Quote".into(),
        }),
        Expr::Unquote(_) => Err(LowerError::PostExpansionNode {
            span: sp,
            what: "Unquote".into(),
        }),
    }
    // Note: lower_if is implemented as a separate function below to keep the
    // var/block dance clean; the unreachable!() above is replaced via a
    // direct branch into it before this match.
}

// -----------------------------------------------------------------------------
// fz-duq.1: branching-construct join helpers
// -----------------------------------------------------------------------------
//
// `if`/`case`/`cond`/`with` need to join multiple arm bodies at a single
// "rest of surrounding code" point. The pre-fz-duq design used a join
// *block* inside the current fn — fragile because a non-tail Call in any
// arm body triggers `cps_split_call`, which finalizes the current fn,
// stranding the join block in a built-and-immutable FnIr.
//
// The fix mirrors what `cps_split_call` already does for non-tail Calls:
// each branching construct uses *continuation fns* as joins. Each arm is
// itself a continuation fn so that arm-internal CPS-splits stay confined
// to their own arm's lineage and never finalize the construct's outer
// fn prematurely.
//
// The three helpers below are used by `lower_if`/`lower_case`/`lower_cond`/
// `lower_with`:
//
//   * `mint_cont_fn`           — allocate a FnId + snapshot outer env.
//   * `switch_to_cont_fn`      — finalize current fn, switch to the cont's
//                                builder, rebind env to cap params.
//   * `finalize_arm`           — at arm's end, emit the right terminator
//                                (Return for tail position, TailCall to
//                                the join fn for non-tail position, or
//                                nothing if the arm self-terminated).
//
// Post-inline, these collapse: a one-call-site cont fn whose body is just
// `Return(param)` gets inlined back by `inline_tail_calls_once`, so the
// final CLIF for a non-CPS-splitting arm is the same as today's block-join
// shape (often tighter — see fz-duq.2 acceptance).

/// Handle to a freshly minted continuation fn (per-arm body or post-construct
/// join). The fn's builder is not yet created; the caller switches into it
/// via `switch_to_cont_fn` when ready to lower its body.
#[derive(Debug, Clone)]
struct ContFn {
    id: FnId,
    name: String,
    /// Names + outer-fn Vars of locals captured at the time the fn was
    /// minted. These names become the cont fn's entry params (after the
    /// extras). The Vars are the *outer-fn* Vars (used by callers when
    /// constructing the TailCall args into this fn).
    outer_captured: Vec<(String, Var)>,
    span: Span,
    /// fz-f88.5 — origin tag baked in at mint time.
    category: crate::fz_ir::FnCategory,
}

/// Mint a fresh continuation FnId, snapshot the outer env at this point,
/// and record the span for diagnostics. The builder is created lazily by
/// `switch_to_cont_fn`.
fn mint_cont_fn(
    ctx: &mut LowerCtx,
    name: impl Into<String>,
    span: Span,
    category: crate::fz_ir::FnCategory,
) -> ContFn {
    let id = ctx.mb.fresh_fn_id();
    ctx.fn_spans.insert(id, span);
    ContFn {
        id,
        name: name.into(),
        outer_captured: ctx.captured_snapshot(),
        span,
        category,
    }
}

/// Finalize ctx.cur (adding it to the module) and switch into a fresh
/// builder for `cont`. Allocates an entry block with params:
/// `[extras..., captured...]`. Returns the Vars for the extras (for a
/// per-arm fn there are 0 extras; for a join fn the single extra is the
/// joined value the arms passed in). The env is rebound from
/// `cont.outer_captured`'s names to the fresh captured-param Vars in the
/// new fn.
fn switch_to_cont_fn(ctx: &mut LowerCtx, cont: &ContFn, extra_param_count: usize) -> Vec<Var> {
    // Finalize current fn.
    let done = ctx
        .cur
        .take()
        .expect("switch_to_cont_fn: no current fn")
        .build();
    ctx.mb.add_fn(done);

    // Build new fn.
    let mut kbuilder = FnBuilder::new(cont.id, cont.name.clone()).with_category(cont.category);

    // Entry params: extras (e.g. join_param) first, then captured renames.
    let extras: Vec<Var> = (0..extra_param_count)
        .map(|_| kbuilder.fresh_var())
        .collect();
    let cap_params: Vec<Var> = cont
        .outer_captured
        .iter()
        .map(|_| kbuilder.fresh_var())
        .collect();
    let mut entry_params = extras.clone();
    entry_params.extend(cap_params.clone());
    let entry = kbuilder.block(entry_params);

    ctx.cur = Some(kbuilder);
    ctx.cur_fn_id = Some(cont.id);
    ctx.cur_block = Some(entry);
    ctx.terminated = false;

    // Var meta for extras + captured renames so diagnostics can attribute
    // them to the construct's span.
    for v in &extras {
        ctx.var_meta
            .insert((cont.id, *v), (cont.span, String::new()));
    }
    for v in &cap_params {
        ctx.var_meta
            .insert((cont.id, *v), (cont.span, String::new()));
    }

    // Rebind env: clear, then map each captured name to its new param Var.
    ctx.env.clear();
    ctx.env_order.clear();
    for ((name, _outer_v), nv) in cont.outer_captured.iter().zip(&cap_params) {
        ctx.bind(name, *nv);
    }

    extras
}

/// At the end of an arm's body, emit the appropriate terminator.
///
/// - If the arm self-terminated (Return / Halt / inner TailCall),
///   `ctx.terminated` is already true: emit nothing.
/// - If `join` is `Some`, emit `TailCall(join.id, [arm_value, ...captured])`.
///   Captured Vars are re-resolved from `ctx.env` at *this* moment because
///   ctx.cur may have changed (via internal CPS-splits) since the arm
///   started — the captured names point to the current fn's Vars now.
/// - If `join` is `None` (tail position), emit `Return(arm_value)`.
///
/// Sets `ctx.terminated = true` after emission.
fn finalize_arm(ctx: &mut LowerCtx, arm_value: Var, join: Option<&ContFn>) {
    if ctx.terminated {
        return;
    }
    if let Some(join) = join {
        let mut tail_args = Vec::with_capacity(1 + join.outer_captured.len());
        tail_args.push(arm_value);
        for (name, _outer_v) in &join.outer_captured {
            let v = ctx.env.get(name).copied().unwrap_or_else(|| {
                panic!(
                    "finalize_arm: captured name `{}` not in env at arm-end",
                    name
                )
            });
            tail_args.push(v);
        }
        ctx.set_term(Term::TailCall {
            ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
            callee: join.id,
            args: tail_args,
            is_back_edge: false,
        });
    } else {
        ctx.set_term(Term::Return(arm_value));
    }
    ctx.terminated = true;
}

fn lower_if(
    ctx: &mut LowerCtx,
    cond: &Spanned<Expr>,
    then_e: &Spanned<Expr>,
    else_opt: &Option<Box<Spanned<Expr>>>,
    is_tail: bool,
    if_span: Span,
) -> Result<Var, LowerError> {
    // fz-duq.2 — Per-arm + (optional) join continuation fns, mirroring
    // the CPS-split protocol from `cps_split_call`. The old block-join
    // design corrupted control flow whenever an arm body contained a
    // non-tail Call (Bug 2) and clobbered self-terminated arms with a
    // Goto-to-join carrying the sentinel Var(0) (Bug 1).
    //
    // Shape (non-tail):
    //   outer fn   : ... ; Term::If(cv, then_b, else_b)
    //   outer.then_b: TailCall(then_fn, [...captures])
    //   outer.else_b: TailCall(else_fn, [...captures])
    //   then_fn     : lower(then_e, is_tail=true) ;
    //                 finalize → TailCall(join_fn, [v, ...captures])
    //   else_fn     : lower(else_e, is_tail=true) ;
    //                 finalize → TailCall(join_fn, [v, ...captures])
    //   join_fn     : becomes ctx.cur. param `join_param` carries the
    //                 if's value. Surrounding code continues here.
    //
    // Shape (tail):
    //   same as above, but no join_fn; arms finalize via Return(v).
    //   ctx.terminated = true on return; ctx.cur is else_fn (or its
    //   inner-CPS-split descendant) — surrounding lower_fn finalizes it.
    //
    // The inliner (`inline_tail_calls_once`) collapses the tiny per-arm
    // and join fns post-IR-build; for non-CPS-splitting arms the
    // final CLIF matches today's block-join shape (often tighter — no
    // join block at all).

    let cv = lower_expr(ctx, cond, false)?;

    let then_cont = mint_cont_fn(
        ctx,
        "if_then",
        if_span,
        crate::fz_ir::FnCategory::ControlFlowCont,
    );
    let else_cont = mint_cont_fn(
        ctx,
        "if_else",
        if_span,
        crate::fz_ir::FnCategory::ControlFlowCont,
    );
    let join_opt = if is_tail {
        None
    } else {
        Some(mint_cont_fn(
            ctx,
            "if_join",
            if_span,
            crate::fz_ir::FnCategory::ControlFlowCont,
        ))
    };

    // Allocate arm blocks in the outer (current) fn.
    let then_b = ctx.cur_mut().block(vec![]);
    let else_b = ctx.cur_mut().block(vec![]);
    ctx.set_if_term(cv, then_b, else_b);

    // Wire each arm block: TailCall its arm fn with the outer captures.
    // Captures are snapshotted from the outer env *now*; they're the
    // same set we passed to `mint_cont_fn` for then_cont/else_cont/join_opt
    // (which all snapshot identical envs at this moment).
    let captures = ctx.captured_snapshot();
    let capture_vars: Vec<Var> = captures.iter().map(|(_, v)| *v).collect();

    ctx.cur_block = Some(then_b);
    ctx.set_term(Term::TailCall {
        ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
        callee: then_cont.id,
        args: capture_vars.clone(),
        is_back_edge: false,
    });
    ctx.cur_block = Some(else_b);
    ctx.set_term(Term::TailCall {
        ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
        callee: else_cont.id,
        args: capture_vars,
        is_back_edge: false,
    });

    // Move to then_fn. Finalizes the outer fn (which is now fully populated).
    let _ = switch_to_cont_fn(ctx, &then_cont, 0);
    let tv = lower_expr(ctx, then_e, /* is_tail */ true)?;
    finalize_arm(ctx, tv, join_opt.as_ref());

    // Move to else_fn. Finalizes then_fn (or its CPS-split descendant).
    let _ = switch_to_cont_fn(ctx, &else_cont, 0);
    let ev = if let Some(else_e) = else_opt {
        lower_expr(ctx, else_e, /* is_tail */ true)?
    } else {
        ctx.let_(Prim::Const(Const::Nil))
    };
    finalize_arm(ctx, ev, join_opt.as_ref());

    if let Some(join) = &join_opt {
        // Non-tail: finalize else_fn, switch into join_fn. Surrounding
        // code continues lowering into join_fn with `join_param` as the
        // if's value.
        let extras = switch_to_cont_fn(ctx, join, 1);
        Ok(extras[0])
    } else {
        // Tail position: both arms finalized via Return. ctx.cur is
        // else_fn (or a downstream CPS-split cont). Caller will finalize
        // it via `ctx.cur.take().build()`.
        ctx.terminated = true;
        Ok(Var(0))
    }
}

fn lower_lambda(
    ctx: &mut LowerCtx,
    params: &[Spanned<Pattern>],
    body: &Spanned<Expr>,
    span: Span,
) -> Result<Var, LowerError> {
    // Capture all in-scope locals.
    let captured = ctx.captured_snapshot();
    let captured_vars: Vec<Var> = captured.iter().map(|(_, v)| *v).collect();

    // Mint a fresh fn for the lambda.
    let lam_id = ctx.mb.fresh_fn_id();

    // Save current state and switch to building the lambda fn.
    let saved_cur = ctx.cur.take();
    let saved_block = ctx.cur_block.take();
    let saved_env = std::mem::take(&mut ctx.env);
    let saved_order = std::mem::take(&mut ctx.env_order);

    let mut lam_builder = FnBuilder::new(lam_id, format!("lambda_{}", lam_id.0))
        .with_category(crate::fz_ir::FnCategory::LambdaLift);
    // Entry params = captured + lambda params.
    let cap_params: Vec<Var> = captured.iter().map(|_| lam_builder.fresh_var()).collect();
    let lam_param_vars: Vec<Var> = params.iter().map(|_| lam_builder.fresh_var()).collect();
    let mut entry_params = cap_params.clone();
    entry_params.extend(lam_param_vars.clone());
    let lam_entry = lam_builder.block(entry_params);

    ctx.cur = Some(lam_builder);
    ctx.cur_block = Some(lam_entry);
    // Bind captured + params in env.
    for ((name, _), nv) in captured.iter().zip(&cap_params) {
        ctx.bind(name, *nv);
    }
    // Seal fail_block FIRST so CPS-split during body lowering can't orphan it.
    let fail_block = ctx.cur_mut().block(vec![]);
    ctx.cur_block = Some(fail_block);
    let me = ctx.atoms.intern("match_error");
    let mev = ctx.let_(Prim::Const(Const::Atom(me)));
    ctx.set_term(Term::Halt(mev));
    ctx.cur_block = Some(lam_entry);

    ctx.terminated = false;
    for (pv, pat) in lam_param_vars.iter().zip(params) {
        lower_pattern_bind(ctx, *pv, pat, fail_block)?;
    }
    let result = lower_expr(ctx, body, true)?;
    if !ctx.terminated {
        ctx.set_term(Term::Return(result));
    }

    let lam_fn = ctx.cur.take().unwrap().build();
    ctx.mb.add_fn(lam_fn);

    // Restore caller state.
    ctx.cur = saved_cur;
    ctx.cur_block = saved_block;
    ctx.env = saved_env;
    ctx.env_order = saved_order;

    Ok(ctx.let_at(Prim::make_closure(span, lam_id, captured_vars), span))
}

fn cps_split_call_closure(
    ctx: &mut LowerCtx,
    closure_var: Var,
    arg_vars: Vec<Var>,
    call_span: Span,
) -> Result<Var, LowerError> {
    let captured = ctx.captured_snapshot();
    let captured_vars: Vec<Var> = captured.iter().map(|(_, v)| *v).collect();
    let cont_id = ctx.mb.fresh_fn_id();

    ctx.set_term_at(
        Term::CallClosure {
            ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
            closure: closure_var,
            args: arg_vars,
            continuation: Cont {
                fn_id: cont_id,
                captured: captured_vars.clone(),
            },
        },
        call_span,
    );

    let done = ctx.cur.take().unwrap().build();
    ctx.mb.add_fn(done);

    let mut kbuilder = FnBuilder::new(cont_id, format!("k_{}", cont_id.0))
        .with_category(crate::fz_ir::FnCategory::CpsCont);
    let result_param = kbuilder.fresh_var();
    let cap_params: Vec<Var> = captured.iter().map(|_| kbuilder.fresh_var()).collect();
    let mut params = vec![result_param];
    params.extend(cap_params.clone());
    let entry = kbuilder.block(params);
    ctx.cur = Some(kbuilder);
    ctx.cur_fn_id = Some(cont_id);
    ctx.fn_spans.insert(cont_id, call_span);
    // Result-slot Var inherits the call's span (it's the value the call returns).
    ctx.var_meta
        .insert((cont_id, result_param), (call_span, String::new()));
    ctx.cur_block = Some(entry);

    ctx.env.clear();
    ctx.env_order.clear();
    for ((name, _), nv) in captured.iter().zip(&cap_params) {
        ctx.bind(name, *nv);
    }
    Ok(result_param)
}

/// fz-ul4.19.3: lower a source-level `receive()` into Term::Receive,
/// mirroring cps_split_call's continuation-building. The continuation
/// receives one arg (the message) plus captured Vars.
///
/// For tail position (the source `receive()` is the last expression in a
/// fn), the cont synthesizes `Return(msg)` so the message becomes the
/// fn's return value. Otherwise the cont becomes a normal continuation
/// that's resumed with the message bound to a Var.
fn cps_split_receive(
    ctx: &mut LowerCtx,
    call_span: Span,
    is_tail: bool,
) -> Result<Var, LowerError> {
    let captured = ctx.captured_snapshot();
    let captured_vars: Vec<Var> = captured.iter().map(|(_, v)| *v).collect();
    let cont_id = ctx.mb.fresh_fn_id();

    // Terminate current block with Term::Receive.
    ctx.set_term_at(
        Term::Receive {
            ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
            continuation: Cont {
                fn_id: cont_id,
                captured: captured_vars.clone(),
            },
        },
        call_span,
    );

    // Finalize current fn.
    let done = ctx.cur.take().unwrap().build();
    ctx.mb.add_fn(done);

    // Build the continuation fn. Same shape as cps_split_call's cont:
    // entry params = [result_param, captured...].
    let mut kbuilder = FnBuilder::new(cont_id, format!("k_receive_{}", cont_id.0))
        .with_category(crate::fz_ir::FnCategory::CpsCont);
    let result_param = kbuilder.fresh_var();
    let cap_params: Vec<Var> = captured.iter().map(|_| kbuilder.fresh_var()).collect();
    let mut params = vec![result_param];
    params.extend(cap_params.clone());
    let entry = kbuilder.block(params);
    ctx.cur = Some(kbuilder);
    ctx.cur_fn_id = Some(cont_id);
    ctx.fn_spans.insert(cont_id, call_span);
    ctx.var_meta
        .insert((cont_id, result_param), (call_span, String::new()));
    ctx.cur_block = Some(entry);

    // Rebind env: each captured name -> its new param Var.
    ctx.env.clear();
    ctx.env_order.clear();
    for ((name, _), nv) in captured.iter().zip(&cap_params) {
        ctx.bind(name, *nv);
    }
    if is_tail {
        // Tail receive: synthesize `Return(msg)` immediately. The cont
        // fn IS the post-receive fn for the parent; in tail position we
        // just return the message.
        ctx.set_term_at(Term::Return(result_param), call_span);
        ctx.terminated = true;
    }
    Ok(result_param)
}

/// fz-yxs — collect the names a pattern would bind, in source-traversal
/// order. Mirrors `collect_one` but emits only the names; the matcher
/// (B3) consumes the same source pattern AST and lines its extracted
/// slots up with this same order, so each clause body fn's first
/// `bound_names.len()` params receive the bound values positionally.
fn collect_pattern_bound_names(p: &Pattern, out: &mut Vec<String>) {
    match p {
        Pattern::Wildcard
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Binary(_)
        | Pattern::Atom(_)
        | Pattern::Bool(_)
        | Pattern::Nil
        | Pattern::Pinned(_) => {}
        Pattern::Var(name) => out.push(name.clone()),
        Pattern::As(name, inner) => {
            out.push(name.clone());
            collect_pattern_bound_names(&inner.node, out);
        }
        Pattern::Tuple(elems) => {
            for e in elems {
                collect_pattern_bound_names(&e.node, out);
            }
        }
        Pattern::List(elems, tail) => {
            for e in elems {
                collect_pattern_bound_names(&e.node, out);
            }
            if let Some(t) = tail {
                collect_pattern_bound_names(&t.node, out);
            }
        }
        Pattern::Map(entries) => {
            for (_k, v) in entries {
                collect_pattern_bound_names(&v.node, out);
            }
        }
        Pattern::Bitstring(fields) => {
            for field in fields {
                collect_pattern_bound_names(&field.value.node, out);
            }
        }
    }
}

/// fz-yxs — collect every `^name` reference appearing in a pattern.
fn collect_pattern_pinned_names(p: &Pattern, out: &mut Vec<String>) {
    match p {
        Pattern::Pinned(name) => out.push(name.clone()),
        Pattern::Wildcard
        | Pattern::Var(_)
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Binary(_)
        | Pattern::Atom(_)
        | Pattern::Bool(_)
        | Pattern::Nil => {}
        Pattern::As(_, inner) => collect_pattern_pinned_names(&inner.node, out),
        Pattern::Tuple(elems) => {
            for e in elems {
                collect_pattern_pinned_names(&e.node, out);
            }
        }
        Pattern::List(elems, tail) => {
            for e in elems {
                collect_pattern_pinned_names(&e.node, out);
            }
            if let Some(t) = tail {
                collect_pattern_pinned_names(&t.node, out);
            }
        }
        Pattern::Map(entries) => {
            for (k, v) in entries {
                collect_pattern_pinned_names(&k.node, out);
                collect_pattern_pinned_names(&v.node, out);
            }
        }
        Pattern::Bitstring(fields) => {
            for field in fields {
                collect_pattern_pinned_names(&field.value.node, out);
            }
        }
    }
}

fn lower_guard_helper_call_to_dispatch(
    ctx: &LowerCtx,
    name: &str,
    arity: usize,
    args: Vec<crate::matcher::GuardExpr>,
    stack: &mut Vec<(String, usize)>,
) -> Result<Option<crate::matcher::GuardExpr>, crate::pattern_matrix::MatcherCompileError> {
    let key = (name.to_string(), arity);
    let Some(fn_def) = ctx.fn_defs_by_arity.get(&key) else {
        return Ok(None);
    };
    if stack.contains(&key) {
        return Err(crate::pattern_matrix::MatcherCompileError::GuardCallCycle(
            key.0, key.1,
        ));
    }
    if fn_def.clauses.is_empty() {
        return Ok(None);
    }
    if fn_def
        .clauses
        .iter()
        .any(|clause| clause.params.len() != arity)
    {
        return Ok(None);
    }

    stack.push(key);
    let subjects: Vec<crate::fz_ir::Var> =
        (0..arity).map(|i| crate::fz_ir::Var(i as u32)).collect();
    let matrix = crate::pattern_matrix::Matrix {
        subjects: subjects.clone(),
        rows: fn_def
            .clauses
            .iter()
            .enumerate()
            .map(|(i, clause)| crate::pattern_matrix::Row {
                patterns: clause.params.clone(),
                preconditions: Vec::new(),
                bindings: Vec::new(),
                guard: clause.guard.clone(),
                body_id: i as crate::pattern_matrix::BodyId,
            })
            .collect(),
    };
    let mut resolver =
        |callee: &str, callee_arity: usize, callee_args: Vec<crate::matcher::GuardExpr>| {
            lower_guard_helper_call_to_dispatch(ctx, callee, callee_arity, callee_args, stack)
        };
    let matcher_result =
        crate::pattern_matrix::compile_matcher_subset_with_guard_resolver(matrix, &mut resolver);
    stack.pop();
    let mut matcher = matcher_result?;
    let param_input_by_name: HashMap<String, crate::fz_ir::Var> = fn_def.clauses[0]
        .params
        .iter()
        .enumerate()
        .filter_map(|(i, pattern)| match &pattern.node {
            crate::ast::Pattern::Var(name) => Some((name.clone(), crate::fz_ir::Var(i as u32))),
            _ => None,
        })
        .collect();
    for pinned in &mut matcher.pinned {
        if let Some(input) = param_input_by_name.get(&pinned.name) {
            pinned.var = Some(*input);
        }
    }

    let mut pinned_by_name: HashMap<String, crate::matcher::PinnedId> = matcher
        .pinned
        .iter()
        .enumerate()
        .map(|(i, pinned)| (pinned.name.clone(), crate::matcher::PinnedId(i as u32)))
        .collect();
    for clause in &fn_def.clauses {
        let mut bound = std::collections::BTreeSet::new();
        for pattern in &clause.params {
            let mut names = Vec::new();
            collect_pattern_bound_names(&pattern.node, &mut names);
            bound.extend(names);
        }
        let mut captures = Vec::new();
        crate::pattern_matrix::collect_guard_capture_names(
            &clause.body.node,
            &bound,
            &mut captures,
        );
        for capture in captures {
            if !pinned_by_name.contains_key(&capture) {
                let id = crate::matcher::PinnedId(matcher.pinned.len() as u32);
                matcher.pinned.push(crate::matcher::PinnedInput {
                    name: capture.clone(),
                    var: None,
                    span: clause.body.span,
                });
                pinned_by_name.insert(capture, id);
            }
        }
    }

    let mut bodies = Vec::with_capacity(fn_def.clauses.len());
    for clause in &fn_def.clauses {
        let bindings = crate::pattern_matrix::collect_matcher_pattern_bindings(
            &clause.params,
            &pinned_by_name,
        )?;
        let mut resolver =
            |callee: &str, callee_arity: usize, callee_args: Vec<crate::matcher::GuardExpr>| {
                lower_guard_helper_call_to_dispatch(ctx, callee, callee_arity, callee_args, stack)
            };
        bodies.push(crate::pattern_matrix::compile_guard_expr_subset(
            &clause.body.node,
            &bindings,
            &pinned_by_name,
            &mut resolver,
        )?);
    }

    Ok(Some(crate::matcher::GuardExpr::Dispatch {
        inputs: args,
        dispatch: Box::new(crate::matcher::GuardDispatch { matcher, bodies }),
    }))
}

fn collect_matcher_pinned_names_recursive(
    matcher: &crate::matcher::Matcher,
    out: &mut Vec<String>,
) {
    for pinned in &matcher.pinned {
        if pinned.var.is_some() {
            continue;
        }
        if !out.contains(&pinned.name) {
            out.push(pinned.name.clone());
        }
    }
    for node in &matcher.nodes {
        if let crate::matcher::MatcherNode::Guard { expr, .. } = node {
            collect_guard_expr_dispatch_pinned(expr, out);
        }
    }
}

fn collect_guard_expr_dispatch_pinned(expr: &crate::matcher::GuardExpr, out: &mut Vec<String>) {
    match expr {
        crate::matcher::GuardExpr::Unary { expr, .. } => {
            collect_guard_expr_dispatch_pinned(expr, out);
        }
        crate::matcher::GuardExpr::Binary { lhs, rhs, .. } => {
            collect_guard_expr_dispatch_pinned(lhs, out);
            collect_guard_expr_dispatch_pinned(rhs, out);
        }
        crate::matcher::GuardExpr::Dispatch { inputs, dispatch } => {
            for input in inputs {
                collect_guard_expr_dispatch_pinned(input, out);
            }
            collect_matcher_pinned_names_recursive(&dispatch.matcher, out);
            for body in &dispatch.bodies {
                collect_guard_expr_dispatch_pinned(body, out);
            }
        }
        crate::matcher::GuardExpr::Const(_)
        | crate::matcher::GuardExpr::Subject(_)
        | crate::matcher::GuardExpr::Pinned(_) => {}
    }
}

fn materialize_prepared_matcher_key(
    ctx: &mut LowerCtx,
    key: &crate::matcher::MatcherConst,
) -> Result<Var, LowerError> {
    match key {
        crate::matcher::MatcherConst::FloatBits(bits) => {
            Ok(ctx.let_(Prim::Const(Const::Float(f64::from_bits(*bits)))))
        }
        crate::matcher::MatcherConst::Utf8Binary(bytes) => {
            let bit_len = (bytes.len() * 8) as u64;
            let bs = ctx.let_(Prim::ConstBitstring(bytes.clone(), bit_len));
            Ok(ctx.let_(Prim::Brand(bs, "utf8".to_string())))
        }
        crate::matcher::MatcherConst::AtomName(name) => {
            let atom = ctx.atoms.intern(name);
            Ok(ctx.let_(Prim::Const(Const::Atom(atom))))
        }
        crate::matcher::MatcherConst::Int(n) => Ok(ctx.let_(Prim::Const(Const::Int(*n)))),
        crate::matcher::MatcherConst::Bool(true) => Ok(ctx.let_(Prim::Const(Const::True))),
        crate::matcher::MatcherConst::Bool(false) => Ok(ctx.let_(Prim::Const(Const::False))),
        crate::matcher::MatcherConst::Nil => Ok(ctx.let_(Prim::Const(Const::Nil))),
        crate::matcher::MatcherConst::EmptyList | crate::matcher::MatcherConst::PreparedKey(_) => {
            Err(LowerError::Unsupported {
                span: Span::DUMMY,
                what: format!("matcher prepared key {:?} cannot be materialized", key),
            })
        }
    }
}

/// fz-puj.36 (H7) — build a degenerate (N=1) Matrix from receive clauses.
///
/// The Matrix subject is a single Var representing the candidate message.
/// Each clause produces one Row with `patterns: vec![clause.pattern]`,
/// `preconditions: []`, `guard: clause.guard`, and a caller-supplied
/// `body_id`. Captures/pinned threading is unchanged from receive's
/// existing wiring — those are not Matrix concerns.
///
/// The Matrix itself accepts arbitrary patterns; lowering turns it into a
/// cached AST-free Matcher before any receive probe executes.
fn build_receive_matrix(
    msg_var: Var,
    clauses: &[crate::ast::MatchClause],
) -> crate::pattern_matrix::Matrix {
    crate::pattern_matrix::Matrix {
        subjects: vec![msg_var],
        rows: clauses
            .iter()
            .enumerate()
            .map(|(i, c)| crate::pattern_matrix::Row {
                patterns: vec![c.pattern.clone()],
                preconditions: Vec::new(),
                bindings: Vec::new(),
                guard: c.guard.clone(),
                body_id: i as crate::pattern_matrix::BodyId,
            })
            .collect(),
    }
}

fn lower_receive(
    ctx: &mut LowerCtx,
    clauses: &[MatchClause],
    after: Option<&crate::ast::AfterClause>,
    is_tail: bool,
    rx_span: Span,
) -> Result<Var, LowerError> {
    if clauses.is_empty() && after.is_none() {
        return Err(LowerError::Unsupported {
            span: rx_span,
            what: "receive with no clauses and no after".into(),
        });
    }

    // After's timeout is lowered into the caller fn first because a
    // non-tail Call inside the timeout expression CPS-splits the current
    // fn — every Var snapshot that follows must come from the post-split
    // env so they belong to the right fn.
    let timeout_var = match after {
        Some(a) => Some(lower_expr(ctx, &a.timeout, false)?),
        None => None,
    };

    // Resolve `^name` references against the (possibly post-CPS-split)
    // outer scope. Dedupe by name; preserve first-seen order so backends
    // see a stable layout.
    let mut seen_pinned: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut pinned: Vec<(String, Var)> = Vec::new();
    for clause in clauses {
        let mut names: Vec<String> = Vec::new();
        collect_pattern_pinned_names(&clause.pattern.node, &mut names);
        if let Some(guard) = &clause.guard {
            let mut bound = std::collections::BTreeSet::new();
            let mut bound_names = Vec::new();
            collect_pattern_bound_names(&clause.pattern.node, &mut bound_names);
            for name in bound_names {
                bound.insert(name);
            }
            crate::pattern_matrix::collect_guard_capture_names(&guard.node, &bound, &mut names);
        }
        for name in names {
            if !seen_pinned.insert(name.clone()) {
                continue;
            }
            let v = ctx
                .env
                .get(&name)
                .copied()
                .ok_or_else(|| LowerError::Unbound {
                    span: clause.pattern.span,
                    name: format!("^{}", name),
                })?;
            pinned.push((name, v));
        }
    }

    // Join cont (post-receive code resumes here); skipped in tail position.
    let join_opt = if is_tail {
        None
    } else {
        Some(mint_cont_fn(
            ctx,
            "receive_join",
            rx_span,
            crate::fz_ir::FnCategory::ControlFlowCont,
        ))
    };

    // Mint per-clause body / guard fns, and the after body fn.
    struct ClauseSlots {
        bound_names: Vec<String>,
        body: ContFn,
        guard: Option<ContFn>,
    }
    let mut clause_slots: Vec<ClauseSlots> = Vec::with_capacity(clauses.len());
    for (i, clause) in clauses.iter().enumerate() {
        let mut bound_names: Vec<String> = Vec::new();
        collect_pattern_bound_names(&clause.pattern.node, &mut bound_names);
        let body = mint_cont_fn(
            ctx,
            format!("rx_clause_{}_body", i),
            clause.span,
            crate::fz_ir::FnCategory::ControlFlowCont,
        );
        let guard = if clause.guard.is_some() {
            Some(mint_cont_fn(
                ctx,
                format!("rx_clause_{}_guard", i),
                clause.span,
                crate::fz_ir::FnCategory::ControlFlowCont,
            ))
        } else {
            None
        };
        clause_slots.push(ClauseSlots {
            bound_names,
            body,
            guard,
        });
    }

    let after_slot: Option<(ContFn, &crate::ast::AfterClause)> = after.map(|a| {
        let body = mint_cont_fn(
            ctx,
            "rx_after_body",
            a.span,
            crate::fz_ir::FnCategory::ControlFlowCont,
        );
        (body, a)
    });

    // Captures: outer-scope vars threaded into every body/guard/after fn.
    // Snapshot once here; every mint_cont_fn above took the same snapshot
    // (env hasn't changed between mints), so the body fns' capture-param
    // shapes match this list.
    let captures_snap = ctx.captured_snapshot();
    let captures_vars: Vec<Var> = captures_snap.iter().map(|(_, v)| *v).collect();

    // Build the IR clauses now that we have all the FnIds.
    let ir_clauses: Vec<crate::fz_ir::ReceiveClause> = clauses
        .iter()
        .zip(clause_slots.iter())
        .map(|(c, slot)| crate::fz_ir::ReceiveClause {
            bound_names: slot.bound_names.clone(),
            guard: slot.guard.as_ref().map(|g| g.id),
            body: slot.body.id,
            span: c.span,
        })
        .collect();

    let ir_after = after_slot
        .as_ref()
        .map(|(cont, a)| crate::fz_ir::ReceiveAfter {
            timeout: timeout_var.expect("timeout lowered when after is Some"),
            body: cont.id,
            span: a.span,
        });
    let receive_matrix = build_receive_matrix(crate::fz_ir::Var(0), clauses);
    let mut guard_stack = Vec::new();
    let mut guard_resolver = |name: &str, arity: usize, args: Vec<crate::matcher::GuardExpr>| {
        lower_guard_helper_call_to_dispatch(ctx, name, arity, args, &mut guard_stack)
    };
    let receive_matcher = crate::pattern_matrix::compile_matcher_subset_with_guard_resolver(
        receive_matrix,
        &mut guard_resolver,
    )
    .map_err(|err| LowerError::Unsupported {
        span: rx_span,
        what: format!("receive matcher cannot be lowered: {:?}", err),
    })
    .map(std::sync::Arc::new)?;
    for (index, key) in receive_matcher.prepared_keys.iter().enumerate() {
        let name = crate::matcher::prepared_key_name(index);
        if !seen_pinned.insert(name.clone()) {
            continue;
        }
        let v = materialize_prepared_matcher_key(ctx, key)?;
        pinned.push((name, v));
    }
    let mut matcher_pinned = Vec::new();
    collect_matcher_pinned_names_recursive(&receive_matcher, &mut matcher_pinned);
    for name in matcher_pinned {
        if !seen_pinned.insert(name.clone()) {
            continue;
        }
        let v = ctx
            .env
            .get(&name)
            .copied()
            .ok_or_else(|| LowerError::Unbound {
                span: rx_span,
                name: format!("^{}", name),
            })?;
        pinned.push((name, v));
    }

    // Terminate the caller fn's current block with the ReceiveMatched.
    ctx.set_term_at(
        Term::ReceiveMatched {
            ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
            clauses: ir_clauses,
            matcher: receive_matcher,
            after: ir_after,
            pinned,
            captures: captures_vars,
        },
        rx_span,
    );

    // Lower each clause body (and any guard) into its own fn. `switch_to_
    // cont_fn` finalises the previously-current fn and switches into the
    // newly-named one; calling it in sequence chains the build-finalise
    // pattern through every body fn.
    let clauses_iter = clauses.iter().zip(clause_slots);
    for (clause, slot) in clauses_iter {
        if let Some(g_cont) = &slot.guard {
            let extras = switch_to_cont_fn(ctx, g_cont, slot.bound_names.len());
            for (name, &v) in slot.bound_names.iter().zip(extras.iter()) {
                ctx.bind(name, v);
            }
            let g_val = lower_expr(
                ctx,
                clause
                    .guard
                    .as_ref()
                    .expect("guard cont implies guard expr"),
                /* is_tail */ true,
            )?;
            // Guards return their value to the matcher caller (B3 will
            // synthesise the dispatch). Use Term::Return so the value
            // appears as the guard fn's result.
            if !ctx.terminated {
                ctx.set_term_at(Term::Return(g_val), clause.span);
                ctx.terminated = true;
            }
        }

        let extras = switch_to_cont_fn(ctx, &slot.body, slot.bound_names.len());
        for (name, &v) in slot.bound_names.iter().zip(extras.iter()) {
            ctx.bind(name, v);
        }
        let result = lower_expr(ctx, &clause.body, /* is_tail */ true)?;
        finalize_arm(ctx, result, join_opt.as_ref());
    }

    if let Some((cont, a)) = after_slot {
        let _extras = switch_to_cont_fn(ctx, &cont, 0);
        let result = lower_expr(ctx, &a.body, /* is_tail */ true)?;
        finalize_arm(ctx, result, join_opt.as_ref());
    }

    if let Some(join) = &join_opt {
        let extras = switch_to_cont_fn(ctx, join, 1);
        Ok(extras[0])
    } else {
        ctx.terminated = true;
        Ok(Var(0))
    }
}

fn cps_split_call(
    ctx: &mut LowerCtx,
    callee: FnId,
    arg_vars: Vec<Var>,
    call_span: Span,
) -> Result<Var, LowerError> {
    let captured = ctx.captured_snapshot();
    let captured_vars: Vec<Var> = captured.iter().map(|(_, v)| *v).collect();
    let cont_id = ctx.mb.fresh_fn_id();

    // Terminate current block with the call.
    ctx.set_term_at(
        Term::Call {
            ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
            callee,
            args: arg_vars,
            continuation: Cont {
                fn_id: cont_id,
                captured: captured_vars.clone(),
            },
        },
        call_span,
    );

    // Finalize current fn.
    let done = ctx.cur.take().unwrap().build();
    ctx.mb.add_fn(done);

    // Start the continuation fn.
    let mut kbuilder = FnBuilder::new(cont_id, format!("k_{}", cont_id.0))
        .with_category(crate::fz_ir::FnCategory::CpsCont);
    let result_param = kbuilder.fresh_var();
    let cap_params: Vec<Var> = captured.iter().map(|_| kbuilder.fresh_var()).collect();
    let mut params = vec![result_param];
    params.extend(cap_params.clone());
    let entry = kbuilder.block(params);
    ctx.cur = Some(kbuilder);
    ctx.cur_fn_id = Some(cont_id);
    ctx.fn_spans.insert(cont_id, call_span);
    ctx.var_meta
        .insert((cont_id, result_param), (call_span, String::new()));
    ctx.cur_block = Some(entry);

    // Rebind env: each captured name -> its new param Var.
    ctx.env.clear();
    ctx.env_order.clear();
    for ((name, _), nv) in captured.iter().zip(&cap_params) {
        ctx.bind(name, *nv);
    }
    Ok(result_param)
}

/// Lower a sequence of subexpressions, parking each result in env so that any
/// CPS-split triggered by a later element rebinds the earlier results into the
/// continuation. Caller unparks/unbinds.
fn lower_seq(ctx: &mut LowerCtx, exprs: &[Spanned<Expr>]) -> Result<Vec<String>, LowerError> {
    let mut parks = Vec::with_capacity(exprs.len());
    for e in exprs {
        let v = lower_expr(ctx, e, false)?;
        parks.push(ctx.park(v));
    }
    Ok(parks)
}

fn lower_binop(op: AstBinOp, span: Span) -> Result<BinOp, LowerError> {
    Ok(match op {
        AstBinOp::Add => BinOp::Add,
        AstBinOp::Sub => BinOp::Sub,
        AstBinOp::Mul => BinOp::Mul,
        AstBinOp::Div => BinOp::Div,
        AstBinOp::Rem => BinOp::Mod,
        AstBinOp::Eq => BinOp::Eq,
        AstBinOp::Neq => BinOp::Neq,
        AstBinOp::Lt => BinOp::Lt,
        AstBinOp::LtEq => BinOp::Le,
        AstBinOp::Gt => BinOp::Gt,
        AstBinOp::GtEq => BinOp::Ge,
        AstBinOp::And => BinOp::And,
        AstBinOp::Or => BinOp::Or,
        AstBinOp::Pipe => {
            return Err(LowerError::Unsupported {
                span,
                what: "BinOp::Pipe should be desugared before lowering".into(),
            });
        }
        AstBinOp::Cons => {
            // a | b — handled at construction sites (List with tail).
            return Err(LowerError::Unsupported {
                span,
                what: "BinOp::Cons should be desugared into List with tail".into(),
            });
        }
    })
}

/// Lower a pattern that matches `subject_var`. On match failure, jump to
/// `fail_block`. After a successful match, the current block is "all matched
/// so far"; `lower_pattern_bind` may split into new blocks via If terminators.
fn lower_pattern_bind(
    ctx: &mut LowerCtx,
    subject: Var,
    spat: &Spanned<Pattern>,
    fail_block: BlockId,
) -> Result<(), LowerError> {
    let pat_span = spat.span;
    match &spat.node {
        Pattern::Wildcard => Ok(()),
        Pattern::Var(name) => {
            ctx.bind(name, subject);
            // Record `subject`'s source name + binding-site span so
            // diagnostics can render the user's identifier later.
            ctx.name_var(subject, name, pat_span);
            Ok(())
        }
        // fz-5vj — `^name` pinned pattern. Lowering lands in fz-yxs (E2)
        // alongside Term::ReceiveMatched. Outside `receive` the typer
        // should already have rejected `^name` per the receive-only
        // syntactic role; reaching here is a planning bug.
        Pattern::Pinned(name) => Err(LowerError::Unsupported {
            span: pat_span,
            what: format!("pinned pattern `^{}` lowering lands in fz-yxs (E2)", name),
        }),
        Pattern::Int(n) => emit_eq_check(ctx, subject, Prim::Const(Const::Int(*n)), fail_block),
        Pattern::Float(x) => emit_eq_check(ctx, subject, Prim::Const(Const::Float(*x)), fail_block),
        Pattern::Binary(bytes) => {
            // fz-axu.11 (L3) — quoted binary patterns lower the same as
            // Expr::Binary: utf8-branded const bitstring, equality-check
            // against the subject. UTF-8 validity is a lexer invariant.
            let bit_len = (bytes.len() * 8) as u64;
            let bs = ctx.let_(Prim::ConstBitstring(bytes.clone(), bit_len));
            let lit_v = ctx.let_(Prim::Brand(bs, "utf8".to_string()));
            let eq_v = ctx.let_(Prim::BinOp(BinOp::Eq, subject, lit_v));
            let cont_b = ctx.cur_mut().block(vec![]);
            ctx.set_if_term(eq_v, cont_b, fail_block);
            ctx.cur_block = Some(cont_b);
            Ok(())
        }
        Pattern::Atom(s) => {
            let id = ctx.atoms.intern(s);
            emit_eq_check(ctx, subject, Prim::Const(Const::Atom(id)), fail_block)
        }
        Pattern::Bool(true) => emit_eq_check(ctx, subject, Prim::Const(Const::True), fail_block),
        Pattern::Bool(false) => emit_eq_check(ctx, subject, Prim::Const(Const::False), fail_block),
        Pattern::Nil => emit_eq_check(ctx, subject, Prim::Const(Const::Nil), fail_block),
        Pattern::As(name, inner) => {
            ctx.bind(name, subject);
            ctx.name_var(subject, name, pat_span);
            lower_pattern_bind(ctx, subject, inner, fail_block)
        }
        Pattern::Tuple(elems) => match_tuple(ctx, subject, elems, fail_block),
        Pattern::List(elems, tail) => match_list(ctx, subject, elems, tail.as_deref(), fail_block),
        Pattern::Map(entries) => match_map(ctx, subject, entries, fail_block),
        Pattern::Bitstring(fields) => match_bitstring(ctx, subject, fields, fail_block),
    }
}

/// fz-ul4.43.H — Constructor pattern helpers. Each emits the IR for a
/// single subject against the constructor pattern. On match success, the
/// helper leaves ctx.cur_block at a "success" block where any bindings
/// from inner sub-patterns are in env and the caller continues lowering
/// inline. On match failure, control jumps to `fail_block` via Term::If
/// terminators along the way.
///
/// Shared by `lower_pattern_bind` and list-cons lowering.
fn match_tuple(
    ctx: &mut LowerCtx,
    subject: Var,
    elems: &[Spanned<Pattern>],
    fail_block: BlockId,
) -> Result<(), LowerError> {
    // fz-ben — TypeTest tuple-of-arity-N before projecting fields. For
    // non-tuple subjects (e.g. an atom flowing into `{:ok, x} <- :err`),
    // projection would read heap garbage without the type test gate.
    let n = elems.len();
    let tuple_ty = concrete_any_tuple(n);
    let test = ctx.let_(Prim::TypeTest(subject, Box::new(tuple_ty)));
    let project_b = ctx.cur_mut().block(vec![]);
    ctx.set_if_term(test, project_b, fail_block);
    ctx.cur_block = Some(project_b);
    for (i, elem_pat) in elems.iter().enumerate() {
        let fv = ctx.let_(Prim::TupleField(subject, i as u32));
        lower_pattern_bind(ctx, fv, elem_pat, fail_block)?;
    }
    Ok(())
}

fn match_list(
    ctx: &mut LowerCtx,
    subject: Var,
    elems: &[Spanned<Pattern>],
    tail: Option<&Spanned<Pattern>>,
    fail_block: BlockId,
) -> Result<(), LowerError> {
    let mut cur = subject;
    for elem_pat in elems {
        let isnil = ctx.let_(Prim::IsEmptyList(cur));
        let cont_b = ctx.cur_mut().block(vec![]);
        ctx.set_if_term(isnil, fail_block, cont_b);
        ctx.cur_block = Some(cont_b);
        let h = ctx.let_(Prim::ListHead(cur));
        let t = ctx.let_(Prim::ListTail(cur));
        lower_pattern_bind(ctx, h, elem_pat, fail_block)?;
        cur = t;
    }
    match tail {
        Some(tail_pat) => lower_pattern_bind(ctx, cur, tail_pat, fail_block),
        None => {
            // Must end with nil.
            let isnil = ctx.let_(Prim::IsEmptyList(cur));
            let cont_b = ctx.cur_mut().block(vec![]);
            ctx.set_if_term(isnil, cont_b, fail_block);
            ctx.cur_block = Some(cont_b);
            Ok(())
        }
    }
}

fn match_map(
    ctx: &mut LowerCtx,
    subject: Var,
    entries: &[(Spanned<Pattern>, Spanned<Pattern>)],
    fail_block: BlockId,
) -> Result<(), LowerError> {
    for (key_pat, val_pat) in entries {
        let key_var = lower_pattern_as_key_expr(ctx, key_pat)?;
        let got = ctx.let_(Prim::MapGet(subject, key_var));
        let nil_v = ctx.let_(Prim::Const(Const::Nil));
        let is_nil = ctx.let_(Prim::BinOp(BinOp::Eq, got, nil_v));
        let cont_b = ctx.cur_mut().block(vec![]);
        ctx.set_if_term(is_nil, fail_block, cont_b);
        ctx.cur_block = Some(cont_b);
        lower_pattern_bind(ctx, got, val_pat, fail_block)?;
    }
    Ok(())
}

fn match_bitstring(
    ctx: &mut LowerCtx,
    subject: Var,
    fields: &[AstBitField<Spanned<Pattern>>],
    fail_block: BlockId,
) -> Result<(), LowerError> {
    // Initialize a reader, then per field: read with size resolved against
    // any IR vars bound by EARLIER fields' patterns; check success;
    // pattern-bind the extracted value (which may bind names visible to
    // later fields' size resolution); thread the new reader. Finally
    // require the reader is fully consumed.
    let mut reader = ctx.let_(Prim::BitReaderInit(subject));
    let n = fields.len();
    for (i, field) in fields.iter().enumerate() {
        let is_last = i + 1 == n;
        let size_ir = lower_bit_size(ctx, &field.spec.size, field.value.span)?;
        let result = ctx.let_(Prim::BitReadField {
            reader,
            ty: field.spec.ty,
            size: size_ir,
            endian: field.spec.endian,
            signed: field.spec.signed,
            unit: field.spec.unit,
            is_last,
        });
        let ok = ctx.let_(Prim::TupleField(result, 0));
        let cont_b = ctx.cur_mut().block(vec![]);
        ctx.set_if_term(ok, cont_b, fail_block);
        ctx.cur_block = Some(cont_b);
        let extracted = ctx.let_(Prim::TupleField(result, 1));
        let next_reader = ctx.let_(Prim::TupleField(result, 2));
        // Park reader so any CPS-split inside the pattern keeps it.
        let r_park = ctx.park(next_reader);
        lower_pattern_bind(ctx, extracted, &field.value, fail_block)?;
        reader = ctx.unpark(&r_park);
        ctx.unbind(&r_park);
    }
    let done = ctx.let_(Prim::BitReaderDone(reader));
    let cont_b = ctx.cur_mut().block(vec![]);
    ctx.set_if_term(done, cont_b, fail_block);
    ctx.cur_block = Some(cont_b);
    Ok(())
}

/// Lower a Pattern that represents a map key. Map keys in patterns are
/// constants (atoms, ints, strings, ...) — no var-binding allowed.
fn lower_pattern_as_key_expr(ctx: &mut LowerCtx, sp: &Spanned<Pattern>) -> Result<Var, LowerError> {
    Ok(match &sp.node {
        Pattern::Int(n) => ctx.let_(Prim::Const(Const::Int(*n))),
        Pattern::Float(x) => ctx.let_(Prim::Const(Const::Float(*x))),
        Pattern::Binary(bytes) => {
            // fz-axu.11 (L3) — map-key pattern: same lowering as
            // Expr::Binary / Pattern::Binary. UTF-8 validity is a lexer
            // invariant (see read_quoted_binary_bytes in src/lexer.rs).
            let bit_len = (bytes.len() * 8) as u64;
            let bs = ctx.let_(Prim::ConstBitstring(bytes.clone(), bit_len));
            ctx.let_(Prim::Brand(bs, "utf8".to_string()))
        }
        Pattern::Atom(s) => {
            let id = ctx.atoms.intern(s);
            ctx.let_(Prim::Const(Const::Atom(id)))
        }
        Pattern::Bool(true) => ctx.let_(Prim::Const(Const::True)),
        Pattern::Bool(false) => ctx.let_(Prim::Const(Const::False)),
        Pattern::Nil => ctx.let_(Prim::Const(Const::Nil)),
        other => {
            return Err(LowerError::Unsupported {
                span: sp.span,
                what: format!(
                    "map-pattern keys must be constants, got {:?}",
                    std::mem::discriminant(other)
                ),
            });
        }
    })
}

fn lower_bit_size(
    ctx: &LowerCtx,
    size: &Option<AstBitSize>,
    span: Span,
) -> Result<Option<BitSizeIr>, LowerError> {
    Ok(match size {
        None => None,
        Some(AstBitSize::Literal(n)) => Some(BitSizeIr::Literal(*n)),
        Some(AstBitSize::Var(name)) => {
            let v = ctx.lookup(name).ok_or_else(|| LowerError::Unbound {
                span,
                name: format!("bit size var {}", name),
            })?;
            Some(BitSizeIr::Var(v))
        }
    })
}

fn emit_eq_check(
    ctx: &mut LowerCtx,
    subject: Var,
    lit: Prim,
    fail_block: BlockId,
) -> Result<(), LowerError> {
    let lit_v = ctx.let_(lit);
    let eq_v = ctx.let_(Prim::BinOp(BinOp::Eq, subject, lit_v));
    let cont_b = ctx.cur_mut().block(vec![]);
    ctx.set_if_term(eq_v, cont_b, fail_block);
    ctx.cur_block = Some(cont_b);
    Ok(())
}

// ----------------------------------------------------------------------
// Expression lowerings added in fz-ul4.11.17
// ----------------------------------------------------------------------

fn lower_map(
    ctx: &mut LowerCtx,
    entries: &[(Spanned<Expr>, Spanned<Expr>)],
) -> Result<Var, LowerError> {
    let mut key_parks = Vec::with_capacity(entries.len());
    let mut val_parks = Vec::with_capacity(entries.len());
    for (k, v) in entries {
        let kv = lower_expr(ctx, k, false)?;
        key_parks.push(ctx.park(kv));
        let vv = lower_expr(ctx, v, false)?;
        val_parks.push(ctx.park(vv));
    }
    let pairs: Vec<(Var, Var)> = key_parks
        .iter()
        .zip(val_parks.iter())
        .map(|(kn, vn)| (ctx.unpark(kn), ctx.unpark(vn)))
        .collect();
    for n in &key_parks {
        ctx.unbind(n);
    }
    for n in &val_parks {
        ctx.unbind(n);
    }
    Ok(ctx.let_(Prim::MakeMap(pairs)))
}

fn lower_map_update(
    ctx: &mut LowerCtx,
    base: &Spanned<Expr>,
    entries: &[(Spanned<Expr>, Spanned<Expr>)],
) -> Result<Var, LowerError> {
    let bv = lower_expr(ctx, base, false)?;
    let base_park = ctx.park(bv);
    let mut key_parks = Vec::with_capacity(entries.len());
    let mut val_parks = Vec::with_capacity(entries.len());
    for (k, v) in entries {
        let kv = lower_expr(ctx, k, false)?;
        key_parks.push(ctx.park(kv));
        let vv = lower_expr(ctx, v, false)?;
        val_parks.push(ctx.park(vv));
    }
    let base_v = ctx.unpark(&base_park);
    let pairs: Vec<(Var, Var)> = key_parks
        .iter()
        .zip(val_parks.iter())
        .map(|(kn, vn)| (ctx.unpark(kn), ctx.unpark(vn)))
        .collect();
    ctx.unbind(&base_park);
    for n in &key_parks {
        ctx.unbind(n);
    }
    for n in &val_parks {
        ctx.unbind(n);
    }
    Ok(ctx.let_(Prim::MapUpdate(base_v, pairs)))
}

fn lower_index(
    ctx: &mut LowerCtx,
    m: &Spanned<Expr>,
    k: &Spanned<Expr>,
) -> Result<Var, LowerError> {
    let mv = lower_expr(ctx, m, false)?;
    let m_park = ctx.park(mv);
    let kv = lower_expr(ctx, k, false)?;
    let m_resolved = ctx.unpark(&m_park);
    ctx.unbind(&m_park);
    Ok(ctx.let_(Prim::MapGet(m_resolved, kv)))
}

fn lower_vec_lit(
    ctx: &mut LowerCtx,
    kind: crate::ast::VecKind,
    els: &[Spanned<Expr>],
    span: Span,
) -> Result<Var, LowerError> {
    use crate::ast::VecKind;
    use crate::fz_ir::VecKindIr;
    // Bifurcate the AST sigil into a concrete element kind. ~v[..] is
    // numeric: inspect element exprs to choose I64 vs F64. Any literal
    // float in the elements forces F64 (currently deferred to .11.23).
    // .11.24.5: syntactic bifurcation of ~v[..]. Any element with a literal
    // Float forces F64; any mix of literal Int and literal Float is an error
    // (no auto-promotion under the "mixed without coercion" rule). Non-literal
    // elements (Vars referring to typed Float values) are refined post-lower
    // by ir_typer::rewrite_vec_kinds — which also catches the all-Float case
    // when the floats arrive via variables instead of literals.
    let ir_kind = match kind {
        VecKind::Numeric => {
            let has_float = els.iter().any(|e| matches!(&e.node, Expr::Float(_)));
            let has_int = els.iter().any(|e| matches!(&e.node, Expr::Int(_)));
            if has_float && has_int {
                return Err(LowerError::Unsupported {
                    span,
                    what: "~v[..] mixes Int and Float literals; no auto-promotion (fz-ul4.11.24.5)"
                        .into(),
                });
            }
            if has_float {
                VecKindIr::F64
            } else {
                VecKindIr::I64
            }
        }
        VecKind::Bytes => VecKindIr::U8,
        VecKind::Bits => VecKindIr::Bit,
    };
    let parks = lower_seq(ctx, els)?;
    let vs: Vec<Var> = parks.iter().map(|n| ctx.unpark(n)).collect();
    for n in &parks {
        ctx.unbind(n);
    }
    Ok(ctx.let_(Prim::MakeVec(ir_kind, vs)))
}

fn lower_bitstring_expr(
    ctx: &mut LowerCtx,
    fields: &[AstBitField<Spanned<Expr>>],
) -> Result<Var, LowerError> {
    // Lower each field's value expression, parking results so any CPS-split in
    // a later field's value still rebinds earlier ones.
    let mut value_parks = Vec::with_capacity(fields.len());
    for f in fields {
        let v = lower_expr(ctx, &f.value, false)?;
        value_parks.push(ctx.park(v));
    }
    let mut ir_fields: Vec<BitFieldIr> = Vec::with_capacity(fields.len());
    for (f, vn) in fields.iter().zip(value_parks.iter()) {
        ir_fields.push(BitFieldIr {
            value: ctx.unpark(vn),
            ty: f.spec.ty,
            size: lower_bit_size(ctx, &f.spec.size, f.value.span)?,
            endian: f.spec.endian,
            signed: f.spec.signed,
            unit: f.spec.unit,
        });
    }
    for n in &value_parks {
        ctx.unbind(n);
    }
    Ok(ctx.let_(Prim::MakeBitstring(ir_fields)))
}

fn lower_case(
    ctx: &mut LowerCtx,
    subject: &Spanned<Expr>,
    clauses: &[MatchClause],
    is_tail: bool,
    case_span: Span,
) -> Result<Var, LowerError> {
    // fz-duq.3 — Per-clause + optional join continuation fns. Same shape
    // as lower_if's fix from fz-duq.2, generalized to N clauses with
    // pattern bind on each.
    //
    // Outer fn: lowers subject, allocates try_blocks + fail_block. The
    // try_blocks form a fail-cascade chain (pattern mismatch → next try
    // block; final mismatch → fail_block → Halt(:case_clause)). At the
    // end of each try_block (after pattern bind succeeded), the block
    // TailCalls a per-clause continuation fn passing the current env
    // (outer + pattern-bound names). The clause body lives in its own fn
    // so any internal CPS-split stays confined to that clause's lineage.
    //
    // The clause-fn captures are snapshotted *after* pattern bind so the
    // newly-bound pattern names are included.
    // fz-ul4.43.F — matrix dispatch replaces the per-clause try_blocks
    // cascade. body_cb mints per-clause cont fns (case bodies always
    // wrap; no inline fast path here unlike multi_clause). join_opt
    // handles non-tail return-value plumbing.
    if clauses.is_empty() {
        return Err(LowerError::Unsupported {
            span: subject.span,
            what: "case with no clauses".into(),
        });
    }
    let sv = lower_expr(ctx, subject, false)?;

    let join_opt = if is_tail {
        None
    } else {
        Some(mint_cont_fn(
            ctx,
            "case_join",
            case_span,
            crate::fz_ir::FnCategory::ControlFlowCont,
        ))
    };

    let fail_block = ctx.cur_mut().block(vec![]);
    let saved_block = ctx.cur_block();
    ctx.cur_block = Some(fail_block);
    let cc = ctx.atoms.intern("case_clause");
    let v = ctx.let_(Prim::Const(Const::Atom(cc)));
    ctx.set_term(Term::Halt(v));
    ctx.cur_block = Some(saved_block);

    let matrix_entry = ctx.cur_mut().block(vec![]);
    ctx.set_term(Term::Goto(matrix_entry, vec![]));
    ctx.cur_block = Some(matrix_entry);
    ctx.terminated = false;

    let matrix = Matrix {
        subjects: vec![sv],
        rows: clauses
            .iter()
            .enumerate()
            .map(|(i, c)| Row {
                patterns: vec![c.pattern.clone()],
                preconditions: Vec::new(),
                bindings: Vec::new(),
                guard: c.guard.clone(),
                body_id: i as BodyId,
            })
            .collect(),
    };

    let saved_env = ctx.env.clone();
    let saved_order = ctx.env_order.clone();

    let mut clause_conts: Vec<Option<ContFn>> = (0..clauses.len()).map(|_| None).collect();
    let prev_origin = ctx.branch_origin;
    ctx.branch_origin = crate::fz_ir::BranchOrigin::ClauseDispatch;
    {
        let clauses_ref = clauses;
        let clause_conts_ref = &mut clause_conts;
        let saved_env_ref = &saved_env;
        let saved_order_ref = &saved_order;
        let mut cb = |ctx: &mut LowerCtx,
                      body_id: BodyId,
                      bindings: Vec<(String, Var)>,
                      _preconds: Vec<(Var, crate::types::Ty)>,
                      guard: Option<crate::ast::Spanned<crate::ast::Expr>>,
                      fall_block: BlockId|
         -> Result<(), LowerError> {
            let i = body_id as usize;
            let clause = &clauses_ref[i];
            ctx.env = saved_env_ref.clone();
            ctx.env_order = saved_order_ref.clone();
            for (name, var) in &bindings {
                ctx.bind(name, *var);
            }
            if let Some(g) = &guard {
                let guard_var = lower_expr(ctx, g, false)?;
                let body_b = ctx.cur_mut().block(vec![]);
                ctx.set_if_term(guard_var, body_b, fall_block);
                ctx.cur_block = Some(body_b);
                ctx.terminated = false;
            }
            let clause_cont = mint_cont_fn(
                ctx,
                format!("case_clause_{}", i),
                clause.span,
                crate::fz_ir::FnCategory::ControlFlowCont,
            );
            let captures = ctx.captured_snapshot();
            let capture_vars: Vec<Var> = captures.iter().map(|(_, v)| *v).collect();
            ctx.set_term(Term::TailCall {
                ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
                callee: clause_cont.id,
                args: capture_vars,
                is_back_edge: false,
            });
            ctx.terminated = true;
            clause_conts_ref[i] = Some(clause_cont);
            Ok(())
        };
        let result = lower_matrix_to_current_fn(ctx, matrix, fail_block, &mut cb);
        ctx.branch_origin = prev_origin;
        result?;
    }

    for (i, clause) in clauses.iter().enumerate() {
        let Some(cont) = clause_conts[i].clone() else {
            continue;
        };
        let _ = switch_to_cont_fn(ctx, &cont, 0);
        let result = lower_expr(ctx, &clause.body, /* is_tail */ true)?;
        finalize_arm(ctx, result, join_opt.as_ref());
    }

    if let Some(join) = &join_opt {
        let extras = switch_to_cont_fn(ctx, join, 1);
        Ok(extras[0])
    } else {
        ctx.terminated = true;
        Ok(Var(0))
    }
}

fn lower_cond(
    ctx: &mut LowerCtx,
    arms: &[(Spanned<Expr>, Spanned<Expr>)],
    is_tail: bool,
    cond_span: Span,
) -> Result<Var, LowerError> {
    // fz-duq.4 — Per-arm continuation fns. Each arm fn evaluates its test
    // and dispatches: true → lower body, finalize; false → TailCall the
    // next arm fn (or the fail fn for the last arm). Because tests in
    // cond can themselves contain calls (unlike `case` pattern bind),
    // wrapping the entire arm in its own fn confines arm-internal
    // CPS-splits — fixing the latent test-side analogue of fz-84m as well
    // as the body side.
    //
    // The outer fn TailCalls the first arm. fail_cont halts `:cond_clause`.
    if arms.is_empty() {
        let cc = ctx.atoms.intern("cond_clause");
        let v = ctx.let_(Prim::Const(Const::Atom(cc)));
        ctx.set_term(Term::Halt(v));
        ctx.terminated = true;
        return Ok(Var(0));
    }

    let join_opt = if is_tail {
        None
    } else {
        Some(mint_cont_fn(
            ctx,
            "cond_join",
            cond_span,
            crate::fz_ir::FnCategory::ControlFlowCont,
        ))
    };

    // Per-arm cont fns + fail cont.
    let arm_conts: Vec<ContFn> = (0..arms.len())
        .map(|i| {
            mint_cont_fn(
                ctx,
                format!("cond_arm_{}", i),
                arms[i].0.span,
                crate::fz_ir::FnCategory::ControlFlowCont,
            )
        })
        .collect();
    let fail_cont = mint_cont_fn(
        ctx,
        "cond_fail",
        cond_span,
        crate::fz_ir::FnCategory::ControlFlowCont,
    );

    // Outer fn: TailCall first arm.
    let captures = ctx.captured_snapshot();
    let capture_vars: Vec<Var> = captures.iter().map(|(_, v)| *v).collect();
    ctx.set_term(Term::TailCall {
        ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
        callee: arm_conts[0].id,
        args: capture_vars,
        is_back_edge: false,
    });

    // Build each arm fn.
    for (i, (test, body)) in arms.iter().enumerate() {
        let next_id = arm_conts.get(i + 1).map(|c| c.id).unwrap_or(fail_cont.id);
        let _ = switch_to_cont_fn(ctx, &arm_conts[i], 0);
        let cv = lower_expr(ctx, test, false)?;

        // body_b + fall_b in whatever fn ctx.cur is now (arm_conts[i] or
        // a CPS-split descendant if the test contained a non-tail call).
        let body_b = ctx.cur_mut().block(vec![]);
        let fall_b = ctx.cur_mut().block(vec![]);
        let prev_origin = ctx.branch_origin;
        ctx.branch_origin = crate::fz_ir::BranchOrigin::ClauseDispatch;
        ctx.set_if_term(cv, body_b, fall_b);
        ctx.branch_origin = prev_origin;

        // fall_b: TailCall next arm (or fail). Captures are the current
        // env, which includes the outer captures (rebound into the arm fn
        // or its CPS-split descendant) plus any temps from test lowering.
        let fall_captures = ctx.captured_snapshot();
        let fall_capture_vars: Vec<Var> = fall_captures.iter().map(|(_, v)| *v).collect();
        ctx.cur_block = Some(fall_b);
        ctx.set_term(Term::TailCall {
            ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
            callee: next_id,
            args: fall_capture_vars,
            is_back_edge: false,
        });

        // body_b: lower the body inline, finalize.
        ctx.cur_block = Some(body_b);
        ctx.terminated = false;
        let result = lower_expr(ctx, body, /* is_tail */ true)?;
        finalize_arm(ctx, result, join_opt.as_ref());
    }

    // Build fail_cont: halt :cond_clause.
    let _ = switch_to_cont_fn(ctx, &fail_cont, 0);
    let cc = ctx.atoms.intern("cond_clause");
    let v = ctx.let_(Prim::Const(Const::Atom(cc)));
    ctx.set_term(Term::Halt(v));
    ctx.terminated = true;

    if let Some(join) = &join_opt {
        let extras = switch_to_cont_fn(ctx, join, 1);
        Ok(extras[0])
    } else {
        ctx.terminated = true;
        Ok(Var(0))
    }
}

fn lower_with(
    ctx: &mut LowerCtx,
    bindings: &[WithBinding],
    body: &Spanned<Expr>,
    else_clauses: &[MatchClause],
    is_tail: bool,
    with_span: Span,
) -> Result<Var, LowerError> {
    // fz-duq.4 — `with` lowers into:
    //   * Main path (in outer fn + CPS descendants): walk bindings.
    //     Each Match binding emits a per-binding `mismatch_b` block whose
    //     terminator TailCalls `with_fail_cont` (a continuation fn)
    //     carrying the unmatched value plus the outer captures.
    //   * `with_fail_cont` (cont fn): dispatches over else_clauses via
    //     try_blocks + per-else-clause body cont fns. No else_clauses →
    //     halt :with_clause.
    //   * Main body: lowered inline at the end of the main path; on
    //     fall-through (`!ctx.terminated`), finalize_arm emits either
    //     Return (tail) or TailCall(with_join_cont, ...).
    //
    // The old design used a single `join_b` block + `with_fail` block in
    // the outer fn; any CPS-split inside a binding/body/else-clause body
    // stranded those blocks in a finalized fn. Continuation-fn shape
    // makes the lowering robust to all CPS-split positions.

    let join_opt = if is_tail {
        None
    } else {
        Some(mint_cont_fn(
            ctx,
            "with_join",
            with_span,
            crate::fz_ir::FnCategory::ControlFlowCont,
        ))
    };

    // with_fail_cont: a continuation fn that receives (unmatched_value,
    // ...outer_captures). Minted now so we know its FnId before walking
    // bindings.
    let with_fail_cont = mint_cont_fn(
        ctx,
        "with_fail",
        with_span,
        crate::fz_ir::FnCategory::ControlFlowCont,
    );

    // -- Main path: walk bindings.
    for binding in bindings {
        match binding {
            WithBinding::Bare(e) => {
                lower_expr(ctx, e, false)?;
            }
            WithBinding::Match(pat, e) => {
                let v = lower_expr(ctx, e, false)?;
                // Park v so any CPS-split during pattern lowering rebinds it.
                let v_park = ctx.park(v);
                // Per-binding mismatch block — TailCalls with_fail_cont
                // with [unmatched, ...outer_captures]. Captures resolved
                // by name (with_fail_cont's outer_captured) from current
                // env, which may be a CPS-split descendant of outer.
                let mismatch_b = ctx.cur_mut().block(vec![]);
                let saved_blk = ctx.cur_block();
                ctx.cur_block = Some(mismatch_b);
                let v_in_mismatch = ctx.unpark(&v_park);
                let mut args = Vec::with_capacity(1 + with_fail_cont.outer_captured.len());
                args.push(v_in_mismatch);
                for (name, _) in &with_fail_cont.outer_captured {
                    let cv = ctx.env.get(name).copied().unwrap_or_else(|| {
                        panic!(
                            "lower_with: captured name `{}` not in env at mismatch",
                            name
                        )
                    });
                    args.push(cv);
                }
                ctx.set_term(Term::TailCall {
                    ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
                    callee: with_fail_cont.id,
                    args,
                    is_back_edge: false,
                });
                ctx.cur_block = Some(saved_blk);
                let v_resolved = ctx.unpark(&v_park);
                ctx.unbind(&v_park);
                let prev_origin = ctx.branch_origin;
                ctx.branch_origin = crate::fz_ir::BranchOrigin::PatternBind;
                let res = lower_pattern_bind(ctx, v_resolved, pat, mismatch_b);
                ctx.branch_origin = prev_origin;
                res?;
            }
        }
    }

    // Main body lowered inline. Finalize via join_opt or Return.
    let result = lower_expr(ctx, body, /* is_tail */ true)?;
    finalize_arm(ctx, result, join_opt.as_ref());

    // -- Build with_fail_cont. Receives (unmatched_value, ...captures).
    let extras = switch_to_cont_fn(ctx, &with_fail_cont, 1);
    let unmatched_v = extras[0];

    if else_clauses.is_empty() {
        let cc = ctx.atoms.intern("with_clause");
        let v = ctx.let_(Prim::Const(Const::Atom(cc)));
        ctx.set_term(Term::Halt(v));
        ctx.terminated = true;
    } else {
        let fail_block = ctx.cur_mut().block(vec![]);
        let saved_block = ctx.cur_block();
        ctx.cur_block = Some(fail_block);
        let cc = ctx.atoms.intern("with_clause");
        let v = ctx.let_(Prim::Const(Const::Atom(cc)));
        ctx.set_term(Term::Halt(v));
        ctx.cur_block = Some(saved_block);

        let matrix_entry = ctx.cur_mut().block(vec![]);
        ctx.set_term(Term::Goto(matrix_entry, vec![]));
        ctx.cur_block = Some(matrix_entry);
        ctx.terminated = false;

        let matrix = Matrix {
            subjects: vec![unmatched_v],
            rows: else_clauses
                .iter()
                .enumerate()
                .map(|(i, c)| Row {
                    patterns: vec![c.pattern.clone()],
                    preconditions: Vec::new(),
                    bindings: Vec::new(),
                    guard: c.guard.clone(),
                    body_id: i as BodyId,
                })
                .collect(),
        };

        let saved_fail_env = ctx.env.clone();
        let saved_fail_order = ctx.env_order.clone();

        let mut else_conts: Vec<Option<ContFn>> = (0..else_clauses.len()).map(|_| None).collect();
        let prev_origin = ctx.branch_origin;
        ctx.branch_origin = crate::fz_ir::BranchOrigin::ClauseDispatch;
        {
            let else_conts_ref = &mut else_conts;
            let saved_fail_env_ref = &saved_fail_env;
            let saved_fail_order_ref = &saved_fail_order;
            let mut cb = |ctx: &mut LowerCtx,
                          body_id: BodyId,
                          bindings: Vec<(String, Var)>,
                          _preconds: Vec<(Var, crate::types::Ty)>,
                          guard: Option<crate::ast::Spanned<crate::ast::Expr>>,
                          fall_block: BlockId|
             -> Result<(), LowerError> {
                let i = body_id as usize;
                let clause = &else_clauses[i];
                ctx.env = saved_fail_env_ref.clone();
                ctx.env_order = saved_fail_order_ref.clone();
                for (name, var) in &bindings {
                    ctx.bind(name, *var);
                }
                if let Some(g) = &guard {
                    let guard_var = lower_expr(ctx, g, false)?;
                    let body_b = ctx.cur_mut().block(vec![]);
                    ctx.set_if_term(guard_var, body_b, fall_block);
                    ctx.cur_block = Some(body_b);
                    ctx.terminated = false;
                }
                let cont = mint_cont_fn(
                    ctx,
                    format!("with_else_{}", i),
                    clause.span,
                    crate::fz_ir::FnCategory::ControlFlowCont,
                );
                let captures = ctx.captured_snapshot();
                let capture_vars: Vec<Var> = captures.iter().map(|(_, v)| *v).collect();
                ctx.set_term(Term::TailCall {
                    ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
                    callee: cont.id,
                    args: capture_vars,
                    is_back_edge: false,
                });
                ctx.terminated = true;
                else_conts_ref[i] = Some(cont);
                Ok(())
            };
            let result = lower_matrix_to_current_fn(ctx, matrix, fail_block, &mut cb);
            ctx.branch_origin = prev_origin;
            result?;
        }

        for (i, clause) in else_clauses.iter().enumerate() {
            let Some(cont) = else_conts[i].clone() else {
                continue;
            };
            let _ = switch_to_cont_fn(ctx, &cont, 0);
            let result = lower_expr(ctx, &clause.body, /* is_tail */ true)?;
            finalize_arm(ctx, result, join_opt.as_ref());
        }
    }

    if let Some(join) = &join_opt {
        let extras = switch_to_cont_fn(ctx, join, 1);
        Ok(extras[0])
    } else {
        ctx.terminated = true;
        Ok(Var(0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    fn lower_src(src: &str) -> Module {
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        lower_program(&mut crate::types::ConcreteTypes, &prog).expect("lower failed")
    }

    fn lower_src_err(src: &str) -> LowerError {
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        lower_program(&mut crate::types::ConcreteTypes, &prog).expect_err("expected lower error")
    }

    /// fz-qbg.4 — Compile + run a fz program through the JIT and return
    /// captured stdout (joined by newline). Mirrors `ir_codegen::tests::
    /// capture_main`; lets ir_lower-level tests assert end-to-end runtime
    /// correctness rather than just IR shape.
    fn run_and_capture(src: &str) -> String {
        let m = lower_src(src);
        let entry = m.fn_by_name("main").expect("no main fn").id;
        let _ = fz_runtime::ir_runtime::test_capture_take();
        let _ = crate::ir_codegen::compile(
            &mut crate::types::ConcreteTypes,
            &m,
            &crate::telemetry::NullTelemetry,
        )
        .unwrap()
        .run(entry);
        fz_runtime::ir_runtime::test_capture_take().join("\n")
    }

    #[test]
    fn lower_const_int_returns_in_entry_block() {
        let m = lower_src("fn f() do 42 end");
        let s = format!("{}", m);
        assert!(s.contains("const(42)"), "{}", s);
        assert!(s.contains("return v"), "{}", s);
    }

    #[test]
    fn lower_var_lookup() {
        let m = lower_src("fn id(x), do: x");
        let s = format!("{}", m);
        assert!(s.contains("return v0"), "got:\n{}", s);
    }

    #[test]
    fn lower_binop_add() {
        let m = lower_src("fn add1(x), do: x + 1");
        let s = format!("{}", m);
        assert!(s.contains("const(1)"), "{}", s);
        assert!(s.contains(" + "), "{}", s);
    }

    #[test]
    fn lower_unop_neg() {
        let m = lower_src("fn neg(x), do: -x");
        let s = format!("{}", m);
        assert!(s.contains("- v0"));
    }

    #[test]
    fn lower_tail_call_uses_tail_call() {
        let m = lower_src("fn caller(x), do: callee(x)\nfn callee(y), do: y");
        let s = format!("{}", m);
        assert!(s.contains("tail_call"), "got:\n{}", s);
    }

    #[test]
    fn lower_nontail_call_splits_into_continuation() {
        let m = lower_src("fn caller(x), do: callee(x) + 1\nfn callee(y), do: y");
        let s = format!("{}", m);
        // "call fnN" where N is callee's FnId (shifts with runtime.fz prelude).
        assert!(s.contains("call fn"), "expected explicit call, got:\n{}", s);
        assert!(s.contains("cont(fn"), "expected continuation, got:\n{}", s);
        // Continuation fn is named "k_{FnId}"; FnId shifts with runtime.fz prelude.
        assert!(
            s.contains(" k_") || s.contains("lambda_"),
            "expected continuation fn, got:\n{}",
            s
        );
    }

    #[test]
    fn lower_if_uses_continuation_fns() {
        // fz-duq.2 — `if` lowers to: outer fn with Term::If + per-arm
        // TailCalls into separate fns (if_then / if_else / optional
        // if_join). The old block-join shape is gone.
        let m = lower_src("fn pos(x), do: if x > 0, do: 1, else: -1");
        let s = format!("{}", m);
        assert!(s.contains("if v"), "expected If terminator: {}", s);
        assert!(s.contains("if_then"), "expected if_then arm fn: {}", s);
        assert!(s.contains("if_else"), "expected if_else arm fn: {}", s);
        assert!(
            s.contains("tail_call"),
            "expected TailCall from arm block: {}",
            s
        );
        // Tail-position if: no join fn (arms self-Return).
        assert!(
            !s.contains("if_join"),
            "tail-position if should not need a join fn: {}",
            s
        );
    }

    #[test]
    fn fz_84m_repro_a_prints_99() {
        // fz-84m repro A — constant cond + non-tail call in if-arm.
        // Pre-fz-duq.2 panicked at fz_ir.rs:453 (block_mut "unknown
        // block") during IR construction. Now runs end-to-end.
        let out = run_and_capture(
            "fn helper(), do: 7\n\
             fn main() do\n\
               if 1 == 0 do print(helper()) else print(99) end\n\
             end",
        );
        assert_eq!(out, "99");
    }

    #[test]
    fn fz_84m_repro_b_prints_7_then_99() {
        // fz-84m repro B — tail-call in if-arm + per-callsite narrowing.
        // Pre-fz-duq.2 silently dropped the tail call by overwriting its
        // TailCall terminator with `Goto(join_b, [Var(0)])`, propagating
        // the sentinel as the if's value. Result: exit 0, no stdout.
        let out = run_and_capture(
            "fn helper(), do: 7\n\
             fn pick(n) do if n == 0 do helper() else 99 end end\n\
             fn main() do print(pick(0)); print(pick(1)) end",
        );
        assert_eq!(out, "7\n99");
    }

    #[test]
    fn lower_case_uses_per_clause_cont_fns() {
        // fz-duq.3 — `case` lowers each clause body into its own cont fn
        // so that internal CPS-splits stay confined.
        let m = lower_src(
            "fn helper(), do: 7\n\
             fn classify(n) do\n\
               case n do\n\
                 0 -> helper()\n\
                 _ -> 99\n\
               end\n\
             end",
        );
        let s = format!("{}", m);
        assert!(s.contains("case_clause_0"), "expected clause cont: {}", s);
        assert!(s.contains("case_clause_1"), "expected clause cont: {}", s);
        // Tail-position case: no join fn.
        assert!(
            !s.contains("case_join"),
            "tail-position case should not need a join fn: {}",
            s
        );
    }

    #[test]
    fn lower_cond_uses_per_arm_cont_fns() {
        // fz-duq.4 — cond arms each lower into their own cont fn so that
        // both test- and body-side CPS-splits stay confined.
        let m = lower_src(
            "fn helper(), do: 7\n\
             fn route(n) do\n\
               cond do\n\
                 n == 0 -> helper()\n\
                 true -> 99\n\
               end\n\
             end",
        );
        let s = format!("{}", m);
        assert!(s.contains("cond_arm_0"), "expected arm cont: {}", s);
        assert!(s.contains("cond_arm_1"), "expected arm cont: {}", s);
        assert!(s.contains("cond_fail"), "expected fail cont: {}", s);
    }

    #[test]
    fn lower_with_uses_continuation_fns() {
        // fz-duq.4 — `with`'s mismatch funnel becomes a continuation fn
        // (`with_fail`) and each else-clause body lives in its own cont fn.
        let m = lower_src(
            "fn f(v) do\n\
               with :ok <- v do\n\
                 1\n\
               else\n\
                 :err -> 2\n\
               end\n\
             end",
        );
        let s = format!("{}", m);
        assert!(s.contains("with_fail"), "expected with_fail cont: {}", s);
        assert!(
            s.contains("with_else_0"),
            "expected else clause cont: {}",
            s
        );
    }

    #[test]
    fn lower_case_with_call_in_clause_no_panic() {
        // case body with a call (was silently broken via Bug 2 — same
        // class as fz-84m's if repros).
        let _ = lower_src(
            "fn helper(), do: 7\n\
             fn classify(n) do\n\
               case n do\n\
                 0 -> helper()\n\
                 _ -> 99\n\
               end\n\
             end\n\
             fn main() do\n\
               print(classify(0))\n\
               print(classify(5))\n\
             end",
        );
    }

    #[test]
    fn fz_ben_tuple_pattern_typetest_routes_non_tuple_to_else() {
        // fz-ben — `{:ok, x}` pattern on `:err` (a non-tuple). Pre-fix,
        // lower_pattern_bind for Pattern::Tuple unconditionally emitted
        // `Prim::TupleField(:err, 0)`, which codegen lowered to a
        // `load notrap aligned :err+16` reading heap garbage. With
        // `notrap` swallowing the SIGSEGV, this fixture silently failed
        // (exit 0, no stdout). After fix: a TypeTest gates the
        // projection — non-tuple subjects route to the fail_block, which
        // dispatches the else-clause `:err -> 0`.
        let out = run_and_capture(
            "fn f(v) do\n\
               with {:ok, x} <- v do x else :err -> 0 end\n\
             end\n\
             fn main() do print(f(:err)) end",
        );
        assert_eq!(out, "0");
    }

    #[test]
    fn fz_84m_repro_c_prints_7_then_99_no_narrowing() {
        // fz-84m repro C — same bug shape as B but with `n > 0` rather
        // than `n == 0`, so the typer doesn't narrow either arm. Proves
        // the bug was structural in lowering, not type-narrowing driven.
        let out = run_and_capture(
            "fn helper(), do: 7\n\
             fn pick(n) do if n > 0 do helper() else 99 end end\n\
             fn main() do print(pick(5)); print(pick(0)) end",
        );
        assert_eq!(out, "7\n99");
    }

    #[test]
    fn lower_if_nontail_uses_join_fn() {
        // Non-tail if (used as call argument): all three cont fns minted.
        let m = lower_src(
            "fn id(x), do: x\n\
             fn pick(x), do: id(if x > 0, do: 1, else: -1)",
        );
        let s = format!("{}", m);
        assert!(s.contains("if_then"), "{}", s);
        assert!(s.contains("if_else"), "{}", s);
        assert!(
            s.contains("if_join"),
            "expected join fn for non-tail: {}",
            s
        );
    }

    #[test]
    fn lower_block_evaluates_last_expr() {
        let m = lower_src("fn b() do\n  1\n  2\n  3\nend");
        let s = format!("{}", m);
        assert!(s.contains("const(1)"), "{}", s);
        assert!(s.contains("const(2)"), "{}", s);
        assert!(s.contains("const(3)"), "{}", s);
        assert!(s.contains("return v"), "{}", s);
    }

    #[test]
    fn lower_list_makes_list_prim() {
        let m = lower_src("fn l(), do: [1, 2]");
        let s = format!("{}", m);
        assert!(s.contains("list(["), "{}", s);
        assert!(
            !s.contains("list([] |"),
            "no-tail list shouldn't have | sep: {}",
            s
        );
    }

    #[test]
    fn lower_list_with_tail() {
        let m = lower_src("fn l(t), do: [1 | t]");
        let s = format!("{}", m);
        assert!(
            s.contains("] | v0)"),
            "expected list with v0 (param t) tail: {}",
            s
        );
    }

    #[test]
    fn lower_tuple_makes_tuple_prim() {
        let m = lower_src("fn t(), do: {1, :ok}");
        let s = format!("{}", m);
        assert!(s.contains("tuple(["), "{}", s);
    }

    #[test]
    fn lower_tuple_pattern_projects_fields() {
        let m = lower_src("fn first({a, b}), do: a");
        let s = format!("{}", m);
        assert!(s.contains("tuple_field(v0, 0)"), "got:\n{}", s);
        assert!(s.contains("tuple_field(v0, 1)"), "got:\n{}", s);
    }

    #[test]
    fn lower_match_expr_binds_var() {
        let m = lower_src("fn m(p) do\n  x = p\n  x\nend");
        let s = format!("{}", m);
        assert!(s.contains("return v0"), "got:\n{}", s);
    }

    /// fz-fyq.3 — `collect_diagnostics` filters `unreachable-arm` to
    /// `BranchOrigin::User`. A destructure (`{a,b} = ...`) and a fn-clause
    /// dispatch both synthesize Ifs the typer can prove dead-edged; neither
    /// should warn. User-authored Ifs whose dead branch the typer can
    /// prove (here: `if true do A else B` where the else is structurally
    /// unreachable) still do.
    #[test]
    fn unreachable_arm_silenced_on_synthesized_ifs() {
        let m = lower_src(concat!(
            "fn fst(0), do: :zero\n",
            "fn fst(_), do: :other\n",
            "fn main() do\n",
            "  {a, b} = {1, 2}\n",
            "  fst(a + b)\n",
            "end\n",
        ));
        let mut ct = crate::types::ConcreteTypes;
        let mt = crate::ir_typer::type_module(&mut ct, &m, &crate::telemetry::NullTelemetry);
        let diags = crate::ir_typer::collect_diagnostics(&mut ct, &m, &mt);
        let unreachable: Vec<_> = diags
            .iter()
            .filter(|d| d.code == crate::diag::codes::TYPE_UNREACHABLE_ARM)
            .collect();
        assert!(
            unreachable.is_empty(),
            "synthesized dispatch Ifs must not warn; got {:?}",
            unreachable,
        );
    }

    /// fz-fyq.2 — `ModuleTypes::dead_branches` publishes one entry per
    /// provably-dead branch under cross-spec consensus, and stays silent
    /// for polymorphic-recursion functions where some spec leaves the
    /// branch live (e.g. a `sum`-style fn typed `[]` vs `[h | t]`).
    #[test]
    fn dead_branches_published_for_destructure_but_not_polymorphic_sum() {
        use crate::fz_ir::DeadBranch;
        // Irrefutable destructure on a known-2-tuple — the typer proves
        // the synthesized fail edge dead under the one live spec.
        let m = lower_src("fn main() do\n  {a, b} = {1, 2}\n  a + b\nend\n");
        let mut ct = crate::types::ConcreteTypes;
        let mt = crate::ir_typer::type_module(&mut ct, &m, &crate::telemetry::NullTelemetry);
        assert!(
            mt.dead_branches
                .values()
                .any(|d| matches!(d, DeadBranch::Else)),
            "expected an Else dead branch for {{a,b}} = {{1,2}}; got {:?}",
            mt.dead_branches,
        );

        // Polymorphic sum — every spec needs both branches alive
        // (the `[]` arm is dead in the leaf spec but live in the
        // recursive spec). Nothing should be published.
        let m2 = lower_src(concat!(
            "fn sum([]), do: 0\n",
            "fn sum([h | t]), do: h + sum(t)\n",
            "fn main(), do: sum([1, 2, 3])\n",
        ));
        let mt2 = crate::ir_typer::type_module(&mut ct, &m2, &crate::telemetry::NullTelemetry);
        // The destructure inside main may itself produce dead branches,
        // but sum's clause-dispatch Ifs must not.
        let sum_fid = m2.fn_by_name("sum").expect("sum exists").id;
        for (fid, _bid) in mt2.dead_branches.keys() {
            assert_ne!(
                *fid, sum_fid,
                "sum/1 is polymorphically recursive; no branch should be published dead",
            );
        }
    }

    /// fz-fyq.1 — every lowering path that synthesizes a `Term::If` tags it
    /// with the right `BranchOrigin`. Cover one source program that exercises
    /// each origin and assert the right set appears in the lowered module.
    #[test]
    fn branch_origin_tagged_per_lowering_path() {
        use crate::fz_ir::BranchOrigin;
        let m = lower_src(concat!(
            // ParamGuard: typed param synthesizes a TypeTest If.
            "fn f(x :: integer), do: x\n",
            // ClauseDispatch (multi-clause): two clauses on a literal.
            "fn g(0), do: :zero\n",
            "fn g(_), do: :other\n",
            // PatternBind: `{a, b} = ...` synthesizes Ifs that check tuple arity.
            "fn h() do\n",
            "  {a, b} = {1, 2}\n",
            "  a + b\n",
            "end\n",
            // User: hand-written `if`.
            "fn i(n), do: if n > 0, do: 1, else: 0\n",
        ));
        let mut seen: std::collections::HashSet<BranchOrigin> = std::collections::HashSet::new();
        for f in &m.fns {
            for b in &f.blocks {
                if let crate::fz_ir::Term::If { origin, .. } = &b.terminator {
                    seen.insert(*origin);
                }
            }
        }
        assert!(
            seen.contains(&BranchOrigin::User),
            "missing User: {:?}",
            seen
        );
        assert!(
            seen.contains(&BranchOrigin::PatternBind),
            "missing PatternBind: {:?}",
            seen,
        );
        assert!(
            seen.contains(&BranchOrigin::ClauseDispatch),
            "missing ClauseDispatch: {:?}",
            seen,
        );
        assert!(
            seen.contains(&BranchOrigin::ParamGuard),
            "missing ParamGuard: {:?}",
            seen,
        );
    }

    #[test]
    fn multi_clause_dispatch_lowers_matcher_inline() {
        // fz-puj.52.7 — multi-clause fns lower the Matcher inline
        // into the user fn again so dispatch does not become a separate
        // spec-producing matcher fn.
        let m = lower_src("fn fact(0), do: 1\nfn fact(n), do: n * fact(n - 1)");
        let s = format!("{}", m);
        assert!(
            !s.contains("fact_matcher_"),
            "did not expect fact_matcher_N fn: {}",
            s
        );
        assert!(s.contains("if v"), "expected pattern test If: {}", s);
        assert!(s.contains("halt v"), "expected halt in fail block:\n{}", s);
        assert!(
            s.contains(":atom_"),
            "expected interned atom in fail block:\n{}",
            s
        );
    }

    #[test]
    fn lower_lambda_creates_separate_fn_and_closure() {
        let m = lower_src("fn mk(x), do: fn(y) -> x + y");
        let s = format!("{}", m);
        assert!(
            s.contains("closure(fn"),
            "expected closure prim, got:\n{}",
            s
        );
        assert!(s.contains("lambda_"), "expected lambda fn name: {}", s);
        // Module has 7 runtime.fz wrapper fns + mk + lambda = 9.
        assert!(
            m.fns.len() >= 2,
            "expected ≥2 fns (mk + lambda + prelude), got {}",
            m.fns.len()
        );
        assert!(m.fns.iter().any(|f| f.name == "mk"), "expected 'mk' fn");
        assert!(
            m.fns.iter().any(|f| f.name.starts_with("lambda_")),
            "expected lambda fn"
        );
    }

    /// fz-ext.7 — `print(x)` now routes through the runtime.fz wrapper fn
    /// `fn print(x) do fz_print_value(x) end`. The wrapper's body contains
    /// `extern#0(` (fz_print_value = ExternId 0 in runtime.fz).
    #[test]
    fn print_call_routes_through_runtime_fz_wrapper() {
        let m = lower_src("fn p(), do: print(1)");
        let s = format!("{}", m);
        // The fz_print_value extern dispatch lives inside the print wrapper.
        assert!(s.contains("extern#0("), "expected extern#0( in:\n{}", s);
    }

    /// fz-ul4.29.9 / fz-ext.7 — a `spawn(x)` call lowers to
    /// `MakeClosure(fz_spawn_thunk, [x])` followed by `Extern(fz_spawn, [wrapper])`.
    /// The synthesized thunk fn appears in the module alongside the user fns.
    #[test]
    fn spawn_callsite_is_wrapped_in_fz_spawn_thunk() {
        let m = lower_src("fn child(), do: 0\nfn p() do spawn(child) end");
        assert!(
            m.fns.iter().any(|f| f.name == "fz_spawn_thunk"),
            "expected fz_spawn_thunk in module fns; got: {:?}",
            m.fns.iter().map(|f| &f.name).collect::<Vec<_>>()
        );
        let thunk_id = m
            .fns
            .iter()
            .find(|f| f.name == "fz_spawn_thunk")
            .unwrap()
            .id;
        // p's body should contain `MakeClosure(thunk_id, [<child-closure>])`
        // followed by `Extern(fz_spawn=5, [<wrapper>])`. Render and grep.
        let s = format!("{}", m);
        let needle = format!("closure(fn{}", thunk_id.0);
        assert!(
            s.contains(&needle),
            "expected wrapper `{}` in lowered IR:\n{}",
            needle,
            s
        );
    }

    /// fz-siu.12 — spawn/2 wraps the closure arg in fz_spawn_thunk exactly
    /// like spawn/1; the min_heap_size arg passes through as the second
    /// Extern operand. fz_spawn_opt = ExternId(6) per runtime.fz ordering.
    #[test]
    fn spawn2_wraps_closure_and_threads_opts() {
        let m = lower_src("fn child(), do: 0\nfn p() do spawn(child, 4096) end");
        let thunk_id = m
            .fns
            .iter()
            .find(|f| f.name == "fz_spawn_thunk")
            .expect("fz_spawn_thunk must be synthesized for spawn/2")
            .id;
        let s = format!("{}", m);
        // Wrapper closure must appear.
        let needle = format!("closure(fn{}", thunk_id.0);
        assert!(
            s.contains(&needle),
            "expected wrapper `{}` in spawn/2 IR:\n{}",
            needle,
            s
        );
        // fz_spawn_opt = ExternId(7) in runtime.fz (0-based, after fz_spawn=6).
        assert!(
            s.contains("extern#7("),
            "expected Extern(fz_spawn_opt=7, ...) in IR:\n{}",
            s
        );
    }

    /// fz-ul4.29.9 — a program with no `spawn` should not synthesize
    /// `fz_spawn_thunk` (lazy synthesis, zero overhead).
    #[test]
    fn no_spawn_means_no_thunk_fn() {
        let m = lower_src("fn p(), do: 0");
        assert!(
            !m.fns.iter().any(|f| f.name == "fz_spawn_thunk"),
            "expected no fz_spawn_thunk for spawn-free program"
        );
    }

    #[test]
    fn unbound_var_returns_lower_error() {
        let err = lower_src_err("fn f(), do: missing");
        assert!(matches!(err, LowerError::Unbound { .. }));
    }

    /// .21 step 3: lower errors carry a real Span of the offending node,
    /// not Span::DUMMY.
    #[test]
    fn unbound_var_diag_has_real_span() {
        let err = lower_src_err("fn f(), do: missing");
        let d = err.to_diagnostic();
        assert_ne!(
            d.primary.span,
            Span::DUMMY,
            "lower diagnostic should carry the unbound Var's span"
        );
        assert_eq!(d.code, crate::diag::codes::LOWER_UNBOUND);
    }

    #[test]
    fn unbound_callee_returns_lower_error() {
        let err = lower_src_err("fn f(), do: nonesuch(1)");
        assert!(matches!(err, LowerError::Unbound { .. }));
    }

    #[test]
    fn empty_case_returns_unsupported() {
        let err = lower_src_err("fn f() do case 1 do end end");
        assert!(matches!(err, LowerError::Unsupported { .. }));
    }

    #[test]
    fn vec_lit_lowers_to_make_vec() {
        let m = lower_src("fn v(), do: ~v[1, 2, 3]");
        let s = format!("{}", m);
        assert!(s.contains("vec(i64, ["), "got:\n{}", s);
    }

    #[test]
    fn map_lowers_to_make_map() {
        let m = lower_src("fn m(), do: %{k: 1}");
        let s = format!("{}", m);
        assert!(s.contains("map({"), "got:\n{}", s);
    }

    #[test]
    fn map_update_lowers() {
        let m = lower_src("fn u(m), do: %{m | k: 2}");
        let s = format!("{}", m);
        assert!(s.contains("map_update("), "got:\n{}", s);
    }

    #[test]
    fn index_lowers_to_map_get() {
        let m = lower_src("fn g(m), do: m[:k]");
        let s = format!("{}", m);
        assert!(s.contains("map_get("), "got:\n{}", s);
    }

    #[test]
    fn bitstring_expr_lowers() {
        let m = lower_src("fn b(), do: << 0xA5 >>");
        let s = format!("{}", m);
        assert!(s.contains("bitstring(["), "got:\n{}", s);
    }

    #[test]
    fn case_lowers_matcher_inline() {
        // fz-puj.52.7 — case sites lower the Matcher inline so the
        // typer does not see a case_matcher_N function boundary.
        let m = lower_src(
            r#"
fn c(x) do
  case x do
    0 -> :zero
    _ -> :other
  end
end
"#,
        );
        let s = format!("{}", m);
        assert!(
            !s.contains("case_matcher_"),
            "did not expect case_matcher_N fn in module dump: {}",
            s
        );
        assert!(
            s.contains("if v"),
            "expected if for inline pattern check: {}",
            s
        );
        assert!(
            s.contains("tail_call"),
            "expected tail_call to clause cont fns: {}",
            s
        );
    }

    #[test]
    fn cond_lowers() {
        // cond is parsed; lowering should emit If terminators.
        let m = lower_src(
            r#"
fn c(x) do
  cond do
    x > 0 -> :pos
    true -> :nonpos
  end
end
"#,
        );
        let s = format!("{}", m);
        assert!(s.contains("if v"), "got:\n{}", s);
    }

    #[test]
    fn with_simple_lowers() {
        let m = lower_src(
            r#"
fn w() do
  with {:ok, a} <- {:ok, 1}, do: a
end
"#,
        );
        let s = format!("{}", m);
        assert!(
            s.contains("tuple_field"),
            "expected pattern projection: {}",
            s
        );
    }

    #[test]
    fn map_pattern_uses_map_get_check() {
        let m = lower_src("fn first(%{name: n}), do: n");
        let s = format!("{}", m);
        assert!(s.contains("map_get("), "got:\n{}", s);
    }

    #[test]
    fn bitstring_pattern_lowers_to_per_field_reads() {
        let m = lower_src("fn p(<<x::8>>), do: x");
        let s = format!("{}", m);
        assert!(s.contains("bit_reader_init("), "got:\n{}", s);
        assert!(s.contains("bit_read_field("), "got:\n{}", s);
        assert!(s.contains("bit_reader_done("), "got:\n{}", s);
    }

    #[test]
    fn quote_returns_post_expansion_node() {
        // Skip macro expansion to surface the leftover-quote error path.
        let err = lower_src_err("fn f(), do: quote do: 1");
        assert!(matches!(err, LowerError::PostExpansionNode { .. }));
    }

    /// Span round-trip: AST nodes parsed by the parser carry non-DUMMY spans
    /// that slice back to their source lexemes.
    #[test]
    fn parser_attaches_real_spans_to_expressions() {
        let src = "fn ident(x), do: x + 1";
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let Item::Fn(def) = &*prog.items[0] else {
            panic!("expected fn")
        };
        // The body `x + 1` is a BinOp; its span should be non-DUMMY and
        // slice to the operator-bracketed substring.
        let body = &def.clauses[0].body;
        assert!(!body.span.is_dummy());
        let lexeme = &src[body.span.start as usize..body.span.end as usize];
        assert!(
            lexeme.contains('+'),
            "body span should cover the binop expression, got {:?}",
            lexeme
        );
    }

    /// FnDef.name_span pinpoints the source name token (not the whole def).
    #[test]
    fn parser_records_fn_name_span() {
        let src = "fn foobar(), do: 0";
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let Item::Fn(def) = &*prog.items[0] else {
            panic!("expected fn")
        };
        let name_text = &src[def.name_span.start as usize..def.name_span.end as usize];
        assert_eq!(name_text, "foobar");
    }

    // ----- .20.4: SourceInfo side-tables -----

    /// Pattern-bound parameters record their name + binding span in
    /// `Module.source`. The ticket's canonical test: lower a `double(x)`
    /// function and verify the param's Var → "x", span → the `x` token.
    #[test]
    fn pattern_var_records_source_name_and_span() {
        let src = "fn double(x), do: x * 2";
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let m = lower_program(&mut crate::types::ConcreteTypes, &prog).expect("lower");
        let f = m.fn_by_name("double").unwrap();
        let param = f.blocks[0].params[0];
        assert_eq!(m.source.var_name_of(param), Some("x"));
        let sp = m.source.var_span_of(param);
        assert!(!sp.is_dummy());
        let txt = &src[sp.start as usize..sp.end as usize];
        assert_eq!(txt, "x");
    }

    /// Every top-level fn gets its source span recorded under
    /// `fn_span[fn_id.0]`.
    #[test]
    fn fn_span_records_def_position() {
        let src = "fn alpha(), do: 1\nfn beta(), do: 2";
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let m = lower_program(&mut crate::types::ConcreteTypes, &prog).expect("lower");
        let beta = m.fn_by_name("beta").unwrap();
        let sp = m.source.fn_span_of(beta.id);
        let txt = &src[sp.start as usize..sp.end as usize];
        assert!(txt.starts_with("fn beta"));
    }

    /// CPS continuations created when a non-tail Call splits use the
    /// originating call expression's span as their `fn_span`, so a
    /// diagnostic on the continuation can point at where the work
    /// originated in source.
    #[test]
    fn continuation_fn_span_points_at_originating_call() {
        // `callee(x) + 1` forces a non-tail Call -> CPS split.
        let src = "fn callee(y), do: y\nfn caller(x), do: callee(x) + 1";
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let m = lower_program(&mut crate::types::ConcreteTypes, &prog).expect("lower");
        let caller = m.fn_by_name("caller").unwrap();
        // The continuation fn is the one whose name starts with "k_".
        // Filter out continuations from the runtime.fz prelude (e.g.
        // Utf8.from_bytes also CPS-splits) by checking FnCategory.
        let k = m
            .fns
            .iter()
            .find(|f| {
                f.name.starts_with("k_")
                    && f.category == crate::fz_ir::FnCategory::CpsCont
                    && f.id.0 >= caller.id.0
            })
            .expect("expected a continuation fn in user code");
        let cont_span = m.source.fn_span_of(k.id);
        assert!(!cont_span.is_dummy());
        // The originating call is `callee(x)` inside `caller`'s body.
        // The continuation's fn_span must be inside caller's source range.
        let caller_span = m.source.fn_span_of(caller.id);
        assert!(
            cont_span.start >= caller_span.start && cont_span.end <= caller_span.end,
            "continuation span {:?} should lie within caller's range {:?}",
            cont_span,
            caller_span
        );
        let txt = &src[cont_span.start as usize..cont_span.end as usize];
        assert!(
            txt.contains("callee"),
            "continuation span should cover the originating call, got {:?}",
            txt
        );
    }

    /// Compiler-introduced Vars (constants, tuple projections, etc.)
    /// keep their source-expression span on `var_span` and an empty
    /// name on `var_name`. .20.8's diagnostic renderer uses the empty-
    /// name signal to render "this value" instead of "`<name>`".
    #[test]
    fn temp_var_records_span_and_empty_name() {
        // `x + 1` produces a Const(1) Var whose source position is the
        // literal `1` in the body.
        let src = "fn add_one(x), do: x + 1";
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let m = lower_program(&mut crate::types::ConcreteTypes, &prog).expect("lower");
        let f = m.fn_by_name("add_one").unwrap();
        // Find a Var bound to `Const(Int(1))`.
        let mut const1_var: Option<Var> = None;
        for blk in &f.blocks {
            for s in &blk.stmts {
                let crate::fz_ir::Stmt::Let(v, prim) = s;
                if matches!(prim, Prim::Const(Const::Int(1))) {
                    const1_var = Some(*v);
                }
            }
        }
        let v = const1_var.expect("Const(1) Var");
        // No source name on this temp.
        assert_eq!(m.source.var_name_of(v), None);
        // But its span points at the `1` literal.
        let sp = m.source.var_span_of(v);
        let txt = &src[sp.start as usize..sp.end as usize];
        assert_eq!(txt, "1");
    }

    fn first_tail_call(m: &crate::fz_ir::Module) -> Option<(crate::fz_ir::FnId, bool)> {
        for f in &m.fns {
            for b in &f.blocks {
                if let Term::TailCall {
                    ident: _,
                    callee,
                    is_back_edge,
                    ..
                } = &b.terminator
                {
                    return Some((*callee, *is_back_edge));
                }
            }
        }
        None
    }

    #[test]
    fn self_recursive_fn_has_back_edge() {
        // fz-qbg.2: with multi-clause body cont fns, prelude multi-clause
        // fns (`print`, `vec_get`) contribute TailCalls to their per-clause
        // cont fns earlier in module order. Look up `loop` specifically
        // rather than the first TailCall anywhere.
        let m = lower_src("fn loop(n), do: loop(n)");
        let loop_fn = m.fn_by_name("loop").expect("loop fn missing");
        let (callee, is_back_edge) = loop_fn
            .blocks
            .iter()
            .find_map(|b| {
                if let Term::TailCall {
                    ident: _,
                    callee,
                    is_back_edge,
                    ..
                } = &b.terminator
                {
                    Some((*callee, *is_back_edge))
                } else {
                    None
                }
            })
            .expect("no TailCall in loop");
        assert!(
            is_back_edge,
            "self-recursion must be a back-edge; callee={:?}",
            callee
        );
    }

    #[test]
    fn non_recursive_call_is_not_back_edge() {
        let m = lower_src("fn id(x), do: x\nfn main(), do: id(1)");
        // Find the TailCall from main to id.
        let mut found = false;
        for f in &m.fns {
            if f.name == "main" {
                for b in &f.blocks {
                    if let Term::TailCall { is_back_edge, .. } = &b.terminator {
                        assert!(!is_back_edge, "non-recursive call must NOT be back-edge");
                        found = true;
                    }
                }
            }
        }
        assert!(found, "no TailCall from main");
    }

    #[test]
    fn back_edge_too_many_args_returns_error() {
        // A self-recursive fn with 9 args exceeds the 8-slot slab limit.
        let err = lower_src_err("fn bigloop(a,b,c,d,e,f,g,h,i), do: bigloop(a,b,c,d,e,f,g,h,i)");
        assert!(
            matches!(err, LowerError::BackEdgeTooManyArgs { arg_count: 9, .. }),
            "expected BackEdgeTooManyArgs(9), got {:?}",
            err
        );
    }

    #[test]
    fn extern_fn_registers_in_module_externs() {
        let toks = Lexer::new("extern \"C\" fn fz_nop(any) :: nil\nfn main() do fz_nop(1) end\n")
            .tokenize()
            .expect("lex");
        let prog = crate::parser::Parser::new(toks)
            .parse_program()
            .expect("parse");
        let (module, _) =
            lower_program_full(&mut crate::types::ConcreteTypes, &prog).expect("lower");
        // 14 runtime.fz externs + 1 user extern = 15 total.
        // fz-ht5 added `fz_make_ref`; fz-swt.7 added `fz_make_resource`;
        // fz-axu.13 added `fz_bitstring_valid_utf8` and
        // `fz_brand_bitstring_as_utf8`.
        assert_eq!(module.externs.len(), 15);
        // fz_nop is at the end (user externs follow runtime.fz externs).
        let nop = module
            .externs
            .iter()
            .find(|e| e.fz_name == "fz_nop")
            .expect("fz_nop not found in externs");
        assert_eq!(nop.params, vec![ExternTy::Any]);
        assert_eq!(nop.ret, ExternTy::Unit);
        // main's IR references fz_nop as the last (user) extern — its index
        // moves whenever runtime.fz grows. The test inspects only that
        // it lands in extern position #(externs.len()-1).
        let last_extern_idx = module.externs.len() - 1;
        let ir = format!("{}", module);
        let needle = format!("extern#{}", last_extern_idx);
        assert!(ir.contains(&needle), "expected {} in IR:\n{}", needle, ir);
    }

    /// fz-0cv — `binary` lowers to ExternTy::Binary; `cstring` lowers to
    /// ExternTy::CString. Both are distinct from ExternTy::Any.
    #[test]
    fn binary_and_cstring_lower_to_distinct_extern_tys() {
        let src = "\
extern \"C\" fn fz_open(cstring, integer) :: integer
extern \"C\" fn fz_write(integer, binary, integer) :: integer
fn main() do fz_open(\"x\", 0) end
";
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = crate::parser::Parser::new(toks)
            .parse_program()
            .expect("parse");
        let (module, _) =
            lower_program_full(&mut crate::types::ConcreteTypes, &prog).expect("lower");
        let open = module
            .externs
            .iter()
            .find(|e| e.fz_name == "fz_open")
            .expect("fz_open missing");
        assert_eq!(open.params, vec![ExternTy::CString, ExternTy::I64]);
        let write = module
            .externs
            .iter()
            .find(|e| e.fz_name == "fz_write")
            .expect("fz_write missing");
        assert_eq!(
            write.params,
            vec![ExternTy::I64, ExternTy::Binary, ExternTy::I64]
        );
        // Sanity: previous `binary` → ExternTy::Any mapping is gone.
        assert_ne!(write.params[1], ExternTy::Any);
    }

    /// fz-eol — `&libc::close/1` resolves to a synthesized top-level
    /// wrapper fn whose body contains a single `Prim::Extern` call. This
    /// is the canonical shape `resolve_dtor_from_closure` walks at
    /// runtime so `make_resource(_, &libc::close/1)` resolves to
    /// libc::close. The wrapper has zero captures so the AOT static dtor
    /// table accepts it. See [[fz-9rs]] for why the simpler "desugar to
    /// lambda" approach doesn't yet work.
    #[test]
    fn fn_ref_to_extern_synthesizes_wrapper() {
        use crate::fz_ir::{Prim, Stmt};
        let src = "\
extern \"C\" fn libc::close(integer) :: integer
fn main() do &libc::close/1 end
";
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = crate::parser::Parser::new(toks)
            .parse_program()
            .expect("parse");
        let (module, _) =
            lower_program_full(&mut crate::types::ConcreteTypes, &prog).expect("lower");
        let wrap = module
            .fns
            .iter()
            .find(|f| f.name.contains("libc::close"))
            .expect("synthesized wrapper not found");
        let has_extern = wrap.blocks.iter().any(|b| {
            b.stmts
                .iter()
                .any(|s| matches!(s, Stmt::Let(_, Prim::Extern(_, _))))
        });
        assert!(
            has_extern,
            "wrapper fn must contain a Prim::Extern statement; got: {}",
            wrap.name
        );
    }

    /// fz-y3k — `extern "C" fn libc::open(path :: cstring, integer) :: integer`
    /// produces an extern whose fz_name carries the `libc::` prefix while
    /// the linker-visible symbol is the bare last segment. Named-typed
    /// params (`path :: cstring`) parse identically to positional ones.
    #[test]
    fn extern_with_library_prefix_splits_fz_name_from_symbol() {
        let src = "\
extern \"C\" fn libc::open(path :: cstring, integer) :: integer
fn main() do libc::open(\"x\", 0) end
";
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = crate::parser::Parser::new(toks)
            .parse_program()
            .expect("parse");
        let (module, _) =
            lower_program_full(&mut crate::types::ConcreteTypes, &prog).expect("lower");
        let open = module
            .externs
            .iter()
            .find(|e| e.fz_name == "libc::open")
            .expect("libc::open missing from module.externs");
        assert_eq!(open.symbol, "open", "linker symbol is the bare suffix");
        assert_eq!(open.params, vec![ExternTy::CString, ExternTy::I64]);
    }

    #[test]
    fn extern_id_is_stable_and_extern_idx_is_consistent() {
        let toks = Lexer::new("extern \"C\" fn fz_nop(any) :: nil\nfn main() do fz_nop(1) end\n")
            .tokenize()
            .expect("lex");
        let prog = crate::parser::Parser::new(toks)
            .parse_program()
            .expect("parse");
        let (module, _) =
            lower_program_full(&mut crate::types::ConcreteTypes, &prog).expect("lower");
        // extern_idx must have an entry for every extern.
        assert_eq!(module.extern_idx.len(), module.externs.len());
        // Each extern's id field must resolve via extern_by_id to itself.
        for (i, e) in module.externs.iter().enumerate() {
            assert_eq!(
                module.extern_idx[&e.id], i,
                "extern_idx out of sync at index {}",
                i
            );
            assert_eq!(module.extern_by_id(e.id).fz_name, e.fz_name);
        }
        // ExternIds are monotonically increasing (counter-based, not len()-based).
        let ids: Vec<u32> = module.externs.iter().map(|e| e.id.0).collect();
        assert!(
            ids.windows(2).all(|w| w[0] < w[1]),
            "ExternIds not monotonic: {:?}",
            ids
        );
    }

    /// fz-f88.5 — every lowered FnIr carries an origin category. This
    /// test pins the contract: prelude fns are `Prelude`, user fns are
    /// `User`, and the well-known synthesized cont families
    /// (fn_clause_, k_, lambda_, if_, case_) map to their respective
    /// variants based on name prefix.
    #[test]
    fn fn_category_tags_match_origin() {
        use crate::fz_ir::FnCategory;
        // Mix user fns covering: multi-clause dispatch (-> MultiClauseCont),
        // CPS-split via non-tail call (-> CpsCont), and lambda lifting
        // (-> LambdaLift).
        let src = "\
fn id(x), do: x
fn pick(:a), do: 1
fn pick(:b), do: 2
fn make_adder(x), do: fn (z) -> x + z

fn main() do
  id(pick(:a))
  make_adder(1)
end
";
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = crate::parser::Parser::new(toks)
            .parse_program()
            .expect("parse");
        let (module, _) =
            lower_program_full(&mut crate::types::ConcreteTypes, &prog).expect("lower");

        let user_names = ["id", "pick", "make_adder", "main"];
        for f in &module.fns {
            let expected = if user_names.contains(&f.name.as_str()) {
                FnCategory::User
            } else if f.name.starts_with("fn_clause_") {
                FnCategory::MultiClauseCont
            } else if f.name.starts_with("lambda_") {
                FnCategory::LambdaLift
            } else if f.name.starts_with("k_") {
                FnCategory::CpsCont
            } else if f.name.contains("_matcher_") {
                // Internal matchers are no longer production lowering
                // artifacts, but keep the category rule for any explicit
                // matcher helper tests that construct such fns.
                FnCategory::Matcher
            } else if f.name.starts_with("if_")
                || f.name.starts_with("case_")
                || f.name.starts_with("cond_")
                || f.name.starts_with("with_")
            {
                FnCategory::ControlFlowCont
            } else {
                // Anything else must be prelude (lowered from runtime.fz or
                // synthesized helpers like fz_spawn_thunk).
                FnCategory::Prelude
            };
            assert_eq!(
                f.category, expected,
                "{} (id {}) categorized as {:?}, expected {:?}",
                f.name, f.id.0, f.category, expected,
            );
        }
    }

    // fz-puj.52.7 — internal case / multi-clause / with-else dispatch no
    // longer mints production matcher fns. Receive remains the ABI-driven
    // matcher-fn path.

    // ----- fz-puj.36 (H7) — Matrix construction from receive clauses -----

    fn parse_receive_clauses(src: &str) -> Vec<crate::ast::MatchClause> {
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = crate::parser::Parser::new(toks)
            .parse_program()
            .expect("parse");
        fn find_receive(e: &crate::ast::Expr) -> Option<&Vec<crate::ast::MatchClause>> {
            match e {
                crate::ast::Expr::Receive { clauses, .. } => Some(clauses),
                crate::ast::Expr::Block(es) => es.iter().find_map(|s| find_receive(&s.node)),
                _ => None,
            }
        }
        for item in &prog.items {
            if let crate::ast::Item::Fn(fd) = item.as_ref() {
                for clause in &fd.clauses {
                    if let Some(rxs) = find_receive(&clause.body.node) {
                        return rxs.clone();
                    }
                }
            }
        }
        panic!("no receive clauses found in source");
    }

    #[test]
    fn build_receive_matrix_one_clause_shape() {
        let clauses = parse_receive_clauses("fn rx() do receive do {:ping, _} -> :pong end end");
        let m = build_receive_matrix(Var(0), &clauses);
        assert_eq!(m.subjects, vec![Var(0)]);
        assert_eq!(m.rows.len(), 1);
        assert_eq!(m.rows[0].patterns.len(), 1);
        assert!(m.rows[0].preconditions.is_empty());
        assert!(m.rows[0].guard.is_none());
        assert_eq!(m.rows[0].body_id, 0);
    }

    #[test]
    fn build_receive_matrix_multi_clause_preserves_order_and_ids() {
        let clauses = parse_receive_clauses(
            "fn rx() do receive do
                :ping -> :pong
                {:msg, _} -> :ok
                _ -> :other
            end end",
        );
        let m = build_receive_matrix(Var(7), &clauses);
        assert_eq!(m.subjects, vec![Var(7)]);
        assert_eq!(m.rows.len(), 3);
        for (i, row) in m.rows.iter().enumerate() {
            assert_eq!(row.body_id, i as crate::pattern_matrix::BodyId);
            assert_eq!(row.patterns.len(), 1);
            assert!(row.preconditions.is_empty());
        }
    }

    #[test]
    fn build_receive_matrix_carries_guard() {
        let clauses = parse_receive_clauses(
            "fn rx() do receive do
                n when n > 0 -> :positive
                _ -> :other
            end end",
        );
        let m = build_receive_matrix(Var(0), &clauses);
        assert_eq!(m.rows.len(), 2);
        assert!(
            m.rows[0].guard.is_some(),
            "first clause's `when n > 0` guard must appear in row[0].guard"
        );
        assert!(m.rows[1].guard.is_none());
    }

    #[test]
    fn case_guard_with_pure_user_fn_inlines_and_lowers() {
        let src = "fn is_pos(n) do n > 0 end
                   fn main() do
                     case 5 do
                       n when is_pos(n) -> :pos
                       _ -> :neg
                     end
                   end";
        let _ = lower_src(src);
    }

    #[test]
    fn case_guard_with_multi_clause_user_fn_lowers_dispatch() {
        let src = "fn is_pos(0) do false end
                   fn is_pos(n) do n > 0 end
                   fn main() do
                     case 5 do
                       n when is_pos(n) -> print(1)
                       _ -> print(0)
                     end
                   end";
        assert_eq!(run_and_capture(src).trim(), "1");
    }

    // ----- fz-yxs (E2) — selective receive lowering -----

    #[test]
    fn lower_receive_one_clause_emits_receive_matched() {
        let src = "fn loop_one() do
              receive do
                {:ping, sender} -> :pong
              end
            end";
        let m = lower_src(src);
        let s = format!("{}", m);
        assert!(
            s.contains("receive_matched [1 clauses]"),
            "expected Term::ReceiveMatched, got:\n{}",
            s
        );
        assert!(
            s.contains("rx_clause_0_body"),
            "expected clause body fn name, got:\n{}",
            s
        );
    }

    #[test]
    fn lower_receive_after_clause_emits_after_body() {
        let src = "fn rx_timeout() do
              receive do
                {:done, x} -> x
              after 100 -> :timeout
              end
            end";
        let m = lower_src(src);
        let s = format!("{}", m);
        assert!(
            s.contains("rx_after_body"),
            "expected after body fn, got:\n{}",
            s
        );
        assert!(
            s.contains("after("),
            "expected after annotation on terminator, got:\n{}",
            s
        );
    }

    #[test]
    fn lower_receive_pinned_resolves_outer_scope() {
        let src = "fn rx_pinned(want) do
              receive do
                {^want, payload} -> payload
              end
            end";
        let m = lower_src(src);
        let s = format!("{}", m);
        assert!(
            s.contains("pinned=[^want="),
            "expected pinned `want` resolved against outer scope, got:\n{}",
            s
        );
    }

    #[test]
    fn lower_receive_pinned_unbound_is_error() {
        let src = "fn rx() do
              receive do
                {^nope, _} -> 0
              end
            end";
        let err = lower_src_err(src);
        match err {
            LowerError::Unbound { name, .. } => {
                assert_eq!(name, "^nope");
            }
            other => panic!("expected Unbound(^nope), got {:?}", other),
        }
    }

    #[test]
    fn lower_receive_typer_accepts_well_formed() {
        // Acceptance bullet: typer accepts well-formed selective receive.
        let src = "fn rx() do
              receive do
                {:ping, _} -> 1
                {:pong, _} -> 2
              end
            end";
        let m = lower_src(src);
        // Typing must not panic and must produce a ModuleTypes for the
        // module. We don't pin the return type — that depends on the
        // body return type which the bodies set to const ints.
        let mut ct = crate::types::ConcreteTypes;
        let mt = crate::ir_typer::type_module(&mut ct, &m, &crate::telemetry::NullTelemetry);
        // No diagnostics from the pure-guard / pure-pattern pass either.
        let diags = crate::ir_typer::collect_diagnostics(&mut ct, &m, &mt);
        let impure: Vec<_> = diags
            .iter()
            .filter(|d| {
                d.code == crate::diag::codes::TYPE_IMPURE_RECEIVE_GUARD
                    || d.code == crate::diag::codes::TYPE_IMPURE_RECEIVE_PATTERN
            })
            .collect();
        assert!(impure.is_empty(), "unexpected purity diags: {:?}", impure);
    }

    #[test]
    fn lower_receive_rejects_impure_guard() {
        // The helper body calls an extern-backed runtime fn, so it cannot
        // lower into the restricted Matcher guard subset.
        let src = "fn helper(), do: make_ref()
            fn rx() do
              receive do
                {:foo, _} when helper() -> 0
              end
            end";
        let err = lower_src_err(src);
        assert!(
            format!("{:?}", err).contains("UnsupportedGuardExpr"),
            "expected restricted guard-lowering error, got {:?}",
            err
        );
    }

    fn first_receive_matcher(m: &Module) -> Option<&crate::matcher::Matcher> {
        for f in &m.fns {
            for b in &f.blocks {
                if let Term::ReceiveMatched { matcher, .. } = &b.terminator {
                    return Some(matcher.as_ref());
                }
            }
        }
        None
    }

    fn matcher_has_guard_dispatch(matcher: &crate::matcher::Matcher) -> bool {
        fn expr_has_dispatch(expr: &crate::matcher::GuardExpr) -> bool {
            match expr {
                crate::matcher::GuardExpr::Dispatch { .. } => true,
                crate::matcher::GuardExpr::Unary { expr, .. } => expr_has_dispatch(expr),
                crate::matcher::GuardExpr::Binary { lhs, rhs, .. } => {
                    expr_has_dispatch(lhs) || expr_has_dispatch(rhs)
                }
                crate::matcher::GuardExpr::Const(_)
                | crate::matcher::GuardExpr::Subject(_)
                | crate::matcher::GuardExpr::Pinned(_) => false,
            }
        }
        matcher.nodes.iter().any(|node| {
            matches!(
                node,
                crate::matcher::MatcherNode::Guard { expr, .. } if expr_has_dispatch(expr)
            )
        })
    }

    #[test]
    fn receive_guard_with_single_clause_helper_lowers_into_matcher() {
        let src = "fn positive(n), do: n > 0
            fn rx() do
              receive do
                n when positive(n) -> n
                _ -> 0
              end
            end";
        let m = lower_src(src);
        let matcher = first_receive_matcher(&m).expect("receive matcher");
        assert!(
            matcher
                .nodes
                .iter()
                .any(|node| matches!(node, crate::matcher::MatcherNode::Guard { .. })),
            "expected inlined helper guard in Matcher: {:#?}",
            matcher
        );
    }

    #[test]
    fn receive_guard_capture_walks_helper_call_args() {
        let src = "fn positive(n), do: n > 0
            fn rx(limit) do
              receive do
                n when positive(n + limit) -> n
                _ -> 0
              end
            end";
        let m = lower_src(src);
        let matcher = first_receive_matcher(&m).expect("receive matcher");
        assert!(
            matcher.pinned.iter().any(|pinned| pinned.name == "limit"),
            "expected guard call argument capture in Matcher pinned inputs: {:#?}",
            matcher
        );
    }

    #[test]
    fn receive_guard_with_transitive_helper_lowers_into_matcher() {
        let src = "fn positive(n), do: n > 0
            fn wanted(n), do: positive(n)
            fn rx() do
              receive do
                n when wanted(n) -> n
                _ -> 0
              end
            end";
        let m = lower_src(src);
        let matcher = first_receive_matcher(&m).expect("receive matcher");
        assert!(
            matcher
                .nodes
                .iter()
                .any(|node| matches!(node, crate::matcher::MatcherNode::Guard { .. })),
            "expected transitive helper guard in Matcher: {:#?}",
            matcher
        );
    }

    #[test]
    fn receive_guard_with_multi_clause_helper_lowers_dispatch() {
        let src = "fn wanted({:ok, n}), do: n > 0
            fn wanted(_), do: false
            fn rx() do
              receive do
                msg when wanted(msg) -> msg
                _ -> 0
              end
            end";
        let m = lower_src(src);
        let matcher = first_receive_matcher(&m).expect("receive matcher");
        assert!(
            matcher_has_guard_dispatch(matcher),
            "expected multi-clause helper guard dispatch in Matcher: {:#?}",
            matcher
        );
    }

    #[test]
    fn receive_guard_helper_dispatch_handles_destructuring() {
        let src = "fn wanted({:ok, {n, _}}), do: n > 0
            fn wanted(_), do: false
            fn rx() do
              receive do
                msg when wanted(msg) -> msg
                _ -> 0
              end
            end";
        let m = lower_src(src);
        let matcher = first_receive_matcher(&m).expect("receive matcher");
        assert!(
            matcher_has_guard_dispatch(matcher),
            "expected nested helper dispatch for destructuring helper: {:#?}",
            matcher
        );
    }

    #[test]
    fn receive_matcher_prepares_heap_map_keys_outside_matcher() {
        let src = "fn rx() do
              receive do
                %{\"id\" => value} -> value
                _ -> 0
              end
            end";
        let m = lower_src(src);
        let matcher = first_receive_matcher(&m).expect("receive matcher");
        assert_eq!(
            matcher.prepared_keys,
            vec![crate::matcher::MatcherConst::Utf8Binary(b"id".to_vec())]
        );
        let s = format!("{}", m);
        assert!(
            s.contains("pinned=[^__matcher_key_0="),
            "expected prepared map key to be threaded as receive pinned input, got:\n{}",
            s
        );
    }

    // ----------------------------------------------------------------
    // fz-axu.24 (M3) — brand-mint visibility gate
    // ----------------------------------------------------------------

    fn module_with_brand_in_fn(
        fn_name: &str,
        brand_tag: &str,
    ) -> (
        Module,
        HashMap<(crate::fz_ir::FnId, crate::fz_ir::BlockId), Vec<Span>>,
    ) {
        use crate::fz_ir::{FnBuilder, FnId, ModuleBuilder, Prim, Term};
        let mut b = FnBuilder::new(FnId(0), fn_name);
        let entry = b.block(vec![]);
        let bs = b.let_(entry, Prim::ConstBitstring(vec![104], 8));
        let branded = b.let_(entry, Prim::Brand(bs, brand_tag.to_string()));
        b.set_terminator(entry, Term::Halt(branded));
        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        (mb.build(), HashMap::new())
    }

    #[test]
    fn brand_visibility_passes_for_builtin_utf8_anywhere() {
        // Built-in `utf8` (no `::` in tag) has no owner; minting it
        // from any fn — even a user module — is allowed.
        let (m, spans) = module_with_brand_in_fn("Mail.send", "utf8");
        let fn_spans = HashMap::new();
        check_brand_visibility(&mut crate::types::ConcreteTypes, &m, &spans, &fn_spans)
            .expect("utf8 mint must be allowed");
    }

    #[test]
    fn brand_visibility_passes_when_fn_owns_brand() {
        // Brand `Mail::Email` minted from fn `Mail.send` (using_module
        // = "Mail") is fine — same owner.
        let (m, spans) = module_with_brand_in_fn("Mail.send", "Mail::Email");
        let fn_spans = HashMap::new();
        check_brand_visibility(&mut crate::types::ConcreteTypes, &m, &spans, &fn_spans)
            .expect("same-module mint must be allowed");
    }

    #[test]
    fn brand_visibility_rejects_cross_module_mint() {
        // Brand `Mail::Email` minted from fn `Other.handler`
        // (using_module = "Other") must be rejected.
        let (m, spans) = module_with_brand_in_fn("Other.handler", "Mail::Email");
        let fn_spans = HashMap::new();
        let err = check_brand_visibility(&mut crate::types::ConcreteTypes, &m, &spans, &fn_spans)
            .expect_err("cross-module mint must be rejected");
        match err {
            LowerError::BrandMintVisibility {
                brand,
                owner_module,
                using_module,
                ..
            } => {
                assert_eq!(brand, "Mail::Email");
                assert_eq!(owner_module, "Mail");
                assert_eq!(using_module, "Other");
            }
            _ => panic!("expected BrandMintVisibility, got {:?}", err),
        }
    }

    #[test]
    fn brand_visibility_rejects_top_level_mint_of_owned_brand() {
        // Top-level fn `main` (no module prefix) trying to mint a
        // module-owned brand is also rejected.
        let (m, spans) = module_with_brand_in_fn("main", "Mail::Email");
        let fn_spans = HashMap::new();
        let err = check_brand_visibility(&mut crate::types::ConcreteTypes, &m, &spans, &fn_spans)
            .expect_err("top-level mint of owned brand must be rejected");
        let diag = err.to_diagnostic();
        assert!(
            diag.message.contains("<top-level>"),
            "diag should mention top-level using_module: {}",
            diag.message,
        );
    }
}
