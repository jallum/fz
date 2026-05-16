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

#![allow(dead_code)]

use crate::ast::{
    BinOp as AstBinOp, BitField as AstBitField, BitSize as AstBitSize, Expr, FnClause, FnDef, Item,
    MatchClause, Pattern, Program, Spanned, UnOp as AstUnOp, WithBinding,
};
use crate::diag::Span;
use crate::fz_ir::{
    BinOp, BitFieldIr, BitSizeIr, BlockId, BuiltinId, Const, Cont, ExternDecl, ExternId, ExternTy,
    FnBuilder, FnId, Module, ModuleBuilder, Prim, SourceInfo, Term, UnOp, Var,
};
use std::collections::HashMap;
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
#[derive(Default)]
pub struct AtomTable {
    map: HashMap<String, u32>,
}

impl AtomTable {
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

/// Builtin registry. Stable ids 0..N seeded for the v1 set.
pub struct BuiltinTable {
    map: HashMap<String, BuiltinId>,
}

impl BuiltinTable {
    pub fn new() -> Self {
        // fz-ext.7 — builtins now registered via runtime.fz ExternTable; keep
        // the BuiltinTable empty so call resolution falls through to ExternTable.
        // Removed in fz-ext.8.
        Self {
            map: HashMap::new(),
        }
    }
    pub fn lookup(&self, name: &str) -> Option<BuiltinId> {
        self.map.get(name).copied()
    }
}

impl Default for BuiltinTable {
    fn default() -> Self {
        Self::new()
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
fn extern_ty_from_name(name: &str) -> Option<ExternTy> {
    match name {
        "any" | "integer" | "binary" | "atom" | "bool" => Some(ExternTy::Any),
        "float" => Some(ExternTy::F64),
        "nil" => Some(ExternTy::Unit),
        "never" => Some(ExternTy::Never),
        _ => None,
    }
}

/// Map of source-fn name -> primary FnId (the entry IR fn for a multi-clause source fn).
type FnMap = HashMap<(String, usize), FnId>;

pub struct LowerCtx {
    pub atoms: AtomTable,
    pub builtins: BuiltinTable,
    pub externs: ExternTable,
    /// Accumulated ExternDecls in declaration order; moved into Module.externs after build.
    pub extern_decls: Vec<ExternDecl>,
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
}

impl LowerCtx {
    pub fn new() -> Self {
        Self {
            atoms: AtomTable::default(),
            builtins: BuiltinTable::new(),
            externs: ExternTable::new(),
            extern_decls: Vec::new(),
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
            prelude_fn_id_cutoff: 0,
            prelude_type_env: crate::type_expr::ModuleTypeEnv::new(),
            combined_type_env: crate::type_expr::ModuleTypeEnv::new(),
        }
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
        let mut tb = FnBuilder::new(id, "fz_spawn_thunk".to_string());
        let c = tb.fresh_var();
        let entry = tb.block(vec![c]);
        tb.set_terminator(
            entry,
            Term::TailCallClosure {
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
    fn let_at(&mut self, prim: Prim, span: Span) -> Var {
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

    fn set_term_at(&mut self, term: Term, span: Span) {
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

fn parse_runtime_prelude() -> (Vec<Rc<Item>>, crate::type_expr::ModuleTypeEnv) {
    let toks = crate::lexer::Lexer::new(RUNTIME_FZ)
        .tokenize()
        .expect("runtime.fz lex error (bug in built-in prelude)");
    let (items, attrs) = crate::parser::Parser::new(toks)
        .parse_prelude()
        .expect("runtime.fz parse error (bug in built-in prelude)");
    let env = crate::type_expr::build_module_type_env(&attrs)
        .expect("runtime.fz @type error (bug in built-in prelude)");
    (items, env)
}

pub fn lower_program(prog: &Program) -> Result<Module, LowerError> {
    let (m, _, _) = lower_program_full(prog)?;
    Ok(m)
}

pub fn lower_program_full(prog: &Program) -> Result<(Module, AtomTable, BuiltinTable), LowerError> {
    let mut ctx = LowerCtx::new();

    // Prepend the built-in runtime.fz prelude so its externs and wrapper fns
    // are visible to every user program without an explicit import.
    let (runtime_items, prelude_type_env) = parse_runtime_prelude();
    ctx.prelude_type_env = prelude_type_env.clone();
    // Build the combined type env: prelude aliases + all user-module aliases.
    let mut combined = prelude_type_env;
    for module_env in prog.module_type_envs.values() {
        combined.extend(module_env.iter().map(|(k, v)| (k.clone(), v.clone())));
    }
    ctx.combined_type_env = combined;
    let runtime_item_count = runtime_items.len();
    let all_items: Vec<Rc<Item>> = runtime_items
        .into_iter()
        .chain(prog.items.iter().cloned())
        .collect();

    // Zeroth pass: register extern "C" fn declarations into ExternTable.
    for item in &all_items {
        if let Item::Fn(fn_def) = item.as_ref() {
            if fn_def.extern_abi.is_none() {
                continue;
            }
            let eid = ExternId(ctx.extern_decls.len() as u32);
            let params = vec![ExternTy::Any; fn_def.extern_param_types.len()];
            let (ret, ret_descr) = lower_extern_ret_ty(fn_def, &ctx.prelude_type_env)?;
            ctx.extern_decls.push(ExternDecl {
                fz_name: fn_def.name.clone(),
                symbol: fn_def.name.clone(),
                params,
                ret,
                ret_descr,
            });
            ctx.externs.insert(fn_def.name.clone(), eid);
        }
    }

    // First pass: assign FnIds to every top-level regular (non-extern) FnDef.
    // We split this into two sub-passes (runtime.fz, then user) so we can
    // record prelude_fn_id_cutoff before user fns get their FnIds. The cutoff
    // lets build_source_info ignore prelude var spans, which would otherwise
    // overwrite user-program spans (both fns restart Var numbering at 0).
    for item in all_items.iter().take(runtime_item_count) {
        if let Item::Fn(fn_def) = item.as_ref() {
            if fn_def.extern_abi.is_some() {
                continue;
            }
            let arity = fn_def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
            let id = ctx.mb.fresh_fn_id();
            ctx.fns.insert((fn_def.name.clone(), arity), id);
        }
    }
    // All FnIds assigned so far belong to the prelude.
    ctx.prelude_fn_id_cutoff = ctx.mb.next_fn_id();

    for item in all_items.iter().skip(runtime_item_count) {
        match item.as_ref() {
            Item::Fn(fn_def) => {
                if fn_def.extern_abi.is_some() {
                    continue; // extern decls have no IR body
                }
                let arity = fn_def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
                let id = ctx.mb.fresh_fn_id();
                ctx.fns.insert((fn_def.name.clone(), arity), id);
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

    // Second pass: lower each fn body.
    for item in &all_items {
        if let Item::Fn(fn_def) = item.as_ref()
            && fn_def.extern_abi.is_none()
        {
            lower_fn(&mut ctx, fn_def)?;
        }
    }

    // Take the module out first; `ctx.mb` is moved but `ctx` itself is
    // still usable for source-info collection.
    let mb = std::mem::take(&mut ctx.mb);
    let mut module = mb.build();
    module.source = build_source_info(&module, &ctx);
    module.atom_names = ctx.atoms.names();
    module.externs = std::mem::take(&mut ctx.extern_decls);
    // fz-02r.4 — annotate TailCall back-edges from the structural SCC.
    annotate_back_edges(&mut module, &ctx.fn_spans)?;
    Ok((module, ctx.atoms, ctx.builtins))
}

/// Parse `extern_ret_tokens` into an ExternTy (wire format) and Descr
/// (semantic type for the type system).
///
/// `type_env` is consulted for named type references (e.g. `pid`).
fn lower_extern_ret_ty(
    fn_def: &FnDef,
    type_env: &crate::type_expr::ModuleTypeEnv,
) -> Result<(ExternTy, crate::types::Descr), LowerError> {
    use crate::lexer::Tok;
    let tokens = &fn_def.extern_ret_tokens;

    // Try to resolve via parse_type_expr first (handles named types like `pid`).
    if !tokens.is_empty()
        && let Ok((descr, _)) = crate::type_expr::parse_type_expr(tokens, type_env)
    {
        let wire = descr_to_extern_ty(&descr);
        return Ok((wire, descr));
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
    ty.map(|wire| (wire, crate::types::Descr::any()))
        .ok_or_else(|| LowerError::Unsupported {
            span: fn_def.name_span,
            what: format!(
                "unrecognised return type in `extern fn {}` (expected any/nil/never/float/pid/…)",
                fn_def.name
            ),
        })
}

/// Derive a coarse C-ABI wire type from a semantic Descr.
///
/// Opaque types erase to Any (they are fz tagged values at runtime).
/// Float-only types get the F64 wire. Nil-only → Unit. Never → Never.
/// Everything else → Any (opaque u64 fz value).
fn descr_to_extern_ty(d: &crate::types::Descr) -> ExternTy {
    use crate::types::Descr;
    if d.is_subtype(&Descr::none()) {
        return ExternTy::Never;
    }
    if d.is_subtype(&Descr::nil()) {
        return ExternTy::Unit;
    }
    if d.is_subtype(&Descr::float()) {
        return ExternTy::F64;
    }
    ExternTy::Any
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

fn lower_fn(ctx: &mut LowerCtx, fn_def: &FnDef) -> Result<(), LowerError> {
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

    let mut builder = FnBuilder::new(fn_id, fn_def.name.clone());
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

        for (pv, pat) in param_vars.iter().zip(&clause.params) {
            lower_pattern_bind(ctx, *pv, pat, fail_block)?;
            // Record the pattern's span on the param Var if not yet named
            // by the pattern walker (e.g. tuple-destructured params).
            ctx.name_var(*pv, "", pat.span);
        }
        emit_param_type_guards(ctx, clause, &param_vars, fail_block)?;
        if let Some(g) = &clause.guard {
            let guard_var = lower_expr(ctx, g, false)?;
            let body_b = ctx.cur_mut().block(vec![]);
            ctx.set_term(Term::If(guard_var, body_b, fail_block));
            ctx.cur_block = Some(body_b);
            ctx.terminated = false;
        }
        let result = lower_expr(ctx, &clause.body, /* is_tail */ true)?;
        if !ctx.terminated {
            ctx.set_term(Term::Return(result));
        }
    } else {
        lower_multi_clause(ctx, fn_def, &param_vars, entry)?;
    }

    let built = ctx.cur.take().unwrap().build();
    ctx.mb.add_fn(built);
    ctx.cur_block = None;
    Ok(())
}

/// fz-ty1.9 — Emit TypeTest guards for `fn f(x :: T)` parameter annotations.
/// For each param that has a type annotation, emit a `TypeTest(pv, descr)`
/// stmt and branch: pass → continue to next block, fail → `on_fail` block.
fn emit_param_type_guards(
    ctx: &mut LowerCtx,
    clause: &FnClause,
    param_vars: &[Var],
    on_fail: BlockId,
) -> Result<(), LowerError> {
    for (pv, type_toks_opt) in param_vars.iter().zip(&clause.param_type_tokens) {
        let toks = match type_toks_opt {
            Some(t) => t,
            None => continue,
        };
        let descr = match crate::type_expr::parse_type_expr(toks, &ctx.combined_type_env) {
            Ok((d, _)) => d,
            Err(_) => continue,
        };
        let tt_var = ctx.let_(crate::fz_ir::Prim::TypeTest(*pv, Box::new(descr)));
        let pass_b = ctx.cur_mut().block(vec![]);
        ctx.set_term(crate::fz_ir::Term::If(tt_var, pass_b, on_fail));
        ctx.cur_block = Some(pass_b);
        ctx.terminated = false;
    }
    Ok(())
}

fn lower_multi_clause(
    ctx: &mut LowerCtx,
    fn_def: &FnDef,
    param_vars: &[Var],
    entry: BlockId,
) -> Result<(), LowerError> {
    // Plan: entry already exists, current_block points to it.
    // For each clause, allocate a "try" block (no params; relies on params being
    // available via Var ids that are stable within this FnIr). Entry Goto's
    // first try block. Each try block tests its patterns; on success, runs the
    // body and returns; on fail, Goto's the next try block (or fail block).

    // Allocate try blocks up front so terminators can reference them.
    let try_blocks: Vec<BlockId> = (0..fn_def.clauses.len())
        .map(|_| ctx.cur_mut().block(vec![]))
        .collect();
    let fail_block = ctx.cur_mut().block(vec![]);

    // Seal fail_block FIRST so CPS-split during clause body lowering can't orphan it.
    ctx.cur_block = Some(fail_block);
    let fc = ctx.atoms.intern("function_clause");
    let v = ctx.let_(Prim::Const(Const::Atom(fc)));
    ctx.set_term(Term::Halt(v));

    // Entry -> first try block.
    ctx.cur_mut()
        .set_terminator(entry, Term::Goto(try_blocks[0], vec![]));

    for (i, clause) in fn_def.clauses.iter().enumerate() {
        let next = try_blocks.get(i + 1).copied().unwrap_or(fail_block);
        ctx.cur_block = Some(try_blocks[i]);
        ctx.env.clear();
        ctx.env_order.clear();
        ctx.terminated = false;
        for (pv, pat) in param_vars.iter().zip(&clause.params) {
            lower_pattern_bind(ctx, *pv, pat, next)?;
        }
        emit_param_type_guards(ctx, clause, param_vars, next)?;
        if let Some(g) = &clause.guard {
            let guard_var = lower_expr(ctx, g, false)?;
            let body_b = ctx.cur_mut().block(vec![]);
            ctx.set_term(Term::If(guard_var, body_b, next));
            ctx.cur_block = Some(body_b);
            ctx.terminated = false;
        }
        let result = lower_expr(ctx, &clause.body, /* is_tail */ true)?;
        if !ctx.terminated {
            ctx.set_term(Term::Return(result));
        }
    }

    Ok(())
}

fn lower_expr(ctx: &mut LowerCtx, e: &Spanned<Expr>, is_tail: bool) -> Result<Var, LowerError> {
    let sp = e.span;
    match &e.node {
        Expr::Int(n) => Ok(ctx.let_at(Prim::Const(Const::Int(*n)), sp)),
        Expr::Float(x) => Ok(ctx.let_at(Prim::Const(Const::Float(*x)), sp)),
        Expr::Str(s) => Ok(ctx.let_at(Prim::Const(Const::Str(s.clone())), sp)),
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
            // closure pointing at the fn's IR id. Picks the first matching
            // arity if the source has multiple (fz currently has no syntax
            // to disambiguate `&name/arity`; the first defined wins).
            if let Some((_, fn_id)) = ctx
                .fns
                .iter()
                .find(|((n, _), _)| n == name)
                .map(|(k, v)| (k.clone(), *v))
            {
                return Ok(ctx.let_(Prim::MakeClosure(fn_id, vec![])));
            }
            Err(LowerError::Unbound {
                span: sp,
                name: name.clone(),
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

        Expr::If(cond, then_e, else_opt) => lower_if(ctx, cond, then_e, else_opt, is_tail),

        Expr::Match(pat, expr) => {
            let v = lower_expr(ctx, expr, false)?;
            let fail_block = ctx.cur_mut().block(vec![]);
            lower_pattern_bind(ctx, v, pat, fail_block)?;
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
                let wrapper = ctx.let_at(Prim::MakeClosure(thunk_id, vec![arg_vars[0]]), sp);
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
            // Builtin fallback — empty in fz-ext.7; fully removed in fz-ext.8.
            if let Some(bid) = ctx.builtins.lookup(&callee_name) {
                return Ok(ctx.let_at(Prim::Builtin(bid, arg_vars), sp));
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

        Expr::Lambda(params, body) => lower_lambda(ctx, params, body),

        Expr::Case(subject, clauses) => lower_case(ctx, subject, clauses, is_tail),
        Expr::Cond(arms) => lower_cond(ctx, arms, is_tail),
        Expr::With(bindings, body, else_clauses) => {
            lower_with(ctx, bindings, body, else_clauses, is_tail)
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

fn lower_if(
    ctx: &mut LowerCtx,
    cond: &Spanned<Expr>,
    then_e: &Spanned<Expr>,
    else_opt: &Option<Box<Spanned<Expr>>>,
    is_tail: bool,
) -> Result<Var, LowerError> {
    let cv = lower_expr(ctx, cond, false)?;
    let then_b = ctx.cur_mut().block(vec![]);
    let else_b = ctx.cur_mut().block(vec![]);
    let join_param = ctx.cur_mut().fresh_var();
    let join_b = ctx.cur_mut().block(vec![join_param]);
    ctx.set_term(Term::If(cv, then_b, else_b));

    let saved_env = ctx.env.clone();
    let saved_order = ctx.env_order.clone();

    ctx.cur_block = Some(then_b);
    let tv = lower_expr(ctx, then_e, is_tail)?;
    ctx.set_term(Term::Goto(join_b, vec![tv]));

    ctx.env = saved_env.clone();
    ctx.env_order = saved_order.clone();
    ctx.cur_block = Some(else_b);
    let ev = if let Some(else_e) = else_opt {
        lower_expr(ctx, else_e, is_tail)?
    } else {
        ctx.let_(Prim::Const(Const::Nil))
    };
    ctx.set_term(Term::Goto(join_b, vec![ev]));

    ctx.env = saved_env;
    ctx.env_order = saved_order;
    ctx.cur_block = Some(join_b);
    Ok(join_param)
}

fn lower_lambda(
    ctx: &mut LowerCtx,
    params: &[Spanned<Pattern>],
    body: &Spanned<Expr>,
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

    let mut lam_builder = FnBuilder::new(lam_id, format!("lambda_{}", lam_id.0));
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

    Ok(ctx.let_(Prim::MakeClosure(lam_id, captured_vars)))
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

    let mut kbuilder = FnBuilder::new(cont_id, format!("k_{}", cont_id.0));
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
    let mut kbuilder = FnBuilder::new(cont_id, format!("k_receive_{}", cont_id.0));
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
    let mut kbuilder = FnBuilder::new(cont_id, format!("k_{}", cont_id.0));
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
        Pattern::Int(n) => emit_eq_check(ctx, subject, Prim::Const(Const::Int(*n)), fail_block),
        Pattern::Float(x) => emit_eq_check(ctx, subject, Prim::Const(Const::Float(*x)), fail_block),
        Pattern::Str(s) => {
            emit_eq_check(ctx, subject, Prim::Const(Const::Str(s.clone())), fail_block)
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
        Pattern::Tuple(elems) => {
            for (i, elem_pat) in elems.iter().enumerate() {
                let fv = ctx.let_(Prim::TupleField(subject, i as u32));
                lower_pattern_bind(ctx, fv, elem_pat, fail_block)?;
            }
            Ok(())
        }
        Pattern::List(elems, tail) => {
            let mut cur = subject;
            for elem_pat in elems {
                let isnil = ctx.let_(Prim::ListIsNil(cur));
                let cont_b = ctx.cur_mut().block(vec![]);
                ctx.set_term(Term::If(isnil, fail_block, cont_b));
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
                    let isnil = ctx.let_(Prim::ListIsNil(cur));
                    let cont_b = ctx.cur_mut().block(vec![]);
                    ctx.set_term(Term::If(isnil, cont_b, fail_block));
                    ctx.cur_block = Some(cont_b);
                    Ok(())
                }
            }
        }
        Pattern::Map(entries) => {
            // For each (key_pattern, value_pattern) in the map pattern: build the
            // key (must be a literal expression-equivalent), call MapGet, ensure
            // result is non-nil (key present), then recurse into value pattern.
            for (key_pat, val_pat) in entries {
                let key_var = lower_pattern_as_key_expr(ctx, key_pat)?;
                let got = ctx.let_(Prim::MapGet(subject, key_var));
                let nil_v = ctx.let_(Prim::Const(Const::Nil));
                let is_nil = ctx.let_(Prim::BinOp(BinOp::Eq, got, nil_v));
                let cont_b = ctx.cur_mut().block(vec![]);
                ctx.set_term(Term::If(is_nil, fail_block, cont_b));
                ctx.cur_block = Some(cont_b);
                lower_pattern_bind(ctx, got, val_pat, fail_block)?;
            }
            Ok(())
        }
        Pattern::Bitstring(fields) => {
            // Initialize a reader, then per field: read with size resolved
            // against any IR vars bound by *earlier* fields' patterns; check
            // success; pattern-bind the extracted value (which may bind names
            // visible to later fields' size resolution); thread the new
            // reader. Finally require the reader is fully consumed.
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
                ctx.set_term(Term::If(ok, cont_b, fail_block));
                ctx.cur_block = Some(cont_b);
                let extracted = ctx.let_(Prim::TupleField(result, 1));
                let next_reader = ctx.let_(Prim::TupleField(result, 2));
                // Park reader so any CPS-split inside the pattern keeps it.
                let r_park = ctx.park(next_reader);
                lower_pattern_bind(ctx, extracted, &field.value, fail_block)?;
                reader = ctx.unpark(&r_park);
                ctx.unbind(&r_park);
            }
            // Require empty reader.
            let done = ctx.let_(Prim::BitReaderDone(reader));
            let cont_b = ctx.cur_mut().block(vec![]);
            ctx.set_term(Term::If(done, cont_b, fail_block));
            ctx.cur_block = Some(cont_b);
            Ok(())
        }
    }
}

/// Lower a Pattern that represents a map key. Map keys in patterns are
/// constants (atoms, ints, strings, ...) — no var-binding allowed.
fn lower_pattern_as_key_expr(ctx: &mut LowerCtx, sp: &Spanned<Pattern>) -> Result<Var, LowerError> {
    Ok(match &sp.node {
        Pattern::Int(n) => ctx.let_(Prim::Const(Const::Int(*n))),
        Pattern::Float(x) => ctx.let_(Prim::Const(Const::Float(*x))),
        Pattern::Str(s) => ctx.let_(Prim::Const(Const::Str(s.clone()))),
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
    ctx.set_term(Term::If(eq_v, cont_b, fail_block));
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
) -> Result<Var, LowerError> {
    if clauses.is_empty() {
        return Err(LowerError::Unsupported {
            span: subject.span,
            what: "case with no clauses".into(),
        });
    }
    let sv = lower_expr(ctx, subject, false)?;
    let subject_park = ctx.park(sv);

    // Allocate try blocks + fail block + join block.
    let try_blocks: Vec<BlockId> = (0..clauses.len())
        .map(|_| ctx.cur_mut().block(vec![]))
        .collect();
    let fail_block = ctx.cur_mut().block(vec![]);
    let join_param = ctx.cur_mut().fresh_var();
    let join_b = ctx.cur_mut().block(vec![join_param]);

    // Seal fail block with halt :case_clause.
    let saved_block = ctx.cur_block();
    ctx.cur_block = Some(fail_block);
    let cc = ctx.atoms.intern("case_clause");
    let v = ctx.let_(Prim::Const(Const::Atom(cc)));
    ctx.set_term(Term::Halt(v));
    ctx.cur_block = Some(saved_block);

    // Goto the first try block.
    ctx.set_term(Term::Goto(try_blocks[0], vec![]));

    let saved_env = ctx.env.clone();
    let saved_order = ctx.env_order.clone();

    for (i, clause) in clauses.iter().enumerate() {
        if let Some(_g) = &clause.guard {
            return Err(LowerError::Unsupported {
                span: clause.span,
                what: "case guard (deferred)".into(),
            });
        }
        let next = try_blocks.get(i + 1).copied().unwrap_or(fail_block);
        ctx.cur_block = Some(try_blocks[i]);
        ctx.env = saved_env.clone();
        ctx.env_order = saved_order.clone();
        ctx.terminated = false;
        let subj_v = ctx.unpark(&subject_park);
        // Re-park so subsequent clauses still see it.
        let inner_park = ctx.park(subj_v);
        lower_pattern_bind(ctx, subj_v, &clause.pattern, next)?;
        ctx.unbind(&inner_park);
        let result = lower_expr(ctx, &clause.body, is_tail)?;
        if !ctx.terminated {
            ctx.set_term(Term::Goto(join_b, vec![result]));
        }
    }

    ctx.unbind(&subject_park);
    ctx.env = saved_env;
    ctx.env_order = saved_order;
    ctx.cur_block = Some(join_b);
    Ok(join_param)
}

fn lower_cond(
    ctx: &mut LowerCtx,
    arms: &[(Spanned<Expr>, Spanned<Expr>)],
    is_tail: bool,
) -> Result<Var, LowerError> {
    // cond is right-associative: each arm is a fresh test/body; on test false,
    // fall through to the next arm. If all fail, halt :cond_clause.
    if arms.is_empty() {
        let cc = ctx.atoms.intern("cond_clause");
        let v = ctx.let_(Prim::Const(Const::Atom(cc)));
        ctx.set_term(Term::Halt(v));
        ctx.terminated = true;
        return Ok(Var(0));
    }

    let join_param = ctx.cur_mut().fresh_var();
    let join_b = ctx.cur_mut().block(vec![join_param]);
    let arm_test_blocks: Vec<BlockId> = (0..arms.len())
        .map(|_| ctx.cur_mut().block(vec![]))
        .collect();
    let fail_block = ctx.cur_mut().block(vec![]);
    let saved_blk = ctx.cur_block();
    ctx.cur_block = Some(fail_block);
    let cc = ctx.atoms.intern("cond_clause");
    let v = ctx.let_(Prim::Const(Const::Atom(cc)));
    ctx.set_term(Term::Halt(v));
    ctx.cur_block = Some(saved_blk);
    ctx.set_term(Term::Goto(arm_test_blocks[0], vec![]));

    let saved_env = ctx.env.clone();
    let saved_order = ctx.env_order.clone();

    for (i, (test, body)) in arms.iter().enumerate() {
        let next = arm_test_blocks.get(i + 1).copied().unwrap_or(fail_block);
        ctx.cur_block = Some(arm_test_blocks[i]);
        ctx.env = saved_env.clone();
        ctx.env_order = saved_order.clone();
        ctx.terminated = false;
        let cv = lower_expr(ctx, test, false)?;
        let body_b = ctx.cur_mut().block(vec![]);
        ctx.set_term(Term::If(cv, body_b, next));
        ctx.cur_block = Some(body_b);
        let result = lower_expr(ctx, body, is_tail)?;
        if !ctx.terminated {
            ctx.set_term(Term::Goto(join_b, vec![result]));
        }
    }

    ctx.env = saved_env;
    ctx.env_order = saved_order;
    ctx.cur_block = Some(join_b);
    Ok(join_param)
}

fn lower_with(
    ctx: &mut LowerCtx,
    bindings: &[WithBinding],
    body: &Spanned<Expr>,
    else_clauses: &[MatchClause],
    is_tail: bool,
) -> Result<Var, LowerError> {
    // Plan: each binding in turn evaluates an expression. For Match(pat, expr):
    //   evaluate expr; match pat against it; if mismatch, jump to a shared
    //   "with_fail" join (carrying the unmatched value). If all match, evaluate
    //   the body and goto join_b with its result. with_fail dispatches to
    //   else_clauses (case-style on the unmatched value); if none match, halt
    //   :with_clause.
    let join_param = ctx.cur_mut().fresh_var();
    let join_b = ctx.cur_mut().block(vec![join_param]);

    // with_fail receives the unmatched value as a block param, then dispatches.
    let with_fail_param = ctx.cur_mut().fresh_var();
    let with_fail = ctx.cur_mut().block(vec![with_fail_param]);

    let saved_env = ctx.env.clone();
    let saved_order = ctx.env_order.clone();

    // -- with_fail block: case-on the unmatched value.
    {
        let saved_blk = ctx.cur_block();
        ctx.cur_block = Some(with_fail);
        if else_clauses.is_empty() {
            // No else: halt :with_clause (re-raise the unmatched value).
            let cc = ctx.atoms.intern("with_clause");
            let v = ctx.let_(Prim::Const(Const::Atom(cc)));
            ctx.set_term(Term::Halt(v));
        } else {
            // Build try blocks + fail.
            let try_blocks: Vec<BlockId> = (0..else_clauses.len())
                .map(|_| ctx.cur_mut().block(vec![]))
                .collect();
            let else_fail = ctx.cur_mut().block(vec![]);
            let saved_b2 = ctx.cur_block();
            ctx.cur_block = Some(else_fail);
            let cc = ctx.atoms.intern("with_clause");
            let v = ctx.let_(Prim::Const(Const::Atom(cc)));
            ctx.set_term(Term::Halt(v));
            ctx.cur_block = Some(saved_b2);
            ctx.set_term(Term::Goto(try_blocks[0], vec![]));
            for (i, clause) in else_clauses.iter().enumerate() {
                if let Some(_g) = &clause.guard {
                    return Err(LowerError::Unsupported {
                        span: clause.span,
                        what: "with-else guard (deferred)".into(),
                    });
                }
                let next = try_blocks.get(i + 1).copied().unwrap_or(else_fail);
                ctx.cur_block = Some(try_blocks[i]);
                ctx.env = saved_env.clone();
                ctx.env_order = saved_order.clone();
                ctx.terminated = false;
                lower_pattern_bind(ctx, with_fail_param, &clause.pattern, next)?;
                let result = lower_expr(ctx, &clause.body, is_tail)?;
                if !ctx.terminated {
                    ctx.set_term(Term::Goto(join_b, vec![result]));
                }
            }
        }
        ctx.cur_block = Some(saved_blk);
        ctx.env = saved_env.clone();
        ctx.env_order = saved_order.clone();
    }

    // -- main path: walk bindings.
    for binding in bindings {
        match binding {
            WithBinding::Bare(e) => {
                lower_expr(ctx, e, false)?;
            }
            WithBinding::Match(pat, e) => {
                let v = lower_expr(ctx, e, false)?;
                // Park v so that any CPS-split during pattern lowering rebinds it.
                let v_park = ctx.park(v);
                // Custom mismatch path: build a per-binding "mismatch" block
                // that gotos with_fail with the unmatched value.
                let mismatch_b = ctx.cur_mut().block(vec![]);
                let saved_blk = ctx.cur_block();
                ctx.cur_block = Some(mismatch_b);
                let v_in_mismatch = ctx.unpark(&v_park);
                ctx.set_term(Term::Goto(with_fail, vec![v_in_mismatch]));
                ctx.cur_block = Some(saved_blk);
                let v_resolved = ctx.unpark(&v_park);
                ctx.unbind(&v_park);
                lower_pattern_bind(ctx, v_resolved, pat, mismatch_b)?;
            }
        }
    }

    let result = lower_expr(ctx, body, is_tail)?;
    if !ctx.terminated {
        ctx.set_term(Term::Goto(join_b, vec![result]));
    }

    ctx.env = saved_env;
    ctx.env_order = saved_order;
    ctx.cur_block = Some(join_b);
    Ok(join_param)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    fn lower_src(src: &str) -> Module {
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        lower_program(&prog).expect("lower failed")
    }

    fn lower_src_err(src: &str) -> LowerError {
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        lower_program(&prog).expect_err("expected lower error")
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
    fn lower_if_uses_join_block() {
        let m = lower_src("fn pos(x), do: if x > 0, do: 1, else: -1");
        let s = format!("{}", m);
        assert!(s.contains("if v"), "expected If terminator: {}", s);
        assert!(s.contains("goto bb"), "expected Goto to join: {}", s);
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

    #[test]
    fn multi_clause_dispatch_emits_try_blocks() {
        let m = lower_src("fn fact(0), do: 1\nfn fact(n), do: n * fact(n - 1)");
        let s = format!("{}", m);
        assert!(s.contains("goto bb"), "got:\n{}", s);
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
        // fz_spawn_opt = ExternId(6) in runtime.fz (0-based, after fz_spawn=5).
        assert!(
            s.contains("extern#6("),
            "expected Extern(fz_spawn_opt=6, ...) in IR:\n{}",
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
    fn case_lowers_to_try_chain() {
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
        assert!(s.contains("if v"), "expected if for pattern check: {}", s);
        assert!(
            s.contains("goto bb"),
            "expected goto for fallthrough: {}",
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
        let m = lower_program(&prog).expect("lower");
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
        let m = lower_program(&prog).expect("lower");
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
        let m = lower_program(&prog).expect("lower");
        let caller = m.fn_by_name("caller").unwrap();
        // The continuation fn is the one whose name starts with "k_".
        let k = m
            .fns
            .iter()
            .find(|f| f.name.starts_with("k_"))
            .expect("expected a continuation fn");
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
        let m = lower_program(&prog).expect("lower");
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
        let m = lower_src("fn loop(n), do: loop(n)");
        let (callee, is_back_edge) = first_tail_call(&m).expect("no TailCall");
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
        let (module, _, _) = lower_program_full(&prog).expect("lower");
        // 9 runtime.fz externs + 1 user extern = 10 total.
        assert_eq!(module.externs.len(), 10);
        // fz_nop is at the end (user externs follow runtime.fz externs).
        let nop = module
            .externs
            .iter()
            .find(|e| e.fz_name == "fz_nop")
            .expect("fz_nop not found in externs");
        assert_eq!(nop.params, vec![ExternTy::Any]);
        assert_eq!(nop.ret, ExternTy::Unit);
        // main's IR should contain Extern(9, [...]) — fz_nop is ExternId(9).
        let ir = format!("{}", module);
        assert!(ir.contains("extern#9"), "expected extern#9 in IR:\n{}", ir);
    }
}
