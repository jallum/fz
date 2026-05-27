use super::*;
use crate::ast::FnDef;
use crate::diag::Span;
use crate::fz_ir::{
    BlockId, CallsiteId, Const, EmitSlot, ExternArg, ExternDecl, ExternId, FnBuilder, FnId,
    ModuleBuilder, Prim, Term, Var,
};
use std::collections::{HashMap, HashSet};

/// Map of source-fn name -> primary FnId (the entry IR fn for a multi-clause source fn).
pub(super) type FnMap = HashMap<(String, usize), FnId>;

pub struct LowerCtx {
    pub atoms: AtomTable,
    pub externs: ExternTable,
    /// Accumulated ExternDecls; moved into Module.externs after build.
    pub extern_decls: Vec<ExternDecl>,
    /// Monotonic counter for minting stable ExternIds. Mirrors mb.next_fn.
    pub(super) next_extern: u32,
    pub mb: ModuleBuilder,
    pub fns: FnMap,
    /// Currently-being-built fn.
    pub(super) cur: Option<FnBuilder>,
    /// FnId of the fn currently being built. Mirrors `cur` so methods that
    /// record into `source` can key on `(FnId, …)` without unwrapping the
    /// builder.
    pub(super) cur_fn_id: Option<FnId>,
    pub(super) current_owner_module: String,
    /// Currently-active block within `cur`.
    pub(super) cur_block: Option<BlockId>,
    /// Locals env: source name -> IR Var.
    pub(super) env: HashMap<String, Var>,
    /// Order of names in env (for stable captured-list building).
    pub(super) env_order: Vec<String>,
    /// True after an expression sets a terminator on the current block
    /// itself (TailCall, etc.). Caller should NOT overwrite with Return.
    pub(super) terminated: bool,
    pub(super) next_temp: u32,
    /// Accumulating side-tables for source positions. Promoted into
    /// `Module.source` at module-build time. Var spans/names indexed
    /// by `(FnId, Var)`; stmt/term spans by their containing block.
    pub(super) var_meta: HashMap<(FnId, Var), (Span, String)>,
    pub(super) stmt_spans: HashMap<(FnId, BlockId), Vec<Span>>,
    pub(super) term_spans: HashMap<(FnId, BlockId), Span>,
    pub(super) fn_spans: HashMap<FnId, Span>,
    /// fz-eol — lazily synthesized top-level fn wrappers around extern
    /// calls, keyed by ExternId. `&libc::close/1` produces a closure
    /// pointing at the wrapper. The wrapper is a true top-level fn (not
    /// a lambda) so it has *zero captures*, which is what
    /// `static_closure_targets` requires for the AOT dtor table.
    pub(super) extern_wrappers: HashMap<ExternId, FnId>,
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
    /// scope, and restore on exit. PatternMatrix helpers and `lower_pattern_bind`
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
    pub(super) prelude_imports: HashMap<(String, usize), String>,
    pub(super) external_exports: HashMap<(String, usize), crate::modules::identity::ExportKey>,
    pub(super) external_stubs: HashMap<crate::modules::identity::ExportKey, FnId>,
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
            current_owner_module: String::new(),
            cur_block: None,
            env: HashMap::new(),
            env_order: Vec::new(),
            terminated: false,
            next_temp: 0,
            var_meta: HashMap::new(),
            stmt_spans: HashMap::new(),
            term_spans: HashMap::new(),
            fn_spans: HashMap::new(),
            extern_wrappers: HashMap::new(),
            prelude_fn_id_cutoff: 0,
            prelude_type_env: crate::type_expr::ModuleTypeEnv::new(),
            combined_type_env: crate::type_expr::ModuleTypeEnv::new(),
            boundary_fns: HashSet::new(),
            branch_origin: crate::fz_ir::BranchOrigin::User,
            fn_defs_by_arity: HashMap::new(),
            prelude_imports: HashMap::new(),
            external_exports: HashMap::new(),
            external_stubs: HashMap::new(),
        }
    }

    pub(super) fn resolve_prelude_import(&self, name: &str, arity: usize) -> Option<String> {
        self.prelude_imports
            .get(&(name.to_string(), arity))
            .cloned()
    }

    pub(super) fn unique_imported_fn_value_target(&self, name: &str) -> Option<(String, FnId)> {
        let mut matches = self
            .prelude_imports
            .iter()
            .filter(|((imported, _arity), _qualified)| imported == name)
            .map(|((_imported, arity), qualified)| (qualified.clone(), *arity));
        let (qualified, arity) = matches.next()?;
        if matches.next().is_some() {
            return None;
        }
        let fn_id = *self.fns.get(&(qualified.clone(), arity))?;
        Some((qualified, fn_id))
    }

    pub(super) fn register_external_interfaces(
        &mut self,
        interfaces: &std::collections::BTreeMap<
            crate::modules::identity::ModuleName,
            crate::modules::interface::ModuleInterface,
        >,
    ) {
        for (module, interface) in interfaces {
            for export in &interface.exports {
                self.external_exports.insert(
                    (format!("{}.{}", module, export.name), export.arity),
                    crate::modules::identity::ExportKey::new(
                        module.clone(),
                        export.name.clone(),
                        export.arity,
                    ),
                );
            }
        }
    }

    pub(super) fn external_callee(
        &mut self,
        name: &str,
        arity: usize,
    ) -> Option<(FnId, crate::modules::identity::ExportKey)> {
        let target = self
            .external_exports
            .get(&(name.to_string(), arity))?
            .clone();
        let fn_id = if let Some(fn_id) = self.external_stubs.get(&target) {
            *fn_id
        } else {
            let fn_id = self.mb.fresh_fn_id();
            let mut stub = FnBuilder::new(fn_id, format!("__external__.{}", target))
                .with_category(crate::fz_ir::FnCategory::User);
            let params = (0..arity).map(|_| stub.fresh_var()).collect::<Vec<_>>();
            let entry = stub.block(params);
            let atom = self.atoms.intern("external_module_unlinked");
            let reason = stub.let_(entry, Prim::Const(Const::Atom(atom)));
            stub.set_terminator(entry, Term::Halt(reason));
            self.mb.add_fn(stub.build());
            self.external_stubs.insert(target.clone(), fn_id);
            fn_id
        };
        Some((fn_id, target))
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

    /// fz-eol — get-or-build a top-level fn that forwards its args to the
    /// named extern. Used by `&libc::close/1` (and any `&<extern>/<arity>`)
    /// so the resulting closure has a real `FnId` and *zero captures* —
    /// `&name/arity` requires a top-level fn to point at, and only zero-cap
    /// closure targets get static-singleton allocation. The wrapper body
    /// is just `Prim::Extern(eid, params); Return`.
    pub(super) fn ensure_extern_wrapper(&mut self, eid: ExternId) -> FnId {
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
        let mut tb = FnBuilder::new(id, name)
            .with_category(crate::fz_ir::FnCategory::Prelude)
            .with_owner_module(self.current_owner_module.clone());
        let params: Vec<Var> = (0..decl.params.len()).map(|_| tb.fresh_var()).collect();
        let extern_args: Vec<ExternArg> = params
            .iter()
            .copied()
            .zip(decl.params.iter().copied())
            .map(|(var, ty)| ExternArg::fixed(var, ty))
            .collect();
        let entry = tb.block(params);
        let returns_value = !matches!(
            decl.ret,
            crate::fz_ir::ExternTy::Unit | crate::fz_ir::ExternTy::Never
        );
        let ret_var = if returns_value {
            tb.let_(entry, Prim::Extern(eid, extern_args.clone()))
        } else {
            let _ = tb.let_(entry, Prim::Extern(eid, extern_args));
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
    pub(super) fn park(&mut self, v: Var) -> String {
        let name = format!("_t{}", self.next_temp);
        self.next_temp += 1;
        self.bind(&name, v);
        name
    }

    pub(super) fn unpark(&self, name: &str) -> Var {
        self.env.get(name).copied().expect("unpark: missing temp")
    }

    pub(super) fn unbind(&mut self, name: &str) {
        self.env.remove(name);
        if let Some(i) = self.env_order.iter().position(|n| n == name) {
            self.env_order.remove(i);
        }
    }

    pub(super) fn bind(&mut self, name: &str, v: Var) {
        if !self.env.contains_key(name) {
            self.env_order.push(name.to_string());
        }
        self.env.insert(name.to_string(), v);
    }

    pub(super) fn lookup(&self, name: &str) -> Option<Var> {
        self.env.get(name).copied()
    }

    pub(super) fn visible_locals(&self) -> Vec<(String, Var)> {
        let mut out = Vec::with_capacity(self.env_order.len());
        for n in &self.env_order {
            if let Some(v) = self.env.get(n) {
                out.push((n.clone(), *v));
            }
        }
        out
    }

    pub(super) fn cur_mut(&mut self) -> &mut FnBuilder {
        self.cur.as_mut().expect("no current fn")
    }

    pub(super) fn cur_block(&self) -> BlockId {
        self.cur_block.expect("no current block")
    }

    pub(super) fn let_(&mut self, prim: Prim) -> Var {
        self.let_at(prim, Span::DUMMY)
    }

    /// Emit `let v = prim` and record the source span the prim came from.
    /// The resulting Var's metadata defaults to `(span, "")` — anonymous
    /// temp. Callers that bind the Var to a source name follow up with
    /// `name_var(v, name, name_span)`.
    pub(super) fn let_at(&mut self, mut prim: Prim, span: Span) -> Var {
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
    pub(super) fn name_var(&mut self, v: Var, name: &str, span: Span) {
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

    pub(super) fn set_term(&mut self, term: Term) {
        self.set_term_at(term, Span::DUMMY);
    }

    pub(super) fn set_term_at(&mut self, mut term: Term, span: Span) {
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

    pub(super) fn set_external_direct_term_at(
        &mut self,
        mut term: Term,
        span: Span,
        target: crate::modules::identity::ExportKey,
    ) {
        term.set_source_span(span);
        let ident = term
            .ident()
            .expect("external direct call term must carry a callsite ident")
            .clone();
        let caller = self.cur_fn_id.expect("no current fn");
        self.set_term_at(term, Span::DUMMY);
        if !span.is_dummy() {
            self.term_spans.insert((caller, self.cur_block()), span);
        }
        self.mb
            .external_call_edges
            .push(crate::fz_ir::ExternalCallEdge {
                callsite: CallsiteId::new(caller, &ident, EmitSlot::Direct),
                target,
            });
    }
}

impl Default for LowerCtx {
    fn default() -> Self {
        Self::new()
    }
}
