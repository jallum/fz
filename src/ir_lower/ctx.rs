use super::*;
use crate::ast::FnDef;
use crate::diag::Span;
use crate::fz_ir::{
    BlockId, BranchOrigin, CallsiteId, CallsiteIdent, Const, ContinuationProvenance, EmitSlot, ExternArg, ExternDecl,
    ExternId, ExternTy, ExternalCallEdge, FnBuilder, FnCategory, FnId, ModuleBuilder, Prim, ProtocolCallTarget, Term,
    Var,
};
use crate::modules::identity::ExportKey;
use crate::type_expr::ModuleTypeEnv;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;

/// Map of compiler-visible callable name -> primary FnId.
pub(super) type FnMap = HashMap<(String, usize), FnId>;

pub(super) struct LoweringShared {
    pub(super) prelude_type_env: ModuleTypeEnv,
    pub(super) combined_type_env: ModuleTypeEnv,
    pub(super) fn_defs_by_arity: HashMap<(String, usize), FnDef>,
    pub(super) prelude_imports: HashMap<(String, usize), String>,
    pub(super) external_exports: HashMap<(String, usize), ExportKey>,
    pub(super) protocol_callbacks: HashMap<(String, usize), ProtocolCallTarget>,
    pub(super) struct_schemas: BTreeMap<String, Vec<String>>,
}

pub struct LowerCtx {
    pub(super) shared: Arc<LoweringShared>,
    pub atoms: AtomTable,
    pub externs: ExternTable,
    /// Accumulated ExternDecls; moved into Module.externs after build.
    pub extern_decls: Vec<ExternDecl>,
    /// Compiler-seeded monotonic counter for minting new ExternIds during this
    /// lowering session. CompilerWorld owns the canonical extern identity space;
    /// workers only borrow the current frontier.
    pub(super) next_extern: u32,
    pub mb: ModuleBuilder,
    pub fns: FnMap,
    pub(super) local_named_fns: HashMap<(ModuleId, String, usize), FnId>,
    /// Currently-being-built fn.
    pub(super) cur: Option<FnBuilder>,
    /// FnId of the fn currently being built. Mirrors `cur` so methods that
    /// record into `source` can key on `(FnId, …)` without unwrapping the
    /// builder.
    pub(super) cur_fn_id: Option<FnId>,
    pub(super) current_owner_module: String,
    pub(super) current_owner_module_id: ModuleId,
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
    /// Prelude-origin FnIds, including continuations minted while lowering
    /// prelude roots on demand. `build_source_info` ignores their var metadata
    /// so runtime.fz spans do not overwrite user-source spans that share the
    /// same per-fn `Var` numbering.
    pub prelude_fn_ids: HashSet<FnId>,
    /// fz-jg5.12 (RED.9) — FnIds of user fns that carry an `@spec`. Copied
    /// into `Module.boundary_fns` after build. The reducer treats these as
    /// firewalls so a declared spec is honored as a contract.
    pub boundary_fns: HashSet<FnId>,
    /// fz-fyq.1 — `BranchOrigin` tag for any `Term::If` synthesized in the
    /// current lowering scope. Defaults to `User`; entry points that
    /// initiate generated dispatch (fn-clause selection, pattern-bind,
    /// param guards) save the previous value, set their origin for the
    /// scope, and restore on exit. PatternMatrix helpers and `lower_pattern_bind`
    /// read this when emitting their Ifs.
    pub branch_origin: BranchOrigin,
    pub(super) external_stubs: HashMap<ExportKey, FnId>,
    pub(super) imported_fn_value_wrappers: HashMap<ExportKey, FnId>,
    pub(super) protocol_stubs: HashMap<(String, usize), FnId>,
    pub(super) continuation_provenance: HashMap<FnId, ContinuationProvenance>,
}

impl LowerCtx {
    pub fn new(
        shared: Arc<LoweringShared>,
        extern_decls: Vec<ExternDecl>,
        externs: ExternTable,
        next_extern: u32,
    ) -> Self {
        Self {
            shared,
            atoms: AtomTable::default(),
            externs,
            extern_decls,
            next_extern,
            mb: ModuleBuilder::new(),
            fns: HashMap::new(),
            local_named_fns: HashMap::new(),
            cur: None,
            cur_fn_id: None,
            current_owner_module: String::new(),
            current_owner_module_id: ModuleId(u32::MAX),
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
            prelude_fn_ids: HashSet::new(),
            boundary_fns: HashSet::new(),
            branch_origin: BranchOrigin::User,
            external_stubs: HashMap::new(),
            imported_fn_value_wrappers: HashMap::new(),
            protocol_stubs: HashMap::new(),
            continuation_provenance: HashMap::new(),
        }
    }

    pub(super) fn register_local_named_function(&mut self, source: &Mfa, qualified_name: &str, fn_id: FnId) {
        self.local_named_fns
            .insert((source.module_id, source.function_name.clone(), source.arity), fn_id);
        self.fns.insert((qualified_name.to_string(), source.arity), fn_id);
    }

    pub(super) fn local_named_fn(&self, module_id: ModuleId, name: &str, arity: usize) -> Option<FnId> {
        self.local_named_fns.get(&(module_id, name.to_string(), arity)).copied()
    }

    pub(super) fn first_local_named_fn(&self, module_id: ModuleId, name: &str) -> Option<FnId> {
        self.local_named_fns
            .iter()
            .find(|((owner, local_name, _arity), _)| *owner == module_id && local_name == name)
            .map(|(_, fn_id)| *fn_id)
    }

    pub(super) fn register_function_id(&mut self, id: FnId) {
        self.mb.advance_next_fn_to(id.0 + 1);
    }

    pub(super) fn record_continuation_provenance(&mut self, continuation: FnId, provenance: ContinuationProvenance) {
        self.continuation_provenance.insert(continuation, provenance);
    }

    pub(super) fn resolve_prelude_import(&self, name: &str, arity: usize) -> Option<String> {
        self.shared.prelude_imports.get(&(name.to_string(), arity)).cloned()
    }

    pub(super) fn unique_imported_fn_value_target(
        &mut self,
        compiler: &mut CompilerWorld,
        name: &str,
    ) -> Option<(String, FnId)> {
        let mut matches = self
            .shared
            .prelude_imports
            .iter()
            .filter(|((imported, _arity), _qualified)| imported == name)
            .map(|((_imported, arity), qualified)| (qualified.clone(), *arity));
        let (qualified, arity) = matches.next()?;
        if matches.next().is_some() {
            return None;
        }
        let fn_id = self.imported_fn_value_target(compiler, &qualified, arity)?.1;
        Some((qualified, fn_id))
    }

    pub(super) fn imported_fn_value_target(
        &mut self,
        compiler: &mut CompilerWorld,
        qualified: &str,
        arity: usize,
    ) -> Option<(String, FnId)> {
        if let Some(&fn_id) = self.fns.get(&(qualified.to_string(), arity)) {
            return Some((qualified.to_string(), fn_id));
        }
        let target = self
            .shared
            .external_exports
            .get(&(qualified.to_string(), arity))?
            .clone();
        let fn_id = self.ensure_imported_fn_value_wrapper(compiler, target.clone());
        Some((qualified.to_string(), fn_id))
    }

    pub(super) fn protocol_callee(&mut self, compiler: &mut CompilerWorld, name: &str, arity: usize) -> Option<FnId> {
        let key = (name.to_string(), arity);
        let target = self.shared.protocol_callbacks.get(&key)?.clone();
        if let Some(fn_id) = self.protocol_stubs.get(&key).copied() {
            return Some(fn_id);
        }
        let stub_name = format!("__protocol__.{}", name);
        let fn_id = compiler.declare_anonymous_fn(
            self.current_owner_module_id,
            FunctionKind::ProtocolStub,
            stub_name.clone(),
        );
        self.register_function_id(fn_id);
        let mut stub = FnBuilder::new(fn_id, stub_name);
        let params = (0..arity).map(|_| stub.fresh_var()).collect::<Vec<_>>();
        let entry = stub.block(params);
        let atom = self.atoms.intern("protocol_dispatch_unplanned");
        let result = stub.let_(entry, Prim::Const(Const::Atom(atom)));
        stub.set_terminator(entry, Term::Halt(result));
        self.mb.add_fn(stub.build());
        self.mb.protocol_call_targets.insert(fn_id, target);
        self.protocol_stubs.insert(key, fn_id);
        Some(fn_id)
    }

    pub(super) fn external_callee(
        &mut self,
        compiler: &mut CompilerWorld,
        name: &str,
        arity: usize,
    ) -> Option<(FnId, ExportKey)> {
        let target = self.shared.external_exports.get(&(name.to_string(), arity))?.clone();
        let fn_id = self.ensure_external_stub(compiler, target.clone(), arity);
        Some((fn_id, target))
    }

    fn ensure_external_stub(&mut self, compiler: &mut CompilerWorld, target: ExportKey, arity: usize) -> FnId {
        if let Some(fn_id) = self.external_stubs.get(&target) {
            return *fn_id;
        }
        let stub_name = format!("__external__.{}", target);
        let fn_id = compiler.declare_anonymous_fn(
            self.current_owner_module_id,
            FunctionKind::ExternalStub,
            stub_name.clone(),
        );
        self.register_function_id(fn_id);
        let mut stub = FnBuilder::new(fn_id, stub_name).with_category(FnCategory::User);
        let params = (0..arity).map(|_| stub.fresh_var()).collect::<Vec<_>>();
        let entry = stub.block(params);
        let atom = self.atoms.intern("external_module_unlinked");
        let reason = stub.let_(entry, Prim::Const(Const::Atom(atom)));
        stub.set_terminator(entry, Term::Halt(reason));
        self.mb.add_fn(stub.build());
        self.external_stubs.insert(target, fn_id);
        fn_id
    }

    fn ensure_imported_fn_value_wrapper(&mut self, compiler: &mut CompilerWorld, target: ExportKey) -> FnId {
        if let Some(fn_id) = self.imported_fn_value_wrappers.get(&target) {
            return *fn_id;
        }
        let callee = self.ensure_external_stub(compiler, target.clone(), target.arity);
        let wrapper_name = format!("__import_wrap__.{}.{}__{}", target.module, target.name, target.arity);
        let fn_id = compiler.declare_anonymous_fn(
            self.current_owner_module_id,
            FunctionKind::ImportedFnValueWrapper,
            wrapper_name.clone(),
        );
        self.register_function_id(fn_id);
        let mut wrapper = FnBuilder::new(fn_id, wrapper_name)
            .with_category(FnCategory::User)
            .with_owner_module(self.current_owner_module.clone());
        let params = (0..target.arity).map(|_| wrapper.fresh_var()).collect::<Vec<_>>();
        let entry = wrapper.block(params.clone());
        let ident = CallsiteIdent::from_source(Span::DUMMY);
        wrapper.set_terminator(
            entry,
            Term::TailCall {
                ident: ident.clone(),
                callee,
                args: params,
                is_back_edge: false,
            },
        );
        self.mb.add_fn(wrapper.build());
        self.mb.external_call_edges.push(ExternalCallEdge {
            callsite: CallsiteId::new(fn_id, &ident, EmitSlot::Direct),
            target: target.clone(),
        });
        self.imported_fn_value_wrappers.insert(target, fn_id);
        fn_id
    }

    /// Helper: emit an If terminator on the current block using the active
    /// `branch_origin`. Lowering paths that synthesize Ifs use this rather
    /// than constructing `Term::If` directly, so origin propagation is
    /// uniform.
    pub fn set_if_term(&mut self, cond: Var, then_b: BlockId, else_b: BlockId) {
        let origin = self.branch_origin;
        self.set_term(Term::If {
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
    /// is just `Prim::Extern(ident, eid, params); Return`.
    pub(super) fn ensure_extern_wrapper(&mut self, compiler: &mut CompilerWorld, eid: ExternId) -> FnId {
        if let Some(id) = self.extern_wrappers.get(&eid) {
            return *id;
        }
        let decl = self
            .extern_decls
            .iter()
            .find(|d| d.id == eid)
            .expect("ensure_extern_wrapper: eid not in extern_decls")
            .clone();
        // Name carries the fz-visible name verbatim (with `::` if any) so
        // dumps render `&libc::close/1` recognisably.
        let name = format!("__extern_wrap__{}", decl.fz_name);
        let id = compiler.declare_anonymous_fn(self.current_owner_module_id, FunctionKind::ExternWrapper, name.clone());
        self.register_function_id(id);
        let mut tb = FnBuilder::new(id, name)
            .with_category(FnCategory::Prelude)
            .with_owner_module(self.current_owner_module.clone());
        let params: Vec<Var> = (0..decl.params.len()).map(|_| tb.fresh_var()).collect();
        let extern_args: Vec<ExternArg> = params
            .iter()
            .copied()
            .zip(decl.params.iter().copied())
            .map(|(var, ty)| ExternArg::fixed(var, ty))
            .collect();
        let entry = tb.block(params);
        let returns_value = !matches!(decl.ret, ExternTy::Unit | ExternTy::Never);
        let ret_var = if returns_value {
            tb.let_(
                entry,
                Prim::Extern(CallsiteIdent::from_source(Span::DUMMY), eid, extern_args.clone()),
            )
        } else {
            let _ = tb.let_(
                entry,
                Prim::Extern(CallsiteIdent::from_source(Span::DUMMY), eid, extern_args),
            );
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
        // into the prim's intrinsic ident (only `Prim::MakeFnRef`,
        // `Prim::MakeClosure`,
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
        let entry = self.var_meta.entry((fn_id, v)).or_insert((Span::DUMMY, String::new()));
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

    pub(super) fn set_external_direct_term_at(&mut self, mut term: Term, span: Span, target: ExportKey) {
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
        self.mb.external_call_edges.push(ExternalCallEdge {
            callsite: CallsiteId::new(caller, &ident, EmitSlot::Direct),
            target,
        });
    }
}

impl Default for LowerCtx {
    fn default() -> Self {
        Self::new(
            Arc::new(LoweringShared {
                prelude_type_env: ModuleTypeEnv::new(),
                combined_type_env: ModuleTypeEnv::new(),
                fn_defs_by_arity: HashMap::new(),
                prelude_imports: HashMap::new(),
                external_exports: HashMap::new(),
                protocol_callbacks: HashMap::new(),
                struct_schemas: BTreeMap::new(),
            }),
            Vec::new(),
            ExternTable::new(),
            0,
        )
    }
}
