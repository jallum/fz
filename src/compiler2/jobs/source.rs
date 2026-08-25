use std::collections::HashSet;

use super::super::code::CodeId;
use super::super::drive::{FactKey, JobEffects, current_uses};
use super::super::identity::{FunctionId, FunctionSource, ModuleId, ModuleSourceKind};
use super::super::namespace::{Namespace, NamespaceSymbol};
use super::super::quoted_expander::{
    ExpandedRoot, ExpandedValue, QuotedExpansionCtx, emit_internal_surface_error, emit_job_diagnostic,
    emit_surface_read_error,
};
use super::super::quoted_surface::{read_compiler_fragment_surface, read_scope_surface};
use super::super::scheduler::FatalError;
use super::super::scope::ScopeSnapshot;
use super::super::source::{QuotedLexicalContextKind, QuotedSourceCursor, QuotedSourceRoot};
use super::super::source_publish::{self, ScopePublication};
use super::super::world::World;
use super::super::{QuotedCodeSource, parse_quoted_program};

/// Parses a code submission and records the parts other jobs can ask for later.
///
/// This job stores the parsed top-level AST on the code record and discovers
/// nested module records. It does not scope modules, define functions, lower
/// bodies, or pull in imports.
pub(super) fn index_code(
    world: &mut World,
    tel: &impl crate::telemetry::RawSpanTelemetry,
    code_id: CodeId,
) -> Result<JobEffects, FatalError> {
    let source_name = world
        .code_name(code_id)
        .map(str::to_owned)
        .unwrap_or_else(|| format!("<code:{}>", code_id.as_u32()));
    let source_text = world.code_text(code_id).to_owned();
    let quoted_root = parse_quoted_program(&source_name, &source_text, code_id, tel)
        .map_err(|error| emit_job_diagnostic(tel, error.to_diagnostic()))?;
    let read_surface = if world.is_bootstrap(code_id) {
        read_compiler_fragment_surface
    } else {
        read_scope_surface
    };
    let surface = read_surface(&quoted_root)
        .map_err(|error| emit_surface_read_error(tel, "quoted surface read failed", &error))?;
    let mut outputs = Vec::new();
    let mut changed = Vec::new();
    source_publish::discover_modules(
        world,
        tel,
        code_id,
        ModuleId::GLOBAL,
        &surface,
        &mut outputs,
        &mut changed,
    )?;

    let quoted = QuotedCodeSource {
        quoted: quoted_root,
        surface,
    };
    let code_changed = world.finish_code_index(code_id, quoted);
    outputs.push(FactKey::CodeIndexed(code_id));
    if code_changed {
        changed.push(FactKey::CodeIndexed(code_id));
    }

    Ok(JobEffects {
        outputs,
        changed,
        ..JobEffects::default()
    })
}

/// Builds the namespace for top-level code after parsing has happened.
///
/// If the code has not been indexed yet, this job waits on `CodeIndexed` and
/// asks for `IndexCode`. When the scope is complete, it publishes `CodeScoped`.
pub(super) fn scope_code(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    code_id: CodeId,
) -> Result<JobEffects, FatalError> {
    let Some(source) = world.code_source(code_id) else {
        return Ok(JobEffects::wait_on_current(FactKey::CodeIndexed(code_id)));
    };
    let mut reads = Vec::new();
    let base_namespace = if world.is_runtime_prelude(code_id) {
        Namespace::default()
    } else {
        // Every non-runtime-prelude submission bases off `prelude_head`, which
        // the runtime prelude and any registered extra prelude (e.g. the `fz2
        // test` macro) advance as they scope. Wait on each so their bindings
        // are layered into `prelude_head` before this code reads it.
        for prelude in world.preludes_to_await(code_id) {
            let prelude_fact = FactKey::CodeScoped(prelude);
            if !world.has_fact(&prelude_fact) {
                return Ok(JobEffects::wait_on_current(prelude_fact));
            }
            reads.push(prelude_fact);
        }
        world.prelude_head()
    };
    match source_publish::publish_scope(
        world,
        tel,
        code_id,
        ScopeSnapshot::module(ModuleId::GLOBAL, base_namespace),
        &source.surface,
    )? {
        ScopePublication::Complete {
            namespace,
            reads: scope_reads,
            mut outputs,
            mut changed,
            ..
        } => {
            if world.is_prelude(code_id) {
                world.set_prelude_head(namespace);
            }
            reads.extend(scope_reads);
            let scoped_changed = world.finish_code_scope(code_id, namespace);
            outputs.push(FactKey::CodeScoped(code_id));
            if scoped_changed {
                changed.push(FactKey::CodeScoped(code_id));
            }
            Ok(JobEffects {
                reads: current_uses(reads),
                outputs,
                changed,
                ..JobEffects::default()
            })
        }
        ScopePublication::Blocked(effects) => Ok(effects),
    }
}

/// Builds one module surface when something demands that module.
///
/// A module can only be defined after its parent scope exists. If the parent is
/// not ready, this job waits on the parent fact and schedules the parent job.
/// When ready, it scopes the module body and publishes `ModuleDefined` and
/// `ModuleInterface`.
pub(super) fn define_module(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    module_id: ModuleId,
) -> Result<JobEffects, FatalError> {
    if let Some((source, scope)) = world.module_scope(module_id) {
        let result = match &source.kind {
            ModuleSourceKind::Body(surface) => source_publish::publish_scope(world, tel, source.code, scope, surface)?,
            ModuleSourceKind::Protocol(surface) => source_publish::publish_protocol_surface(
                world,
                tel,
                source.code,
                module_id,
                scope.namespace(),
                surface,
            )?,
            ModuleSourceKind::ProtocolImpl(impl_source) => source_publish::publish_protocol_impl_surface(
                world,
                tel,
                source.code,
                module_id,
                scope.namespace(),
                &impl_source.clone(),
            )?,
        };
        return match result {
            ScopePublication::Complete {
                namespace,
                revision_floor: _revision_floor,
                reads,
                mut outputs,
                mut changed,
                interface,
            } => {
                let interface = world.merge_module_interface_expectations(module_id, interface);
                super::super::drive::ExecutionContext::new(world, tel)
                    .validate_module_interface_expectations(module_id, &interface)?;
                let module_changed = super::super::drive::ExecutionContext::new(world, tel)
                    .define_module(module_id, namespace, interface);
                outputs.push(FactKey::ModuleDefined(module_id));
                outputs.push(FactKey::ModuleInterface(module_id));
                if module_changed {
                    changed.push(FactKey::ModuleDefined(module_id));
                    changed.push(FactKey::ModuleInterface(module_id));
                }
                Ok(JobEffects {
                    reads: current_uses(reads),
                    outputs,
                    changed,
                    ..JobEffects::default()
                })
            }
            ScopePublication::Blocked(effects) => Ok(effects),
        };
    }

    if let Some((code_id, parent_module)) = world.module_indexed_parent(module_id) {
        if parent_module.is_global() {
            return Ok(JobEffects::wait_on_current(FactKey::CodeScoped(code_id)));
        }
        return Ok(JobEffects::wait_on_current(FactKey::ModuleDefined(parent_module)));
    }

    if let Some(parent_module) = world.module_named_parent(module_id) {
        return Ok(JobEffects::wait_on_current(FactKey::ModuleDefined(parent_module)));
    }

    if let Some(code_id) = super::super::drive::ExecutionContext::new(world, tel).ensure_runtime_module(module_id) {
        return Ok(JobEffects::wait_on_current(FactKey::CodeIndexed(code_id)));
    }

    Ok(JobEffects::wait_on_current(FactKey::ModuleIndexed(module_id)))
}

pub(super) fn define_module_interface(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    module_id: ModuleId,
) -> Result<JobEffects, FatalError> {
    if world.module_scope(module_id).is_some() {
        return Ok(JobEffects::wait_on_current(FactKey::ModuleInterface(module_id)));
    }

    let Some(interface) = world.module_interface_if_present(module_id) else {
        return Ok(JobEffects::wait_on_current(FactKey::ModuleIndexed(module_id)));
    };
    let interface = world.merge_module_interface_expectations(module_id, interface);
    super::super::drive::ExecutionContext::new(world, tel)
        .validate_module_interface_expectations(module_id, &interface)?;
    let changed = world.define_module_interface(module_id, interface);
    Ok(JobEffects {
        outputs: vec![FactKey::ModuleInterface(module_id)],
        changed: changed
            .then_some(FactKey::ModuleInterface(module_id))
            .into_iter()
            .collect(),
        ..JobEffects::default()
    })
}

pub(super) fn define_function(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    function_id: super::super::FunctionId,
) -> Result<JobEffects, FatalError> {
    let Some(expanded_source) = world.expanded_function_source(function_id) else {
        return Ok(JobEffects::wait_on_current(FactKey::ExpandedFunctionSource(
            function_id,
        )));
    };
    let Some(raw_source) = world.function_source(function_id) else {
        return Ok(JobEffects::wait_on_current(FactKey::FunctionSource(function_id)));
    };

    let surface = crate::compiler2::quoted_function::derive_function_surface(&expanded_source.source)
        .map_err(|error| emit_surface_read_error(tel, "quoted function decode failed", &error))?;
    let declares_contract = surface.extern_abi.is_some()
        || surface
            .attrs
            .iter()
            .any(|attr| matches!(attr, crate::ast::Attribute::Spec(_)));
    let warnings = if declares_contract {
        crate::compiler2::source_diagnostics::function_body_warnings(&surface)
    } else {
        crate::compiler2::source_diagnostics::function_warnings(&surface)
    };
    for diagnostic in warnings {
        super::super::drive::ExecutionContext::new(world, tel).emit_warning_once(diagnostic);
    }
    source_publish::record_function_type_refs(world, tel, function_id, &surface)?;
    let changed = super::super::drive::ExecutionContext::new(world, tel).define_function(
        function_id,
        raw_source,
        expanded_source,
        surface,
    );
    Ok(JobEffects {
        reads: current_uses([
            FactKey::FunctionSource(function_id),
            FactKey::ExpandedFunctionSource(function_id),
        ]),
        outputs: vec![FactKey::FunctionDefined(function_id)],
        changed: changed
            .then_some(FactKey::FunctionDefined(function_id))
            .into_iter()
            .collect(),
        ..JobEffects::default()
    })
}

/// Mints the consumable `FunctionSource` fact for one function when a reached
/// consumer pulls its body (fz-f98.14.5).
///
/// Scope publication stashes every function's source eagerly but leaves the
/// body cold. This job promotes the one stashed source a consumer asked for,
/// so opening a scope produces no cold body work: a function the program never
/// reaches never reaches this job. If the owning scope has not been walked yet
/// the stash is empty, so it waits on that scope first. `FunctionSource`'s sole
/// producer arm (`World::demand_fact_producer`) is this job, so any consumer
/// blocked on `FunctionSource` restarts it through that map rather than a push.
pub(super) fn publish_function_source_job(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    function_id: super::super::FunctionId,
) -> Result<JobEffects, FatalError> {
    let Some(changed) =
        super::super::drive::ExecutionContext::new(world, tel).publish_pending_function_source(function_id)
    else {
        // The owning scope has not been walked yet, so the stash is empty. Wait
        // on that scope and re-run once it has stashed this body; never wait on
        // `FunctionSource`, the fact this job is the sole producer of.
        //
        // `demand_function_scope` names each fact directly rather than pushing a
        // job: a global-module function waits on `CodeIndexed(code_id)` for
        // every still-`Pending` candidate home (sole producer `Job::IndexCode`)
        // until a home is found, then narrows to that home's
        // `CodeScoped(code_id)` (sole producer `Job::ScopeCode`); a scoped
        // function waits on `ModuleDefined(module)` (sole producer
        // `Job::DefineModule`) -- all three are arms in
        // `World::demand_fact_producer`, and each is wake-coherent: satisfying
        // it re-runs this job at the exact step the next scope fact appears.
        // The satisfying `ScopeCode` co-produces `FunctionSourceStash` in the
        // *same* `JobEffects` as `CodeScoped` (see `source_publish`), so the
        // `CodeScoped`-triggered re-run already finds the stash present -- no
        // separate wait on the stash is needed while a scope fact is named.
        let mut waits: Vec<FactKey> =
            super::super::drive::ExecutionContext::new(world, tel).demand_function_scope(function_id)?;
        if waits.is_empty() {
            // Only the terminal case -- no code names this function's home yet
            // (its owning code has not been submitted, or the reference is
            // dangling) -- falls back to the arm-less
            // `FunctionSourceStash(function_id)` (fz-go4.38). It is the ONLY
            // arm-less wait, correct here because there is no arm-covered fact
            // to name. It must NEVER be bundled with an arm-covered
            // `CodeIndexed`/`CodeScoped` wait: the scheduler re-runs a waiter
            // only when ALL its waits are satisfied (`enqueue_dependents`), so
            // pairing an arm-covered fact (produced now by
            // `IndexCode`/`ScopeCode`) with `FunctionSourceStash` (produced
            // only by a later `ScopeCode`) would AND-block the wake and never
            // fire. Whichever scope eventually stashes this function's body --
            // first pass or a later (re)scope -- bumps this fact and rewakes
            // the job through the standing changed-revision path, never a
            // manual enqueue.
            waits.push(FactKey::FunctionSourceStash(function_id));
        }
        return Ok(JobEffects {
            waits: current_uses(waits),
            ..JobEffects::default()
        });
    };
    Ok(JobEffects {
        // Read the stash fact the scope job that just satisfied us co-produced
        // (fz-go4.38): this is the standing subscription that lets a later
        // (re)scope wake this job through the ordinary changed-revision path
        // instead of a manual enqueue. `stash_function_source` bumps this
        // fact's revision on redefinition, and the scheduler's rebased check
        // re-demands every job whose recorded reads shifted.
        reads: current_uses(vec![FactKey::FunctionSourceStash(function_id)]),
        outputs: vec![FactKey::FunctionSource(function_id)],
        changed: changed
            .then_some(FactKey::FunctionSource(function_id))
            .into_iter()
            .collect(),
        ..JobEffects::default()
    })
}

pub(super) fn expand_function_source(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    function_id: super::super::FunctionId,
) -> Result<JobEffects, FatalError> {
    let Some(source) = world.function_source(function_id) else {
        return Ok(JobEffects::wait_on_current(FactKey::FunctionSource(function_id)));
    };
    match FunctionSourceExpander::new(world, tel, function_id, &source).expand(&source)? {
        FunctionSourceExpansion::Complete { source, reads } => {
            let changed = super::super::drive::ExecutionContext::new(world, tel)
                .note_expanded_function_source(function_id, source);
            let mut reads = reads;
            reads.push(FactKey::FunctionSource(function_id));
            Ok(JobEffects {
                reads: current_uses(reads),
                outputs: vec![FactKey::ExpandedFunctionSource(function_id)],
                changed: changed
                    .then_some(FactKey::ExpandedFunctionSource(function_id))
                    .into_iter()
                    .collect(),
                ..JobEffects::default()
            })
        }
        FunctionSourceExpansion::Blocked(effects) => Ok(*effects),
    }
}

enum FunctionSourceExpansion {
    Complete {
        source: FunctionSource,
        reads: Vec<FactKey>,
    },
    Blocked(Box<JobEffects>),
}

struct FunctionSourceExpander<'world, 'tel, T: crate::telemetry::Telemetry> {
    world: &'world mut World,
    telemetry: &'tel T,
    function: FunctionId,
    current_module: ModuleId,
    namespace: Namespace,
    required_remote_macros: HashSet<FunctionId>,
    reads: Vec<FactKey>,
}

impl<'world, 'tel, T: crate::telemetry::Telemetry> QuotedExpansionCtx for FunctionSourceExpander<'world, 'tel, T> {
    type Telemetry = T;
    fn world(&mut self) -> &mut World {
        self.world
    }

    fn telemetry(&self) -> &T {
        self.telemetry
    }

    fn split(&mut self) -> (&mut World, &T) {
        (self.world, self.telemetry)
    }

    fn current_module(&self) -> ModuleId {
        self.current_module
    }

    fn required_remote_macros(&self) -> &HashSet<FunctionId> {
        &self.required_remote_macros
    }

    fn note_read(&mut self, fact: FactKey) {
        self.reads.push(fact);
    }

    fn lookup_current_module_macro(&mut self, scope: ScopeSnapshot, name: &str, arity: usize) -> Option<FunctionId> {
        match self.world.lookup_callable_namespace(scope.namespace(), name, arity) {
            Some(NamespaceSymbol::Macro(function)) if self.world.function_module(function) == self.current_module => {
                Some(function)
            }
            _ => None,
        }
    }
}

impl<'world, 'tel, T: crate::telemetry::Telemetry> FunctionSourceExpander<'world, 'tel, T> {
    fn new(world: &'world mut World, telemetry: &'tel T, function: FunctionId, source: &FunctionSource) -> Self {
        let current_module = world.function_module(function);
        Self {
            world,
            telemetry,
            function,
            current_module,
            namespace: source.namespace,
            required_remote_macros: source.required_remote_macros.iter().copied().collect(),
            reads: Vec::new(),
        }
    }

    fn expand(mut self, source: &FunctionSource) -> Result<FunctionSourceExpansion, FatalError> {
        // Bind __ENV__ for this body: the definition env, projected from the def
        // scope (so its `function` is this definition) and added to the
        // namespace as a splice. The expander resolves it where the body names
        // __ENV__; it is transient — it is never recorded on the function.
        let def_scope = ScopeSnapshot::function(self.current_module, self.namespace, self.function);
        let builder = source.source.builder();
        let env = self
            .world
            .project_env_value(&builder, def_scope, QuotedLexicalContextKind::Definition)
            .map_err(|error| {
                emit_internal_surface_error(self.telemetry, format!("__ENV__ projection failed: {error}"))
            })?;
        let env = source.source.subroot(env);
        let namespace = self
            .world
            .bind_namespace(self.namespace, "__ENV__", NamespaceSymbol::Splice(env));
        let scope = ScopeSnapshot::function(self.current_module, namespace, self.function);
        let expanded = match self.expand_function_root(source.source.clone(), scope, 0)? {
            ExpandedRoot::Complete(expanded) => expanded,
            ExpandedRoot::Blocked(effects) => {
                return Ok(FunctionSourceExpansion::Blocked(Box::new(
                    self.blocked_effects(*effects),
                )));
            }
        };
        let mut source = source.clone();
        source.source = expanded;
        Ok(FunctionSourceExpansion::Complete {
            source,
            reads: self.reads,
        })
    }

    fn expand_function_root(
        &mut self,
        source: QuotedSourceRoot,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedRoot, FatalError> {
        let cursor = source.cursor();
        if cursor
            .ast_node()
            .map_err(|error| {
                emit_internal_surface_error(self.telemetry, format!("function source read failed: {error}"))
            })?
            .is_some()
        {
            return match self.expand_function_clause(&source, &cursor, scope, depth)? {
                ExpandedValue::Complete(value) => Ok(ExpandedRoot::Complete(source.subroot(value))),
                ExpandedValue::Blocked(effects) => Ok(ExpandedRoot::Blocked(effects)),
            };
        }

        let items = cursor.list_items().map_err(|error| {
            emit_internal_surface_error(self.telemetry, format!("grouped function source read failed: {error}"))
        })?;
        let mut changed = false;
        let mut expanded = Vec::with_capacity(items.len());
        for item in items {
            let Some(node) = item.ast_node().map_err(|error| {
                emit_internal_surface_error(self.telemetry, format!("grouped function item read failed: {error}"))
            })?
            else {
                return Err(emit_internal_surface_error(
                    self.telemetry,
                    "grouped function source expected quoted AST items".to_string(),
                ));
            };
            let head = node.head.atom_name().map_err(|error| {
                emit_internal_surface_error(
                    self.telemetry,
                    format!("grouped function item head read failed: {error}"),
                )
            })?;
            if head.starts_with('@') {
                expanded.push(item.root());
                continue;
            }
            match self.expand_function_clause(&source, &item, scope, depth)? {
                ExpandedValue::Complete(value) => {
                    changed |= value != item.root();
                    expanded.push(value);
                }
                ExpandedValue::Blocked(effects) => return Ok(ExpandedRoot::Blocked(effects)),
            }
        }

        if !changed {
            return Ok(ExpandedRoot::Complete(source));
        }
        let root = source.builder().list(&expanded).map_err(|error| {
            emit_internal_surface_error(
                self.telemetry,
                format!("grouped function source rebuild failed: {error}"),
            )
        })?;
        Ok(ExpandedRoot::Complete(source.subroot(root)))
    }

    fn expand_function_clause(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, FatalError> {
        let Some(node) = cursor.ast_node().map_err(|error| {
            emit_internal_surface_error(self.telemetry, format!("function clause read failed: {error}"))
        })?
        else {
            return Err(emit_internal_surface_error(
                self.telemetry,
                "function source expected a quoted AST node".to_string(),
            ));
        };
        let head = node.head.atom_name().map_err(|error| {
            emit_internal_surface_error(self.telemetry, format!("function clause head read failed: {error}"))
        })?;
        if head == "extern" {
            return Ok(ExpandedValue::Complete(cursor.root()));
        }
        if !matches!(head.as_str(), "fn" | "fnp" | "defmacro") {
            return Err(emit_internal_surface_error(
                self.telemetry,
                format!("function source expected fn/fnp/defmacro/extern, got `{head}`"),
            ));
        }

        let args = node.tail.list_items().map_err(|error| {
            emit_internal_surface_error(self.telemetry, format!("function clause args read failed: {error}"))
        })?;
        let Some(kwargs) = args.get(1) else {
            return Ok(ExpandedValue::Complete(cursor.root()));
        };
        let kw_items = kwargs.list_items().map_err(|error| {
            emit_internal_surface_error(
                self.telemetry,
                format!("function clause keyword args read failed: {error}"),
            )
        })?;

        let mut changed = false;
        let mut expanded_kw = Vec::with_capacity(kw_items.len());
        for kw in kw_items {
            let tuple = kw.tuple_items().map_err(|error| {
                emit_internal_surface_error(self.telemetry, format!("function clause keyword read failed: {error}"))
            })?;
            if tuple.len() != 2 {
                return Err(emit_internal_surface_error(
                    self.telemetry,
                    "function clause expected keyword tuples".to_string(),
                ));
            }
            if tuple[0].atom_name().map_err(|error| {
                emit_internal_surface_error(
                    self.telemetry,
                    format!("function clause keyword name read failed: {error}"),
                )
            })? != "do"
            {
                expanded_kw.push(kw.root());
                continue;
            }

            match self.expand_cursor(owner, &tuple[1], scope, depth)? {
                ExpandedValue::Complete(body) => {
                    if body == tuple[1].root() {
                        expanded_kw.push(kw.root());
                    } else {
                        let rebuilt = owner.builder().tuple(&[tuple[0].root(), body]).map_err(|error| {
                            emit_internal_surface_error(
                                self.telemetry,
                                format!("function clause keyword rebuild failed: {error}"),
                            )
                        })?;
                        expanded_kw.push(rebuilt);
                        changed = true;
                    }
                }
                ExpandedValue::Blocked(effects) => return Ok(ExpandedValue::Blocked(effects)),
            }
        }
        if !changed {
            return Ok(ExpandedValue::Complete(cursor.root()));
        }

        let kw_root = owner.builder().list(&expanded_kw).map_err(|error| {
            emit_internal_surface_error(
                self.telemetry,
                format!("function clause keyword list rebuild failed: {error}"),
            )
        })?;
        let mut expanded_args = args.iter().map(QuotedSourceCursor::root).collect::<Vec<_>>();
        expanded_args[1] = kw_root;
        let tail = owner.builder().list(&expanded_args).map_err(|error| {
            emit_internal_surface_error(
                self.telemetry,
                format!("function clause arg list rebuild failed: {error}"),
            )
        })?;
        let rebuilt = owner
            .builder()
            .tuple(&[node.head.root(), node.meta.root(), tail])
            .map_err(|error| {
                emit_internal_surface_error(self.telemetry, format!("function clause rebuild failed: {error}"))
            })?;
        Ok(ExpandedValue::Complete(rebuilt))
    }

    fn blocked_effects(&self, mut effects: JobEffects) -> JobEffects {
        effects.reads.extend(current_uses(self.reads.clone()));
        effects
    }
}
