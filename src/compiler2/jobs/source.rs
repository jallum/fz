use std::collections::HashSet;

use super::super::code::CodeId;
use super::super::drive::{FactKey, Job, JobEffects};
use super::super::identity::{FunctionId, FunctionSource, ModuleId, ModuleSourceKind};
use super::super::namespace::{Namespace, NamespaceSymbol};
use super::super::quoted_expander::{
    ExpandedRoot, ExpandedValue, QuotedExpansionCtx, emit_internal_surface_error, emit_job_diagnostic,
};
use super::super::quoted_surface::{SurfaceSourceContext, read_compiler_fragment_surface, read_scope_surface};
use super::super::scheduler::FatalError;
use super::super::scope::ScopeSnapshot;
use super::super::source::{QuotedSourceCursor, QuotedSourceRoot};
use super::super::source_publish::{self, ScopePublication};
use super::super::world::World;
use super::super::{QuotedCodeSource, parse_quoted_program};

/// Parses a code submission and records the parts other jobs can ask for later.
///
/// This job stores the parsed top-level AST on the code record and discovers
/// nested module records. It does not scope modules, define functions, lower
/// bodies, or pull in imports.
pub(super) fn index_code(world: &mut World<'_>, code_id: CodeId) -> Result<JobEffects, FatalError> {
    let source_name = world
        .code_name(code_id)
        .map(str::to_owned)
        .unwrap_or_else(|| format!("<code:{}>", code_id.as_u32()));
    let source_text = world.code_text(code_id).to_owned();
    let quoted_root = parse_quoted_program(source_name.clone(), &source_text, world.tel())
        .map_err(|error| emit_job_diagnostic(world, error.to_diagnostic()))?;
    let ctx = SurfaceSourceContext::new(code_id, &source_text);
    let read_surface = if world.is_runtime_prelude(code_id) || world.is_runtime_module_code(code_id) {
        read_compiler_fragment_surface
    } else {
        read_scope_surface
    };
    let surface = read_surface(&quoted_root, &ctx)
        .map_err(|error| emit_internal_surface_error(world, format!("quoted surface read failed: {error}")))?;
    let quoted = QuotedCodeSource {
        quoted: quoted_root.clone(),
        surface: surface.clone(),
    };

    let mut outputs = Vec::new();
    source_publish::discover_modules(world, code_id, ModuleId::GLOBAL, &surface, &ctx, &mut outputs)?;

    let code_changed = world.finish_code_index(code_id, quoted);
    outputs.push((FactKey::CodeIndexed(code_id), code_changed));

    Ok(JobEffects {
        outputs,
        ..JobEffects::default()
    })
}

/// Builds the namespace for top-level code after parsing has happened.
///
/// If the code has not been indexed yet, this job waits on `CodeIndexed` and
/// asks for `IndexCode`. When the scope is complete, it publishes `CodeScoped`.
pub(super) fn scope_code(world: &mut World<'_>, code_id: CodeId) -> Result<JobEffects, FatalError> {
    let Some(source) = world.code_source(code_id) else {
        return Ok(JobEffects::wait_on(
            FactKey::CodeIndexed(code_id),
            [Job::IndexCode(code_id)],
        ));
    };
    let mut reads = Vec::new();
    let base_namespace = if world.is_runtime_prelude(code_id) {
        Namespace::default()
    } else {
        let prelude = world.runtime_prelude();
        let prelude_fact = FactKey::CodeScoped(prelude);
        if !world.has_fact(&prelude_fact) {
            return Ok(JobEffects::wait_on(prelude_fact, [Job::ScopeCode(prelude)]));
        }
        reads.push(prelude_fact);
        world.prelude_head()
    };
    match source_publish::publish_scope(
        world,
        code_id,
        ScopeSnapshot::module(ModuleId::GLOBAL, base_namespace),
        &source.surface,
    )? {
        ScopePublication::Complete {
            namespace,
            reads: scope_reads,
            mut outputs,
            ..
        } => {
            if world.is_runtime_prelude(code_id) {
                world.set_prelude_head(namespace);
            }
            reads.extend(scope_reads);
            let scoped_changed = world.finish_code_scope(code_id, namespace);
            outputs.push((FactKey::CodeScoped(code_id), scoped_changed));
            Ok(JobEffects {
                reads,
                outputs,
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
pub(super) fn define_module(world: &mut World<'_>, module_id: ModuleId) -> Result<JobEffects, FatalError> {
    if let Some((source, scope)) = world.module_scope(module_id) {
        let result = match &source.kind {
            ModuleSourceKind::Body(surface) => source_publish::publish_scope(world, source.code, scope, surface)?,
            ModuleSourceKind::Protocol(surface) => {
                source_publish::publish_protocol_surface(world, source.code, module_id, scope.namespace(), surface)?
            }
        };
        return match result {
            ScopePublication::Complete {
                namespace,
                revision_floor: _revision_floor,
                reads,
                mut outputs,
                interface,
            } => {
                let changed = world.define_module(module_id, namespace, interface);
                outputs.push((FactKey::ModuleDefined(module_id), changed));
                outputs.push((FactKey::ModuleInterface(module_id), changed));
                Ok(JobEffects {
                    reads,
                    outputs,
                    ..JobEffects::default()
                })
            }
            ScopePublication::Blocked(effects) => Ok(effects),
        };
    }

    if let Some((code_id, parent_module)) = world.module_indexed_parent(module_id) {
        if parent_module.is_global() {
            return Ok(JobEffects::wait_on(
                FactKey::CodeScoped(code_id),
                [Job::ScopeCode(code_id)],
            ));
        }
        return Ok(JobEffects::wait_on(
            FactKey::ModuleDefined(parent_module),
            [Job::DefineModule(parent_module)],
        ));
    }

    if let Some(parent_module) = world.module_named_parent(module_id) {
        return Ok(JobEffects::wait_on(
            FactKey::ModuleDefined(parent_module),
            [Job::DefineModule(parent_module)],
        ));
    }

    if let Some(code_id) = world.ensure_runtime_module(module_id) {
        return Ok(JobEffects::wait_on(
            FactKey::CodeIndexed(code_id),
            [Job::IndexCode(code_id)],
        ));
    }

    Ok(JobEffects::wait_on(FactKey::ModuleIndexed(module_id), []))
}

pub(super) fn define_module_interface(world: &mut World<'_>, module_id: ModuleId) -> Result<JobEffects, FatalError> {
    if world.module_scope(module_id).is_some() {
        return Ok(JobEffects::wait_on(
            FactKey::ModuleInterface(module_id),
            [Job::DefineModule(module_id)],
        ));
    }

    let Some(interface) = world.module_interface_if_present(module_id) else {
        return Ok(JobEffects::wait_on(FactKey::ModuleIndexed(module_id), []));
    };
    let changed = world.define_module_interface(module_id, interface);
    Ok(JobEffects {
        outputs: vec![(FactKey::ModuleInterface(module_id), changed)],
        ..JobEffects::default()
    })
}

pub(super) fn define_function(
    world: &mut World<'_>,
    function_id: super::super::FunctionId,
) -> Result<JobEffects, FatalError> {
    let Some(source) = world.expanded_function_source(function_id) else {
        return Ok(JobEffects::wait_on(
            FactKey::ExpandedFunctionSource(function_id),
            world.ensure_expanded_function_source(function_id),
        ));
    };

    let surface = crate::compiler2::quoted_function::derive_function_surface(
        &source.source,
        source.code,
        world.code_name(source.code),
        world.code_text(source.code),
        world.tel(),
    )
    .map_err(|error| emit_internal_surface_error(world, format!("quoted function decode failed: {error}")))?;
    for diagnostic in crate::compiler2::source_diagnostics::function_warnings(&surface) {
        world.emit_warning_once(diagnostic);
    }
    source_publish::record_function_type_refs(world, function_id, &surface)?;
    let (_, changed) = world.define_function(
        world.function_module(function_id),
        source.owner_module,
        world.function_ref(function_id).name.clone(),
        source.code,
        source.namespace,
        source.required_remote_macros.clone(),
        source.source,
        surface,
    );
    Ok(JobEffects {
        reads: vec![FactKey::ExpandedFunctionSource(function_id)],
        outputs: vec![(FactKey::FunctionDefined(function_id), changed)],
        ..JobEffects::default()
    })
}

pub(super) fn expand_function_source(
    world: &mut World<'_>,
    function_id: super::super::FunctionId,
) -> Result<JobEffects, FatalError> {
    let Some(source) = world.function_source(function_id) else {
        return Ok(JobEffects::wait_on(
            FactKey::FunctionSource(function_id),
            world.ensure_function_source(function_id),
        ));
    };
    match FunctionSourceExpander::new(world, function_id, &source).expand(&source)? {
        FunctionSourceExpansion::Complete { source, reads } => {
            let changed = world.note_expanded_function_source(function_id, source);
            let mut reads = reads;
            reads.push(FactKey::FunctionSource(function_id));
            Ok(JobEffects {
                reads,
                outputs: vec![(FactKey::ExpandedFunctionSource(function_id), changed)],
                ..JobEffects::default()
            })
        }
        FunctionSourceExpansion::Blocked(effects) => Ok(effects),
    }
}

enum FunctionSourceExpansion {
    Complete {
        source: FunctionSource,
        reads: Vec<FactKey>,
    },
    Blocked(JobEffects),
}

struct FunctionSourceExpander<'world, 'tel> {
    world: &'world mut World<'tel>,
    function: FunctionId,
    current_module: ModuleId,
    namespace: Namespace,
    required_remote_macros: HashSet<FunctionId>,
    reads: Vec<FactKey>,
}

impl<'world, 'tel> QuotedExpansionCtx<'tel> for FunctionSourceExpander<'world, 'tel> {
    fn world(&mut self) -> &mut World<'tel> {
        self.world
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

impl<'world, 'tel> FunctionSourceExpander<'world, 'tel> {
    fn new(world: &'world mut World<'tel>, function: FunctionId, source: &FunctionSource) -> Self {
        let current_module = world.function_module(function);
        Self {
            world,
            function,
            current_module,
            namespace: source.namespace,
            required_remote_macros: source.required_remote_macros.iter().copied().collect(),
            reads: Vec::new(),
        }
    }

    fn expand(mut self, source: &FunctionSource) -> Result<FunctionSourceExpansion, FatalError> {
        let scope = ScopeSnapshot::function(self.current_module, self.namespace, self.function);
        let expanded = match self.expand_function_root(source.source.clone(), scope, 0)? {
            ExpandedRoot::Complete(expanded) => expanded,
            ExpandedRoot::Blocked(effects) => {
                return Ok(FunctionSourceExpansion::Blocked(self.blocked_effects(effects)));
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
            .map_err(|error| emit_internal_surface_error(self.world, format!("function source read failed: {error}")))?
            .is_some()
        {
            return match self.expand_function_clause(&source, &cursor, scope, depth)? {
                ExpandedValue::Complete(value) => Ok(ExpandedRoot::Complete(source.subroot(value))),
                ExpandedValue::Blocked(effects) => Ok(ExpandedRoot::Blocked(effects)),
            };
        }

        let items = cursor.list_items().map_err(|error| {
            emit_internal_surface_error(self.world, format!("grouped function source read failed: {error}"))
        })?;
        let mut changed = false;
        let mut expanded = Vec::with_capacity(items.len());
        for item in items {
            let Some(node) = item.ast_node().map_err(|error| {
                emit_internal_surface_error(self.world, format!("grouped function item read failed: {error}"))
            })?
            else {
                return Err(emit_internal_surface_error(
                    self.world,
                    "grouped function source expected quoted AST items".to_string(),
                ));
            };
            let head = node.head.atom_name().map_err(|error| {
                emit_internal_surface_error(self.world, format!("grouped function item head read failed: {error}"))
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
            emit_internal_surface_error(self.world, format!("grouped function source rebuild failed: {error}"))
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
            emit_internal_surface_error(self.world, format!("function clause read failed: {error}"))
        })?
        else {
            return Err(emit_internal_surface_error(
                self.world,
                "function source expected a quoted AST node".to_string(),
            ));
        };
        let head = node.head.atom_name().map_err(|error| {
            emit_internal_surface_error(self.world, format!("function clause head read failed: {error}"))
        })?;
        if head == "extern" {
            return Ok(ExpandedValue::Complete(cursor.root()));
        }
        if !matches!(head.as_str(), "fn" | "fnp" | "defmacro") {
            return Err(emit_internal_surface_error(
                self.world,
                format!("function source expected fn/fnp/defmacro/extern, got `{head}`"),
            ));
        }

        let args = node.tail.list_items().map_err(|error| {
            emit_internal_surface_error(self.world, format!("function clause args read failed: {error}"))
        })?;
        let Some(kwargs) = args.get(1) else {
            return Ok(ExpandedValue::Complete(cursor.root()));
        };
        let kw_items = kwargs.list_items().map_err(|error| {
            emit_internal_surface_error(self.world, format!("function clause keyword args read failed: {error}"))
        })?;

        let mut changed = false;
        let mut expanded_kw = Vec::with_capacity(kw_items.len());
        for kw in kw_items {
            let tuple = kw.tuple_items().map_err(|error| {
                emit_internal_surface_error(self.world, format!("function clause keyword read failed: {error}"))
            })?;
            if tuple.len() != 2 {
                return Err(emit_internal_surface_error(
                    self.world,
                    "function clause expected keyword tuples".to_string(),
                ));
            }
            if tuple[0].atom_name().map_err(|error| {
                emit_internal_surface_error(self.world, format!("function clause keyword name read failed: {error}"))
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
                                self.world,
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
                self.world,
                format!("function clause keyword list rebuild failed: {error}"),
            )
        })?;
        let mut expanded_args = args.iter().map(QuotedSourceCursor::root).collect::<Vec<_>>();
        expanded_args[1] = kw_root;
        let tail = owner.builder().list(&expanded_args).map_err(|error| {
            emit_internal_surface_error(self.world, format!("function clause arg list rebuild failed: {error}"))
        })?;
        let rebuilt = owner
            .builder()
            .tuple(&[node.head.root(), node.meta.root(), tail])
            .map_err(|error| {
                emit_internal_surface_error(self.world, format!("function clause rebuild failed: {error}"))
            })?;
        Ok(ExpandedValue::Complete(rebuilt))
    }

    fn blocked_effects(&self, mut effects: JobEffects) -> JobEffects {
        effects.reads.extend(self.reads.clone());
        effects
    }
}
