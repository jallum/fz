//! Work loop, source-surface jobs, and the first semantic root seed.
//!
//! This work layer turns submitted code into compiler-owned facts. `IndexCode`
//! parses source and discovers module shells. `ScopeCode` builds the top-level
//! namespace. `DefineModule` builds a module surface on demand. `SeedRoot` and
//! `CheckSemanticClosure` start the root-scoped semantic island without
//! lowering or planning bodies yet. Jobs do not mutate the work graph
//! directly; they return `JobEffects`, and the world applies those effects
//! after the job span closes.

use std::rc::Rc;

use crate::ast::{FnDef, Item};
use crate::compiler::source::Id as SourceId;
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::parser::Parser;
use crate::parser::lexer::Lexer;
use crate::telemetry::{TelemetryExt, opaque};
use crate::{measurements, metadata};
use std::collections::HashSet;

use super::code::CodeId;
use super::identity::{ActivationKey, ExecutableKey, FunctionId, ModuleExport, ModuleId, RootId};
use super::namespace::{Namespace, NamespaceSymbol};
use super::scheduler::{DriveOutcome, FatalError, Scheduler};
use super::world::World;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Job {
    IndexCode(CodeId),
    ScopeCode(CodeId),
    DefineModule(ModuleId),
    SeedRoot(RootId),
    CheckSemanticClosure(RootId),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FactKey {
    CodeIndexed(CodeId),
    CodeScoped(CodeId),
    ModuleIndexed(ModuleId),
    ModuleDefined(ModuleId),
    FunctionDefined(FunctionId),
    RootEntry(RootId),
    Activation(ActivationKey),
    Executable(ExecutableKey),
    SemanticClosed(RootId),
}

pub type WorkGraph = Scheduler<Job, FactKey, super::deps::ExactPattern<FactKey>>;
type Output = (FactKey, u64);
type Outputs = Vec<Output>;
type FollowUp = Vec<Job>;

#[derive(Debug, Default)]
pub(crate) struct JobEffects {
    pub(crate) reads: Vec<FactKey>,
    pub(crate) waits: Vec<FactKey>,
    pub(crate) outputs: Outputs,
    pub(crate) follow_up: FollowUp,
}

impl JobEffects {
    fn wait_on(fact: FactKey, follow_up: impl IntoIterator<Item = Job>) -> Self {
        Self {
            waits: vec![fact],
            follow_up: follow_up.into_iter().collect(),
            ..Self::default()
        }
    }
}

enum ScopeResult {
    Complete {
        namespace: Namespace,
        reads: Vec<FactKey>,
        outputs: Outputs,
        exports: Vec<ModuleExport>,
    },
    Blocked(JobEffects),
}

impl World<'_> {
    /// Runs queued jobs until the work graph has no ready work.
    ///
    /// Each job gets one telemetry span. A successful job closes with its raw
    /// effects, then the world publishes those effects to the graph. A fatal
    /// job closes its span, closes the drive span as fatal, and stops the loop.
    pub fn drive(&mut self) -> DriveOutcome<Job, super::deps::ExactPattern<FactKey>> {
        let mut span = self.tel().span(
            &["fz", "compiler2", "drive"],
            metadata! {
                pending_jobs: self.work_graph.pending_jobs() as u64,
            },
        );
        let mut jobs_ran = 0_u64;
        while let Some(job) = self.work_graph.pop() {
            let job_kind = job.kind();
            let job_id = job.id();
            let mut job_span = self.tel().span(
                &["fz", "compiler2", "job"],
                metadata! {
                    kind: job_kind,
                    id: job_id,
                },
            );
            let result = match job {
                Job::IndexCode(code_id) => index_code(self, code_id),
                Job::ScopeCode(code_id) => scope_code(self, code_id),
                Job::DefineModule(module_id) => define_module(self, module_id),
                Job::SeedRoot(root_id) => seed_root(self, root_id),
                Job::CheckSemanticClosure(root_id) => check_semantic_closure(self, root_id),
            };
            match result {
                Ok(effects) => {
                    jobs_ran += 1;
                    job_span.stop_with(
                        &measurements! {},
                        &metadata! {
                            outcome: "ok",
                            effects: opaque(&effects),
                        },
                    );
                    self.complete_job(job, effects);
                }
                Err(_) => {
                    job_span.close_with(measurements! {}, metadata! { outcome: "fatal" });
                    span.close_with(measurements! { jobs_ran: jobs_ran }, metadata! { outcome: "fatal" });
                    return DriveOutcome::Fatal { job };
                }
            }
        }
        if !self.work_graph.has_unresolved() {
            span.close_with(measurements! { jobs_ran: jobs_ran }, metadata! { outcome: "resolved" });
            DriveOutcome::Resolved
        } else {
            let unresolved = self.work_graph.unresolved();
            span.stop_with(
                &measurements! { jobs_ran: jobs_ran },
                &metadata! {
                    outcome: "unresolved",
                    waits: opaque(&unresolved),
                },
            );
            DriveOutcome::Unresolved { waits: unresolved }
        }
    }
}

impl Job {
    fn kind(&self) -> &'static str {
        match self {
            Job::IndexCode(_) => "IndexCode",
            Job::ScopeCode(_) => "ScopeCode",
            Job::DefineModule(_) => "DefineModule",
            Job::SeedRoot(_) => "SeedRoot",
            Job::CheckSemanticClosure(_) => "CheckSemanticClosure",
        }
    }

    fn id(&self) -> u64 {
        match self {
            Job::IndexCode(id) | Job::ScopeCode(id) => id.as_u32() as u64,
            Job::DefineModule(id) => id.as_u32() as u64,
            Job::SeedRoot(id) | Job::CheckSemanticClosure(id) => id.as_u32() as u64,
        }
    }
}

/// Parses a code submission and records the parts other jobs can ask for later.
///
/// This job stores the parsed top-level AST on the code record and discovers
/// nested module records. It does not scope modules, define functions, lower
/// bodies, or pull in imports.
fn index_code(world: &mut World<'_>, code_id: CodeId) -> Result<JobEffects, FatalError> {
    let source_name = world
        .code_name(code_id)
        .map(str::to_owned)
        .unwrap_or_else(|| format!("<code:{}>", code_id.as_u32()));
    let source_text = world.code_text(code_id).to_owned();

    let source_id = SourceId(code_id.as_u32());
    let tokens = Lexer::with_code_id_and_source_name(&source_text, source_id, source_name)
        .tokenize(world.tel())
        .map_err(|error| emit_job_diagnostic(world, error.to_diagnostic()))?;
    let program = Parser::new(tokens)
        .parse_program(world.tel())
        .map_err(|error| emit_job_diagnostic(world, error.to_diagnostic()))?;
    let mut outputs = Vec::new();
    discover_modules(world, code_id, ModuleId::GLOBAL, &program.items, &mut outputs);

    let code_revision = world.finish_code_index(code_id, program.items.clone());
    outputs.push((FactKey::CodeIndexed(code_id), code_revision));

    Ok(JobEffects {
        outputs,
        ..JobEffects::default()
    })
}

/// Builds the namespace for top-level code after parsing has happened.
///
/// If the code has not been indexed yet, this job waits on `CodeIndexed` and
/// asks for `IndexCode`. When the scope is complete, it publishes `CodeScoped`.
fn scope_code(world: &mut World<'_>, code_id: CodeId) -> Result<JobEffects, FatalError> {
    let Some(items) = world.code_items(code_id).map(|items| items.to_vec()) else {
        return Ok(JobEffects::wait_on(
            FactKey::CodeIndexed(code_id),
            [Job::IndexCode(code_id)],
        ));
    };
    match define_scope(world, code_id, ModuleId::GLOBAL, world.prelude_head(), &items)? {
        ScopeResult::Complete { reads, mut outputs, .. } => {
            outputs.push((FactKey::CodeScoped(code_id), world.code_revision(code_id)));
            Ok(JobEffects {
                reads,
                outputs,
                ..JobEffects::default()
            })
        }
        ScopeResult::Blocked(effects) => Ok(effects),
    }
}

/// Builds one module surface when something demands that module.
///
/// A module can only be defined after its parent scope exists. If the parent is
/// not ready, this job waits on the parent fact and schedules the parent job.
/// When ready, it scopes the module body and publishes `ModuleDefined`.
fn define_module(world: &mut World<'_>, module_id: ModuleId) -> Result<JobEffects, FatalError> {
    if let Some((code_id, items, base_namespace)) = world.module_scope(module_id) {
        return match define_scope(world, code_id, module_id, base_namespace, &items)? {
            ScopeResult::Complete {
                namespace,
                reads,
                mut outputs,
                exports,
            } => {
                let revision = world.define_module(module_id, namespace, exports);
                outputs.push((FactKey::ModuleDefined(module_id), revision));
                Ok(JobEffects {
                    reads,
                    outputs,
                    ..JobEffects::default()
                })
            }
            ScopeResult::Blocked(effects) => Ok(effects),
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

    Ok(JobEffects::wait_on(FactKey::ModuleIndexed(module_id), []))
}

/// Seeds one semantic root once its entry definition exists.
///
/// A root entry is compiler-owned and can exist before the function does. The
/// seed publishes the root fact immediately, then waits until the entry
/// function is defined before it publishes the first activation and executable.
fn seed_root(world: &mut World<'_>, root_id: RootId) -> Result<JobEffects, FatalError> {
    let root = world.root_entry(root_id);
    let root_fact = FactKey::RootEntry(root_id);
    let root_revision = world.root_revision(root_id);
    let mut effects = JobEffects {
        reads: vec![root_fact.clone()],
        outputs: vec![(root_fact, root_revision)],
        ..JobEffects::default()
    };

    let function_fact = FactKey::FunctionDefined(root.function);
    let Some(function_revision) = world.function_defined_revision(root.function) else {
        effects.waits.push(function_fact);
        return Ok(effects);
    };

    effects.reads.push(function_fact);
    let revision = root_revision.max(function_revision);
    let activation = ActivationKey {
        root: root_id,
        function: root.function,
    };
    let executable = ExecutableKey {
        activation,
        need: root.need,
    };
    effects.outputs.push((FactKey::Activation(activation), revision));
    effects.outputs.push((FactKey::Executable(executable), revision));
    effects.follow_up.push(Job::CheckSemanticClosure(root_id));
    Ok(effects)
}

/// Publishes the first semantic-closure marker for a seeded root.
///
/// This ticket keeps closure intentionally small: once the entry activation and
/// executable exist, the root can publish `SemanticClosed`. Later semantic jobs
/// will make this job stricter without changing the work-graph contract.
fn check_semantic_closure(world: &mut World<'_>, root_id: RootId) -> Result<JobEffects, FatalError> {
    let root = world.root_entry(root_id);
    let activation = ActivationKey {
        root: root_id,
        function: root.function,
    };
    let executable = ExecutableKey {
        activation,
        need: root.need,
    };
    let mut reads = vec![FactKey::RootEntry(root_id)];
    let Some(activation_revision) = world.fact_revision(FactKey::Activation(activation)) else {
        return Ok(JobEffects::wait_on(FactKey::Activation(activation), []));
    };
    reads.push(FactKey::Activation(activation));
    let Some(executable_revision) = world.fact_revision(FactKey::Executable(executable)) else {
        return Ok(JobEffects::wait_on(FactKey::Executable(executable), []));
    };
    reads.push(FactKey::Executable(executable));
    let revision = world
        .root_revision(root_id)
        .max(activation_revision)
        .max(executable_revision);
    Ok(JobEffects {
        reads,
        outputs: vec![(FactKey::SemanticClosed(root_id), revision)],
        ..JobEffects::default()
    })
}

/// Walks one scope in source order and returns the namespace it produces.
///
/// The first walk reserves local functions and child modules so bodies can
/// reference names declared later in the same scope. The second walk applies
/// order-dependent items: aliases, imports, function definitions, and child
/// module scope points. Imports may block until the provider module is defined.
fn define_scope(
    world: &mut World<'_>,
    code_id: CodeId,
    current_module: ModuleId,
    namespace: Namespace,
    items: &[Rc<Item>],
) -> Result<ScopeResult, FatalError> {
    let mut scope = namespace;
    for item in items {
        match &**item {
            Item::Fn(def) => {
                let function_id = world.reference_function(current_module, def.name.clone(), def.arity());
                if def.is_macro {
                    scope = world.bind_namespace(scope, def.name.clone(), NamespaceSymbol::Macro(function_id));
                } else {
                    scope = world.bind_namespace(scope, def.name.clone(), NamespaceSymbol::Function(function_id));
                }
            }
            Item::Module(module) => {
                let module_id = world.reference_child_module(current_module, &module.name);
                scope = world.bind_namespace(scope, module.name.clone(), NamespaceSymbol::Module(module_id));
            }
            Item::Alias { .. } | Item::Import { .. } | Item::Struct(_) | Item::Protocol(_) | Item::ProtocolImpl(_) => {}
            Item::MacroCall { span, .. } => {
                return Err(emit_job_diagnostic(
                    world,
                    Diagnostic::error(
                        crate::diag::codes::INTERNAL_POST_RESOLUTION_LEFTOVER,
                        "compiler2 indexing expected expanded AST without item macro calls",
                        *span,
                    ),
                ));
            }
        }
    }

    let mut reads = Vec::new();
    let mut function_plans = Vec::new();
    for item in items {
        match &**item {
            Item::Alias { full_path, as_name, .. } => {
                let module_id = world.reference_module(full_path.dotted());
                scope = world.bind_namespace(scope, as_name.clone(), NamespaceSymbol::Module(module_id));
            }
            Item::Import {
                path,
                only,
                except,
                span,
            } => {
                let imported_module = world.reference_module(path.dotted());
                let surface_fact = FactKey::ModuleDefined(imported_module);
                if world.module_defined_revision(imported_module).is_none() {
                    let follow_up = if imported_module.is_global() {
                        Vec::new()
                    } else {
                        vec![Job::DefineModule(imported_module)]
                    };
                    return Ok(ScopeResult::Blocked(JobEffects::wait_on(surface_fact, follow_up)));
                }
                reads.push(surface_fact);

                let exports = world.module_exports(imported_module);
                if let Some(only) = only.as_deref() {
                    for (name, arity) in only {
                        let export = find_export(&exports, name, *arity).ok_or_else(|| {
                            emit_job_diagnostic(
                                world,
                                Diagnostic::error(
                                    codes::RESOLVE_UNKNOWN_IMPORT,
                                    format!("module `{}` does not export `{}/{}`", path, name, arity),
                                    *span,
                                ),
                            )
                        })?;
                        scope = bind_export(world, scope, export);
                    }
                } else if let Some(except) = except.as_deref() {
                    let mut deny = HashSet::new();
                    for (name, arity) in except {
                        if find_export(&exports, name, *arity).is_none() {
                            return Err(emit_job_diagnostic(
                                world,
                                Diagnostic::error(
                                    codes::RESOLVE_UNKNOWN_IMPORT,
                                    format!("module `{}` does not export `{}/{}`", path, name, arity),
                                    *span,
                                ),
                            ));
                        }
                        deny.insert((name.as_str(), *arity));
                    }
                    for export in exports
                        .iter()
                        .filter(|export| !deny.contains(&(export.name.as_str(), export.arity)))
                    {
                        scope = bind_export(world, scope, export);
                    }
                } else {
                    for export in &exports {
                        scope = bind_export(world, scope, export);
                    }
                }
            }
            Item::Fn(def) => {
                function_plans.push((scope, def.clone()));
            }
            Item::Module(module) => {
                let module_id = world.reference_child_module(current_module, &module.name);
                world.scope_module(module_id, scope);
            }
            Item::Struct(_) | Item::Protocol(_) | Item::ProtocolImpl(_) | Item::MacroCall { .. } => {}
        }
    }

    let mut outputs = Vec::new();
    let mut exports = Vec::new();
    for (function_namespace, def) in function_plans {
        let (output, export) = index_function(world, code_id, current_module, function_namespace, &def)?;
        outputs.push(output);
        if let Some(export) = export {
            exports.push(export);
        }
    }

    Ok(ScopeResult::Complete {
        namespace: scope,
        reads,
        outputs,
        exports,
    })
}

fn index_function(
    world: &mut World<'_>,
    code_id: CodeId,
    current_module: ModuleId,
    namespace: Namespace,
    def: &FnDef,
) -> Result<(Output, Option<ModuleExport>), FatalError> {
    let (function_id, revision) =
        world.define_function(current_module, def.name.clone(), code_id, namespace, def.clone());
    let export = (!def.is_private).then(|| ModuleExport {
        name: def.name.clone(),
        arity: def.arity(),
        symbol: if def.is_macro {
            NamespaceSymbol::Macro(function_id)
        } else {
            NamespaceSymbol::Function(function_id)
        },
    });
    Ok(((FactKey::FunctionDefined(function_id), revision), export))
}

fn emit_job_diagnostic(world: &World<'_>, diagnostic: Diagnostic) -> FatalError {
    emit_through(world.tel(), None, std::slice::from_ref(&diagnostic));
    FatalError
}

fn find_export<'a>(exports: &'a [ModuleExport], name: &str, arity: usize) -> Option<&'a ModuleExport> {
    exports
        .iter()
        .find(|export| export.name == name && export.arity == arity)
}

fn bind_export(world: &mut World<'_>, scope: Namespace, export: &ModuleExport) -> Namespace {
    world.bind_namespace(scope, export.name.clone(), export.symbol.clone())
}

fn discover_modules(
    world: &mut World<'_>,
    code_id: CodeId,
    parent_module: ModuleId,
    items: &[Rc<Item>],
    outputs: &mut Outputs,
) {
    for item in items {
        if let Item::Module(module) = &**item {
            let module_id = world.reference_child_module(parent_module, &module.name);
            let revision = world.index_module(
                module_id,
                code_id,
                parent_module,
                module.name.clone(),
                module.items.clone(),
            );
            outputs.push((FactKey::ModuleIndexed(module_id), revision));
            discover_modules(world, code_id, module_id, &module.items, outputs);
        }
    }
}
