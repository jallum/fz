use std::collections::HashSet;
use std::rc::Rc;

use crate::ast::{FnDef, Item};
use crate::compiler::source::Id as SourceId;
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::parser::Parser;
use crate::parser::lexer::Lexer;

use super::super::code::CodeId;
use super::super::drive::{FactKey, Job, JobEffects};
use super::super::identity::{ModuleExport, ModuleId};
use super::super::namespace::{Namespace, NamespaceSymbol};
use super::super::scheduler::FatalError;
use super::super::world::World;

type Output = (FactKey, u64);
type Outputs = Vec<Output>;

enum ScopeResult {
    Complete {
        namespace: Namespace,
        reads: Vec<FactKey>,
        outputs: Outputs,
        exports: Vec<ModuleExport>,
    },
    Blocked(JobEffects),
}

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
pub(super) fn scope_code(world: &mut World<'_>, code_id: CodeId) -> Result<JobEffects, FatalError> {
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
pub(super) fn define_module(world: &mut World<'_>, module_id: ModuleId) -> Result<JobEffects, FatalError> {
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
                module.attrs.clone(),
                module.items.clone(),
            );
            outputs.push((FactKey::ModuleIndexed(module_id), revision));
            discover_modules(world, code_id, module_id, &module.items, outputs);
        }
    }
}
