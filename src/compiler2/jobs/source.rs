use std::collections::HashSet;

use crate::ast::{Attribute, SpecDecl, TypeExprBody};
use crate::compiler::source::Span;
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::function_surface::FunctionSurface;
use crate::modules::identity::ModuleName;

use super::super::code::CodeId;
use super::super::drive::{FactKey, Job, JobEffects};
use super::super::identity::{ModuleExport, ModuleId, ModuleSourceKind, NotedTypeDecl, TypeName};
use super::super::namespace::{Namespace, NamespaceSymbol};
use super::super::protocol::ProtocolCallbackImpl;
use super::super::quoted_surface::{
    FunctionForm, ProtocolImplForm, ScopeForm, ScopeSurface, SurfaceSourceContext, read_module_body_surface,
    read_protocol_body_surface, read_protocol_impl_body_surface, read_scope_surface,
};
use super::super::scheduler::FatalError;
use super::super::scope::ScopeSnapshot;
use super::super::type_expr::{NominalKind, TypeDefBody, TypeExpr, parse_type_def_body, parse_type_expr};
use super::super::world::World;
use super::super::{FunctionSource, QuotedCodeSource, parse_quoted_program};

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
    let quoted_root = parse_quoted_program(source_name.clone(), &source_text, world.tel())
        .map_err(|error| emit_job_diagnostic(world, error.to_diagnostic()))?;
    let ctx = SurfaceSourceContext::new(code_id, &source_text, world.tel());
    let surface = read_scope_surface(&quoted_root, &ctx)
        .map_err(|error| emit_internal_surface_error(world, format!("quoted surface read failed: {error}")))?;
    let quoted = QuotedCodeSource {
        quoted: quoted_root.clone(),
        surface: surface.clone(),
    };

    let mut outputs = Vec::new();
    discover_modules(world, code_id, ModuleId::GLOBAL, &surface, &ctx, &mut outputs)?;

    let code_revision = world.finish_code_index(code_id, quoted);
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
        if world.fact_revision(prelude_fact.clone()).is_none() {
            return Ok(JobEffects::wait_on(prelude_fact, [Job::ScopeCode(prelude)]));
        }
        reads.push(prelude_fact);
        world.prelude_head()
    };
    match define_scope(
        world,
        code_id,
        ScopeSnapshot::module(ModuleId::GLOBAL, base_namespace),
        &source.surface,
    )? {
        ScopeResult::Complete {
            namespace,
            reads: scope_reads,
            mut outputs,
            ..
        } => {
            if world.is_runtime_prelude(code_id) {
                world.set_prelude_head(namespace);
            }
            reads.extend(scope_reads);
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
    if let Some((source, scope)) = world.module_scope(module_id) {
        let result = match &source.kind {
            ModuleSourceKind::Body(surface) => define_scope(world, source.code, scope, surface)?,
            ModuleSourceKind::Protocol(surface) => {
                define_protocol_surface(world, module_id, scope.namespace(), surface)
            }
        };
        return match result {
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

    if let Some(code_id) = world.ensure_runtime_module(module_id) {
        return Ok(JobEffects::wait_on(
            FactKey::CodeIndexed(code_id),
            [Job::IndexCode(code_id)],
        ));
    }

    Ok(JobEffects::wait_on(FactKey::ModuleIndexed(module_id), []))
}

/// Walks one scope in source order and returns the namespace it produces.
///
/// First it reserves `@type` declarations from the surface attributes — bound
/// deepest so value names shadow a same-named type, and so sibling/forward type
/// references resolve without a fixpoint. The first item walk then reserves
/// local functions and child modules so bodies can reference names declared
/// later in the same scope, after which each `@type` is noted against the
/// fully-reserved scope. The second walk applies order-dependent items:
/// aliases, imports, function definitions, and child module scope points.
/// Imports may block until the provider module is defined.
fn define_scope(
    world: &mut World<'_>,
    code_id: CodeId,
    current_scope: ScopeSnapshot,
    surface: &ScopeSurface,
) -> Result<ScopeResult, FatalError> {
    let current_module = current_scope.module_id();
    let mut scope = current_scope.namespace();

    let mut pending_types = Vec::new();
    for attr in &surface.attrs {
        let Attribute::TypeAlias(decl) = attr else {
            continue;
        };
        let body = parse_type_def_body(&decl.body_tokens.0).map_err(|error| {
            emit_job_diagnostic(
                world,
                Diagnostic::error(
                    codes::RESOLVE_TYPE_ALIAS,
                    format!("compiler2 could not parse `@type {}`: {}", decl.name, error.msg),
                    error.span,
                ),
            )
        })?;
        let type_name = TypeName {
            module: current_module,
            name: decl.name.clone(),
            arity: decl.params.len(),
        };
        scope = world.bind_namespace(scope, decl.name.clone(), NamespaceSymbol::Type(type_name.clone()));
        pending_types.push((type_name, decl.params.clone(), body, decl.span));
    }

    let local_protocols = surface
        .forms
        .iter()
        .filter_map(|form| match form {
            ScopeForm::Protocol(protocol) if protocol.name.segments().len() == 1 => {
                Some(protocol.name.last_segment().to_string())
            }
            _ => None,
        })
        .collect::<HashSet<_>>();
    for form in &surface.forms {
        match form {
            ScopeForm::Function(function) => {
                let function_id = world.reference_function(current_module, function.name.clone(), function.arity);
                if function.is_macro {
                    scope = world.bind_namespace(scope, function.name.clone(), NamespaceSymbol::Macro(function_id));
                } else {
                    scope = world.bind_namespace(scope, function.name.clone(), NamespaceSymbol::Function(function_id));
                }
            }
            ScopeForm::Module(module) => {
                let module_id = world.reference_child_module(current_module, &module.name);
                scope = world.bind_namespace(scope, module.name.clone(), NamespaceSymbol::Module(module_id));
            }
            ScopeForm::Protocol(protocol) => {
                let protocol_id = reference_declared_protocol_module(world, current_module, &protocol.name);
                scope = world.bind_namespace(
                    scope,
                    protocol.name.last_segment().to_string(),
                    NamespaceSymbol::Module(protocol_id),
                );
            }
            ScopeForm::Alias(_)
            | ScopeForm::Import(_)
            | ScopeForm::Require(_)
            | ScopeForm::Struct(_)
            | ScopeForm::ProtocolImpl(_) => {}
            ScopeForm::MacroCall(macro_call) => {
                return Err(emit_job_diagnostic(
                    world,
                    Diagnostic::error(
                        crate::diag::codes::INTERNAL_POST_RESOLUTION_LEFTOVER,
                        "compiler2 indexing expected expanded AST without item macro calls",
                        macro_call.span,
                    ),
                ));
            }
        }
    }

    // The scope now carries every sibling type, function, and child module, so
    // note each @type against it: that captured namespace is the resolution
    // context DeriveTypeDef reads, replacing the per-module type-env fixpoint.
    for (type_name, params, body, span) in pending_types {
        let mut refs = Vec::new();
        collect_type_refs(world, scope, &body.inner, &mut refs);
        world.record_type_def_refs(type_name.clone(), refs);
        world.note_type_decl(
            type_name,
            NotedTypeDecl {
                params,
                body,
                namespace: scope,
                span,
            },
        );
    }

    let mut reads = Vec::new();
    let mut function_plans = Vec::new();
    let mut protocol_outputs = Vec::new();
    for form in &surface.forms {
        match form {
            ScopeForm::Alias(alias) => {
                let module_id = world.reference_module(alias.path.join("."));
                scope = world.bind_namespace(scope, alias.as_name.clone(), NamespaceSymbol::Module(module_id));
            }
            ScopeForm::Import(import) => {
                let imported_module = world.reference_module(import.path.join("."));
                if let Some(only) = import.only.as_deref() {
                    for (name, arity) in only {
                        let function = world.reference_function(imported_module, name.clone(), *arity);
                        scope = world.bind_namespace(scope, name.clone(), NamespaceSymbol::Function(function));
                    }
                    continue;
                }

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
                if let Some(except) = import.except.as_deref() {
                    let mut deny = HashSet::new();
                    for (name, arity) in except {
                        if find_export(&exports, name, *arity).is_none() {
                            return Err(emit_job_diagnostic(
                                world,
                                Diagnostic::error(
                                    codes::RESOLVE_UNKNOWN_IMPORT,
                                    format!(
                                        "module `{}` does not export `{}/{}`",
                                        import.path.join("."),
                                        name,
                                        arity
                                    ),
                                    import.span,
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
            ScopeForm::Function(function) => {
                function_plans.push((current_scope.with_namespace(scope), function.clone()));
            }
            ScopeForm::Module(module) => {
                let module_id = world.reference_child_module(current_module, &module.name);
                world.scope_module(module_id, scope);
            }
            ScopeForm::Protocol(protocol) => {
                let protocol_id = reference_declared_protocol_module(world, current_module, &protocol.name);
                world.scope_module(protocol_id, scope);
            }
            ScopeForm::ProtocolImpl(protocol_impl) => {
                let mut outputs =
                    define_protocol_impl(world, code_id, current_module, scope, &local_protocols, protocol_impl)?;
                protocol_outputs.append(&mut outputs);
            }
            ScopeForm::Require(_) | ScopeForm::Struct(_) | ScopeForm::MacroCall(_) => {}
        }
    }

    let mut outputs = Vec::new();
    outputs.append(&mut protocol_outputs);
    let mut exports = Vec::new();
    for (function_scope, function) in function_plans {
        let (output, export) = index_function(world, code_id, function_scope, &function)?;
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
    scope: ScopeSnapshot,
    function: &FunctionForm,
) -> Result<(Output, Option<ModuleExport>), FatalError> {
    let current_module = scope.module_id();
    let namespace = scope.namespace();
    let function_id = world.reference_function(current_module, function.name.clone(), function.arity);
    let revision = world.note_function_source(
        function_id,
        FunctionSource {
            code: code_id,
            owner_module: current_module,
            namespace,
            capture_params: Vec::new(),
            variadic: function.variadic,
            source: function.source.clone(),
        },
    );

    let export = (!function.is_private).then(|| ModuleExport {
        name: function.name.clone(),
        arity: function.arity,
        variadic: function.variadic,
        symbol: if function.is_macro {
            NamespaceSymbol::Macro(function_id)
        } else {
            NamespaceSymbol::Function(function_id)
        },
    });
    Ok(((FactKey::FunctionSource(function_id), revision), export))
}

/// Walks a parsed type expression, recording each name that resolves to a type
/// identity against `scope`. Builtins, free type variables, and unresolvable
/// bare names are not references — resolution decides them, not this walk.
fn collect_type_refs(world: &mut World<'_>, scope: Namespace, expr: &TypeExpr, out: &mut Vec<TypeName>) {
    match expr {
        TypeExpr::Name { path, args } => {
            if let Some(type_name) = world.reference_type(scope, path, args.len()) {
                out.push(type_name);
            }
            for arg in args {
                collect_type_refs(world, scope, arg, out);
            }
        }
        TypeExpr::List(inner) => collect_type_refs(world, scope, inner, out),
        TypeExpr::Tuple(elems) | TypeExpr::Union(elems) => {
            for elem in elems {
                collect_type_refs(world, scope, elem, out);
            }
        }
        TypeExpr::Arrow { params, result } => {
            for param in params {
                collect_type_refs(world, scope, param, out);
            }
            collect_type_refs(world, scope, result, out);
        }
        TypeExpr::StructRecord { fields, .. } => {
            for (_, ty) in fields {
                collect_type_refs(world, scope, ty, out);
            }
        }
        TypeExpr::EmptyList
        | TypeExpr::AtomLit(_)
        | TypeExpr::IntLit(_)
        | TypeExpr::FloatLit(_)
        | TypeExpr::Wildcard
        | TypeExpr::Nil
        | TypeExpr::Bool => {}
    }
}

/// Walks every type-position of a spec — each parameter, the result, and each
/// constraint bound — recording the type names it references.
fn collect_spec_refs(
    world: &mut World<'_>,
    scope: Namespace,
    spec: &SpecDecl,
    out: &mut Vec<TypeName>,
) -> Result<(), FatalError> {
    for body in spec
        .param_body_tokens
        .iter()
        .chain(std::iter::once(&spec.result_body_tokens))
        .chain(spec.constraints.iter().map(|(_, bound)| bound))
    {
        collect_body_refs(world, scope, body, out)?;
    }
    Ok(())
}

/// Parses one type-expression body and records the type names it references.
fn collect_body_refs(
    world: &mut World<'_>,
    scope: Namespace,
    body: &TypeExprBody,
    out: &mut Vec<TypeName>,
) -> Result<(), FatalError> {
    if body.0.is_empty() {
        return Ok(());
    }
    let expr = parse_type_expr(&body.0).map_err(|error| {
        emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::RESOLVE_TYPE_ALIAS,
                format!("compiler2 could not parse a type expression: {}", error.msg),
                error.span,
            ),
        )
    })?;
    collect_type_refs(world, scope, &expr, out);
    Ok(())
}

fn record_function_type_refs(
    world: &mut World<'_>,
    function: super::super::FunctionId,
    surface: &FunctionSurface,
) -> Result<(), FatalError> {
    let namespace = world
        .function_source(function)
        .expect("function type refs should only be recorded after function source is noted")
        .namespace;
    let mut refs = Vec::new();
    for attr in &surface.attrs {
        if let Attribute::Spec(spec) = attr {
            collect_spec_refs(world, namespace, spec, &mut refs)?;
        }
    }
    if let Some(extern_spec) = surface.extern_contract_decl() {
        collect_spec_refs(world, namespace, &extern_spec, &mut refs)?;
    }
    for clause in &surface.clauses {
        for annotation in clause.param_annotations.iter().flatten() {
            collect_body_refs(world, namespace, annotation, &mut refs)?;
        }
    }
    world.record_function_type_refs(function, refs);
    Ok(())
}

pub(super) fn define_function(
    world: &mut World<'_>,
    function_id: super::super::FunctionId,
) -> Result<JobEffects, FatalError> {
    let Some(source) = world.function_source(function_id) else {
        return Ok(JobEffects::wait_on(
            FactKey::FunctionSource(function_id),
            world.ensure_function_source(function_id),
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
    record_function_type_refs(world, function_id, &surface)?;
    let (_, revision) = world.define_function(
        world.function_module(function_id),
        source.owner_module,
        world.function_ref(function_id).name.clone(),
        source.code,
        source.namespace,
        source.source,
        surface,
    );
    Ok(JobEffects {
        reads: vec![FactKey::FunctionSource(function_id)],
        outputs: vec![(FactKey::FunctionDefined(function_id), revision)],
        ..JobEffects::default()
    })
}

fn define_protocol_surface(
    world: &mut World<'_>,
    module_id: ModuleId,
    namespace: Namespace,
    surface: &ScopeSurface,
) -> ScopeResult {
    let mut scope = namespace;
    let protocol_t = TypeName {
        module: module_id,
        name: "t".to_string(),
        arity: 0,
    };
    scope = world.bind_namespace(scope, "t".to_string(), NamespaceSymbol::Type(protocol_t.clone()));
    note_protocol_domain_type(world, protocol_t, scope, Vec::new());
    note_protocol_domain_type(
        world,
        TypeName {
            module: module_id,
            name: "t".to_string(),
            arity: 1,
        },
        scope,
        vec!["a".to_string()],
    );

    let mut outputs = world.refresh_protocol_domain_facts(module_id);
    outputs.push(world.refresh_protocol_dispatch_fact(module_id));
    let mut exports = Vec::new();
    for form in &surface.forms {
        let ScopeForm::Function(callback) = form else {
            continue;
        };
        let function = world.reference_function(module_id, callback.name.clone(), callback.arity);
        world.define_protocol_callback(function, module_id);
        let symbol = NamespaceSymbol::Function(function);
        scope = world.bind_namespace(scope, callback.name.clone(), symbol.clone());
        exports.push(ModuleExport {
            name: callback.name.clone(),
            arity: callback.arity,
            variadic: false,
            symbol,
        });
    }
    ScopeResult::Complete {
        namespace: scope,
        reads: Vec::new(),
        outputs,
        exports,
    }
}

fn note_protocol_domain_type(world: &mut World<'_>, name: TypeName, namespace: Namespace, params: Vec<String>) {
    world.note_type_decl(
        name.clone(),
        NotedTypeDecl {
            params,
            body: TypeDefBody {
                kind: NominalKind::Opaque,
                inner: TypeExpr::Wildcard,
            },
            namespace,
            span: Span::DUMMY,
        },
    );
    world.record_type_def_refs(name, Vec::new());
}

fn define_protocol_impl(
    world: &mut World<'_>,
    code_id: CodeId,
    current_module: ModuleId,
    namespace: Namespace,
    local_protocols: &HashSet<String>,
    protocol_impl: &ProtocolImplForm,
) -> Result<Outputs, FatalError> {
    let protocol = reference_impl_protocol_module(world, current_module, &protocol_impl.protocol, local_protocols);
    let target = reference_impl_target_module(world, current_module, &protocol_impl.target);
    let impl_module = reference_protocol_impl_module(world, protocol, target);
    let code_text = world.code_text(code_id).to_owned();
    let ctx = SurfaceSourceContext::new(code_id, &code_text, world.tel());
    let body_surface = read_protocol_impl_body_surface(protocol_impl, &ctx).map_err(|error| {
        emit_internal_surface_error(world, format!("quoted protocol impl body read failed: {error}"))
    })?;

    let mut impl_scope = namespace;
    let mut functions = Vec::new();
    for form in &body_surface.forms {
        let ScopeForm::Function(function) = form else {
            return Err(emit_job_diagnostic(
                world,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    "compiler2 protocol implementations only support callback functions",
                    protocol_impl.span,
                ),
            ));
        };
        if function.is_macro {
            return Err(emit_job_diagnostic(
                world,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    "compiler2 protocol implementations cannot define macros",
                    function.span,
                ),
            ));
        }
        let function_id = world.reference_function(impl_module, function.name.clone(), function.arity);
        impl_scope = world.bind_namespace(
            impl_scope,
            function.name.clone(),
            NamespaceSymbol::Function(function_id),
        );
        functions.push(function.clone());
    }

    let mut outputs = Vec::new();
    let mut callbacks = std::collections::HashMap::new();
    for function in functions {
        let function_id = world.reference_function(impl_module, function.name.clone(), function.arity);
        let revision = world.note_function_source(
            function_id,
            FunctionSource {
                code: code_id,
                owner_module: current_module,
                namespace: impl_scope,
                capture_params: Vec::new(),
                variadic: function.variadic,
                source: function.source.clone(),
            },
        );
        outputs.push((FactKey::FunctionSource(function_id), revision));
        callbacks.insert(
            (function.name.clone(), function.arity),
            ProtocolCallbackImpl {
                function: function_id,
                owner_module: current_module,
            },
        );
    }
    world.define_protocol_impl(protocol, target, callbacks);
    outputs.extend(world.refresh_protocol_domain_facts(protocol));
    outputs.push(world.refresh_protocol_dispatch_fact(protocol));
    Ok(outputs)
}

fn emit_job_diagnostic(world: &World<'_>, diagnostic: Diagnostic) -> FatalError {
    emit_through(world.tel(), None, std::slice::from_ref(&diagnostic));
    FatalError
}

fn emit_internal_surface_error(world: &World<'_>, message: String) -> FatalError {
    emit_job_diagnostic(
        world,
        Diagnostic::error(codes::INTERNAL_POST_RESOLUTION_LEFTOVER, message, Span::DUMMY),
    )
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
    surface: &ScopeSurface,
    ctx: &SurfaceSourceContext<'_>,
    outputs: &mut Outputs,
) -> Result<(), FatalError> {
    for form in &surface.forms {
        match form {
            ScopeForm::Module(module) => {
                let module_id = world.reference_child_module(parent_module, &module.name);
                let nested = read_module_body_surface(module, ctx).map_err(|error| {
                    emit_internal_surface_error(world, format!("nested module body read failed: {error}"))
                })?;
                let revision = world.index_module_body(
                    module_id,
                    code_id,
                    parent_module,
                    module.name.clone(),
                    module.source.clone(),
                    nested.clone(),
                );
                outputs.push((FactKey::ModuleIndexed(module_id), revision));
                discover_modules(world, code_id, module_id, &nested, ctx, outputs)?;
            }
            ScopeForm::Protocol(protocol) => {
                let module_id = reference_declared_protocol_module(world, parent_module, &protocol.name);
                let protocol_surface = read_protocol_body_surface(protocol, ctx).map_err(|error| {
                    emit_internal_surface_error(world, format!("quoted protocol body read failed: {error}"))
                })?;
                let revision = world.index_protocol_module(
                    module_id,
                    code_id,
                    parent_module,
                    protocol.name.last_segment().to_string(),
                    protocol.source.clone(),
                    protocol_surface,
                );
                outputs.push((FactKey::ModuleIndexed(module_id), revision));
            }
            _ => {}
        }
    }
    Ok(())
}

fn reference_declared_protocol_module(world: &mut World<'_>, current_module: ModuleId, name: &ModuleName) -> ModuleId {
    world.reference_module(qualified_child_module_name(world, current_module, name))
}

fn reference_impl_protocol_module(
    world: &mut World<'_>,
    current_module: ModuleId,
    name: &ModuleName,
    local_protocols: &HashSet<String>,
) -> ModuleId {
    world.reference_module(qualified_impl_protocol_name(
        world,
        current_module,
        name,
        local_protocols,
    ))
}

fn reference_impl_target_module(world: &mut World<'_>, current_module: ModuleId, name: &ModuleName) -> ModuleId {
    world.reference_module(qualified_child_module_name(world, current_module, name))
}

fn reference_protocol_impl_module(world: &mut World<'_>, protocol: ModuleId, target: ModuleId) -> ModuleId {
    let protocol_name = world
        .module_name(protocol)
        .expect("protocol modules should have reverse names");
    let target_name = world
        .module_name(target)
        .expect("protocol impl targets should have reverse names");
    let target_local = last_segment(target_name);
    world.reference_module(format!("{protocol_name}.{target_local}"))
}

fn qualified_impl_protocol_name(
    world: &World<'_>,
    current_module: ModuleId,
    name: &ModuleName,
    local_protocols: &HashSet<String>,
) -> String {
    if name.segments().len() != 1 || current_module.is_global() {
        return name.dotted();
    }
    let local = name.last_segment();
    if !local_protocols.contains(local) && !same_as_current_module(world, current_module, local) {
        return name.dotted();
    }
    qualify_local_child_name(world, current_module, local)
}

fn qualified_child_module_name(world: &World<'_>, current_module: ModuleId, name: &ModuleName) -> String {
    if name.segments().len() != 1 || current_module.is_global() {
        return name.dotted();
    }
    qualify_local_child_name(world, current_module, name.last_segment())
}

fn qualify_local_child_name(world: &World<'_>, current_module: ModuleId, local: &str) -> String {
    let current_name = world
        .module_name(current_module)
        .expect("named scoped modules should have reverse lookups");
    if local == last_segment(current_name) {
        current_name.to_string()
    } else {
        format!("{current_name}.{local}")
    }
}

fn same_as_current_module(world: &World<'_>, current_module: ModuleId, local: &str) -> bool {
    let current_name = world
        .module_name(current_module)
        .expect("named scoped modules should have reverse lookups");
    local == last_segment(current_name)
}

fn last_segment(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
}
