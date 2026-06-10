//! Compiler-owned publication for quoted source forms.
//!
//! Source jobs schedule work. This module owns the source-form rules that turn
//! quoted surface readers into namespace mutations and compiler2 fact outputs.

use std::collections::{HashMap, HashSet};

use crate::ast::{Attribute, SpecDecl, TypeExprBody};
use crate::compiler::source::Span;
use crate::diag::driver::emit_through;
use crate::diag::{Diagnostic, codes};
use crate::function_surface::FunctionSurface;
use crate::modules::identity::ModuleName;

use super::code::CodeId;
use super::drive::{FactKey, Job, JobEffects};
use super::identity::{FunctionId, FunctionSource, ModuleExport, ModuleId, NotedTypeDecl, TypeName};
use super::namespace::{Namespace, NamespaceSymbol};
use super::protocol::ProtocolCallbackImpl;
use super::quoted_surface::{
    FunctionForm, ProtocolImplForm, ScopeForm, ScopeSurface, SurfaceSourceContext, read_module_body_surface,
    read_protocol_body_surface, read_protocol_impl_body_surface,
};
use super::scheduler::FatalError;
use super::scope::ScopeSnapshot;
use super::type_expr::{NominalKind, TypeDefBody, TypeExpr, parse_type_def_body, parse_type_expr};
use super::world::World;

type Output = (FactKey, u64);
type Outputs = Vec<Output>;

pub(crate) enum ScopePublication {
    Complete {
        namespace: Namespace,
        revision_floor: u64,
        reads: Vec<FactKey>,
        outputs: Outputs,
        exports: Vec<ModuleExport>,
    },
    Blocked(JobEffects),
}

struct PendingType {
    name: TypeName,
    params: Vec<String>,
    body: TypeDefBody,
    span: Span,
}

struct FunctionPlan {
    scope: ScopeSnapshot,
    function: FunctionForm,
}

struct ScopeSession<'world, 'tel> {
    world: &'world mut World<'tel>,
    code_id: CodeId,
    current_scope: ScopeSnapshot,
    current_module: ModuleId,
    namespace: Namespace,
    local_protocols: HashSet<String>,
    pending_types: Vec<PendingType>,
    function_plans: Vec<FunctionPlan>,
    reads: Vec<FactKey>,
    outputs: Outputs,
    exports: Vec<ModuleExport>,
    revision_floor: u64,
}

pub(crate) fn publish_scope(
    world: &mut World<'_>,
    code_id: CodeId,
    current_scope: ScopeSnapshot,
    surface: &ScopeSurface,
) -> Result<ScopePublication, FatalError> {
    ScopeSession::new(world, code_id, current_scope).publish(surface)
}

pub(crate) fn publish_protocol_surface(
    world: &mut World<'_>,
    module_id: ModuleId,
    namespace: Namespace,
    surface: &ScopeSurface,
) -> ScopePublication {
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
    ScopePublication::Complete {
        namespace: scope,
        revision_floor: 0,
        reads: Vec::new(),
        outputs,
        exports,
    }
}

pub(crate) fn discover_modules(
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

pub(crate) fn record_function_type_refs(
    world: &mut World<'_>,
    function: FunctionId,
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

impl<'world, 'tel> ScopeSession<'world, 'tel> {
    fn new(world: &'world mut World<'tel>, code_id: CodeId, current_scope: ScopeSnapshot) -> Self {
        Self {
            world,
            code_id,
            current_scope,
            current_module: current_scope.module_id(),
            namespace: current_scope.namespace(),
            local_protocols: HashSet::new(),
            pending_types: Vec::new(),
            function_plans: Vec::new(),
            reads: Vec::new(),
            outputs: Vec::new(),
            exports: Vec::new(),
            revision_floor: 0,
        }
    }

    /// Walks one scope in source order and publishes every source-form fact it
    /// defines through this session's accumulated state.
    fn publish(mut self, surface: &ScopeSurface) -> Result<ScopePublication, FatalError> {
        self.local_protocols = local_protocol_names(surface);
        self.reserve_types(&surface.attrs)?;
        self.reserve_local_forms(&surface.forms)?;
        self.note_pending_types();
        if let Some(blocked) = self.apply_ordered_forms(&surface.forms)? {
            return Ok(ScopePublication::Blocked(blocked));
        }
        self.publish_functions();
        Ok(self.complete())
    }

    fn reserve_types(&mut self, attrs: &[Attribute]) -> Result<(), FatalError> {
        for attr in attrs {
            let Attribute::TypeAlias(decl) = attr else {
                continue;
            };
            let body = parse_type_def_body(&decl.body_tokens.0).map_err(|error| {
                emit_job_diagnostic(
                    self.world,
                    Diagnostic::error(
                        codes::RESOLVE_TYPE_ALIAS,
                        format!("compiler2 could not parse `@type {}`: {}", decl.name, error.msg),
                        error.span,
                    ),
                )
            })?;
            let name = TypeName {
                module: self.current_module,
                name: decl.name.clone(),
                arity: decl.params.len(),
            };
            self.namespace =
                self.world
                    .bind_namespace(self.namespace, decl.name.clone(), NamespaceSymbol::Type(name.clone()));
            self.pending_types.push(PendingType {
                name,
                params: decl.params.clone(),
                body,
                span: decl.span,
            });
        }
        Ok(())
    }

    fn reserve_local_forms(&mut self, forms: &[ScopeForm]) -> Result<(), FatalError> {
        for form in forms {
            match form {
                ScopeForm::Function(function) => {
                    let function_id =
                        self.world
                            .reference_function(self.current_module, function.name.clone(), function.arity);
                    let symbol = if function.is_macro {
                        NamespaceSymbol::Macro(function_id)
                    } else {
                        NamespaceSymbol::Function(function_id)
                    };
                    self.namespace = self.world.bind_namespace(self.namespace, function.name.clone(), symbol);
                }
                ScopeForm::Module(module) => {
                    let module_id = self.world.reference_child_module(self.current_module, &module.name);
                    self.namespace = self.world.bind_namespace(
                        self.namespace,
                        module.name.clone(),
                        NamespaceSymbol::Module(module_id),
                    );
                }
                ScopeForm::Protocol(protocol) => {
                    let protocol_id =
                        reference_declared_protocol_module(self.world, self.current_module, &protocol.name);
                    self.namespace = self.world.bind_namespace(
                        self.namespace,
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
                        self.world,
                        Diagnostic::error(
                            codes::INTERNAL_POST_RESOLUTION_LEFTOVER,
                            "compiler2 indexing expected expanded AST without item macro calls",
                            macro_call.span,
                        ),
                    ));
                }
            }
        }
        Ok(())
    }

    fn note_pending_types(&mut self) {
        for PendingType {
            name,
            params,
            body,
            span,
        } in self.pending_types.drain(..)
        {
            let mut refs = Vec::new();
            collect_type_refs(self.world, self.namespace, &body.inner, &mut refs);
            self.world.record_type_def_refs(name.clone(), refs);
            self.world.note_type_decl(
                name,
                NotedTypeDecl {
                    params,
                    body,
                    namespace: self.namespace,
                    span,
                },
            );
        }
    }

    fn apply_ordered_forms(&mut self, forms: &[ScopeForm]) -> Result<Option<JobEffects>, FatalError> {
        for form in forms {
            match form {
                ScopeForm::Alias(alias) => {
                    let module_id = self.world.reference_module(alias.path.join("."));
                    self.namespace = self.world.bind_namespace(
                        self.namespace,
                        alias.as_name.clone(),
                        NamespaceSymbol::Module(module_id),
                    );
                }
                ScopeForm::Import(import) => {
                    if let Some(blocked) = self.apply_import(import)? {
                        return Ok(Some(blocked));
                    }
                }
                ScopeForm::Function(function) => {
                    self.function_plans.push(FunctionPlan {
                        scope: self.current_scope.with_namespace(self.namespace),
                        function: function.clone(),
                    });
                }
                ScopeForm::Module(module) => {
                    let module_id = self.world.reference_child_module(self.current_module, &module.name);
                    self.world.scope_module(module_id, self.namespace);
                }
                ScopeForm::Protocol(protocol) => {
                    let protocol_id =
                        reference_declared_protocol_module(self.world, self.current_module, &protocol.name);
                    self.world.scope_module(protocol_id, self.namespace);
                }
                ScopeForm::ProtocolImpl(protocol_impl) => {
                    let mut outputs = self.define_protocol_impl(protocol_impl)?;
                    self.outputs.append(&mut outputs);
                }
                ScopeForm::Require(_) | ScopeForm::Struct(_) | ScopeForm::MacroCall(_) => {}
            }
        }
        Ok(None)
    }

    fn apply_import(&mut self, import: &super::quoted_surface::ImportForm) -> Result<Option<JobEffects>, FatalError> {
        let imported_module = self.world.reference_module(import.path.join("."));
        if let Some(only) = import.only.as_deref() {
            for (name, arity) in only {
                let function = self.world.reference_function(imported_module, name.clone(), *arity);
                self.namespace =
                    self.world
                        .bind_namespace(self.namespace, name.clone(), NamespaceSymbol::Function(function));
            }
            return Ok(None);
        }

        let surface_fact = FactKey::ModuleDefined(imported_module);
        if self.world.module_defined_revision(imported_module).is_none() {
            let follow_up = if imported_module.is_global() {
                Vec::new()
            } else {
                vec![Job::DefineModule(imported_module)]
            };
            return Ok(Some(JobEffects::wait_on(surface_fact, follow_up)));
        }
        self.reads.push(surface_fact);

        let exports = self.world.module_exports(imported_module);
        if let Some(except) = import.except.as_deref() {
            let mut deny = HashSet::new();
            for (name, arity) in except {
                if find_export(&exports, name, *arity).is_none() {
                    return Err(emit_job_diagnostic(
                        self.world,
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
                self.namespace = bind_export(self.world, self.namespace, export);
            }
        } else {
            for export in &exports {
                self.namespace = bind_export(self.world, self.namespace, export);
            }
        }
        Ok(None)
    }

    fn define_protocol_impl(&mut self, protocol_impl: &ProtocolImplForm) -> Result<Outputs, FatalError> {
        let protocol = reference_impl_protocol_module(
            self.world,
            self.current_module,
            &protocol_impl.protocol,
            &self.local_protocols,
        );
        let target = reference_impl_target_module(self.world, self.current_module, &protocol_impl.target);
        let impl_module = reference_protocol_impl_module(self.world, protocol, target);
        let code_text = self.world.code_text(self.code_id).to_owned();
        let ctx = SurfaceSourceContext::new(self.code_id, &code_text, self.world.tel());
        let body_surface = read_protocol_impl_body_surface(protocol_impl, &ctx).map_err(|error| {
            emit_internal_surface_error(self.world, format!("quoted protocol impl body read failed: {error}"))
        })?;

        let mut impl_scope = self.namespace;
        let mut functions = Vec::new();
        for form in &body_surface.forms {
            let ScopeForm::Function(function) = form else {
                return Err(emit_job_diagnostic(
                    self.world,
                    Diagnostic::error(
                        codes::LOWER_UNSUPPORTED,
                        "compiler2 protocol implementations only support callback functions",
                        protocol_impl.span,
                    ),
                ));
            };
            if function.is_macro {
                return Err(emit_job_diagnostic(
                    self.world,
                    Diagnostic::error(
                        codes::LOWER_UNSUPPORTED,
                        "compiler2 protocol implementations cannot define macros",
                        function.span,
                    ),
                ));
            }
            let function_id = self
                .world
                .reference_function(impl_module, function.name.clone(), function.arity);
            impl_scope = self.world.bind_namespace(
                impl_scope,
                function.name.clone(),
                NamespaceSymbol::Function(function_id),
            );
            functions.push(function.clone());
        }

        let mut outputs = Vec::new();
        let mut callbacks = HashMap::new();
        for function in functions {
            let function_id = self
                .world
                .reference_function(impl_module, function.name.clone(), function.arity);
            let revision = self.world.note_function_source(
                function_id,
                FunctionSource {
                    code: self.code_id,
                    owner_module: self.current_module,
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
                    owner_module: self.current_module,
                },
            );
        }
        self.world.define_protocol_impl(protocol, target, callbacks);
        outputs.extend(self.world.refresh_protocol_domain_facts(protocol));
        outputs.push(self.world.refresh_protocol_dispatch_fact(protocol));
        Ok(outputs)
    }

    fn publish_functions(&mut self) {
        for FunctionPlan { scope, function } in self.function_plans.drain(..) {
            let (output, export) = index_function(self.world, self.code_id, scope, &function);
            self.outputs.push(output);
            if let Some(export) = export {
                self.exports.push(export);
            }
        }
    }

    fn complete(self) -> ScopePublication {
        ScopePublication::Complete {
            namespace: self.namespace,
            revision_floor: self.revision_floor,
            reads: self.reads,
            outputs: self.outputs,
            exports: self.exports,
        }
    }
}

fn local_protocol_names(surface: &ScopeSurface) -> HashSet<String> {
    surface
        .forms
        .iter()
        .filter_map(|form| match form {
            ScopeForm::Protocol(protocol) if protocol.name.segments().len() == 1 => {
                Some(protocol.name.last_segment().to_string())
            }
            _ => None,
        })
        .collect()
}

fn index_function(
    world: &mut World<'_>,
    code_id: CodeId,
    scope: ScopeSnapshot,
    function: &FunctionForm,
) -> (Output, Option<ModuleExport>) {
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
    (
        (FactKey::FunctionSource(function_id), revision),
        export,
    )
}

/// Walks a parsed type expression, recording each name that resolves to a type
/// identity against `scope`. Builtins, free type variables, and unresolvable
/// bare names are not references; resolution decides them, not this walk.
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

/// Walks every type-position of a spec: each parameter, the result, and each
/// constraint bound.
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
