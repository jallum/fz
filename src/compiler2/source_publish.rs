//! Compiler-owned publication for quoted source forms.
//!
//! Source jobs schedule work. This module owns the source-form rules that turn
//! quoted surface readers into namespace mutations and compiler2 fact outputs.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use fz_runtime::any_value::{AnyValueRef, ValueKind};

use crate::ast::{Attribute, SpecDecl, TypeExprBody};
use crate::compiler::source::Span;
use crate::diag::driver::emit_through;
use crate::diag::{Diagnostic, codes};
use crate::function_surface::FunctionSurface;
use crate::modules::identity::ModuleName;
use crate::telemetry::opaque_debug;
use crate::{measurements, metadata};

use super::code::CodeId;
use super::drive::{FactKey, Job, JobEffects};
use super::identity::{FunctionId, FunctionSource, ModuleExport, ModuleId, NotedTypeDecl, TypeName};
use super::namespace::{Namespace, NamespaceSymbol};
use super::protocol::ProtocolCallbackImpl;
use super::quoted_surface::{
    CompilerService, CompilerServiceForm, FunctionForm, MacroCallForm, ProtocolImplForm, ScopeForm, ScopeSurface,
    SurfaceSourceContext, read_module_body_surface, read_protocol_body_surface, read_protocol_impl_body_surface,
    read_scope_surface,
};
use super::scheduler::FatalError;
use super::scope::ScopeSnapshot;
use super::source::{
    QuotedLexicalContextKind, QuotedSourceCursor, QuotedSourceError, QuotedSourceHeap, QuotedSourceMetadata,
    QuotedSourceRoot,
};
use super::source_sugar::rewrite_source_sugar;
use super::type_expr::{NominalKind, TypeDefBody, TypeExpr, parse_type_def_body, parse_type_expr};
use super::world::World;

type Output = (FactKey, u64);
type Outputs = Vec<Output>;
const MAX_MACRO_EXPANSION_DEPTH: usize = 64;

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

enum ExpandedFunction {
    Complete(FunctionForm),
    Blocked(JobEffects),
}

enum ExpandedRoot {
    Complete(QuotedSourceRoot),
    Blocked(JobEffects),
}

enum ExpandedValue {
    Complete(AnyValueRef),
    Blocked(JobEffects),
}

enum FunctionDefinition {
    Complete(FunctionPublication),
    Blocked(JobEffects),
}

enum ProtocolImplDefinition {
    Complete { outputs: Outputs },
    Blocked(JobEffects),
}

struct ScopeSession<'world, 'tel> {
    world: &'world mut World<'tel>,
    code_id: CodeId,
    current_module: ModuleId,
    namespace: Namespace,
    local_protocols: HashSet<String>,
    local_callables: HashMap<(String, usize), NamespaceSymbol>,
    pending_types: Vec<PendingType>,
    required_remote_macros: HashSet<FunctionId>,
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

    let outputs = vec![world.refresh_protocol_dispatch_fact(module_id)];
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
            current_module: current_scope.module_id(),
            namespace: current_scope.namespace(),
            local_protocols: HashSet::new(),
            local_callables: HashMap::new(),
            pending_types: Vec::new(),
            required_remote_macros: HashSet::new(),
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
        if let Some(blocked) = self.publish_module_info()? {
            return Ok(ScopePublication::Blocked(self.blocked_effects(blocked)));
        }
        Ok(self.complete())
    }

    fn publish_module_info(&mut self) -> Result<Option<JobEffects>, FatalError> {
        if self.current_module.is_global()
            || self
                .exports
                .iter()
                .any(|export| export.name == "__info__" && export.arity == 1)
        {
            return Ok(None);
        }

        let module_name = self
            .world
            .module_name(self.current_module)
            .ok_or_else(|| {
                emit_internal_surface_error(
                    self.world,
                    "module info synthesis expected a named current module".to_string(),
                )
            })?
            .to_string();
        let function = build_module_info_function(&self.exports, &module_name).map_err(|error| {
            emit_internal_surface_error(self.world, format!("module info source synthesis failed: {error}"))
        })?;
        let function_id = self
            .world
            .reference_function(self.current_module, function.name.clone(), function.arity);
        self.namespace = self.world.bind_namespace(
            self.namespace,
            function.name.clone(),
            NamespaceSymbol::Function(function_id),
        );
        let publication = match self.define_source_function(
            self.current_module,
            self.current_module,
            self.namespace,
            &function,
            true,
        )? {
            FunctionDefinition::Complete(publication) => publication,
            FunctionDefinition::Blocked(effects) => return Ok(Some(effects)),
        };
        self.outputs.push(publication.output);
        if let Some(export) = publication.export {
            self.exports.push(export);
        }
        Ok(None)
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
                    self.local_callables
                        .insert((function.name.clone(), function.arity), symbol.clone());
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
                | ScopeForm::CompilerService(_)
                | ScopeForm::Struct(_)
                | ScopeForm::ProtocolImpl(_)
                | ScopeForm::MacroCall(_) => {}
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
                        return Ok(Some(self.blocked_effects(blocked)));
                    }
                }
                ScopeForm::Require(import) => {
                    if let Some(blocked) = self.apply_require(import)? {
                        return Ok(Some(self.blocked_effects(blocked)));
                    }
                }
                ScopeForm::CompilerService(service) => {
                    self.apply_compiler_service(service)?;
                }
                ScopeForm::Function(function) => {
                    let publication = match self.define_source_function(
                        self.current_module,
                        self.current_module,
                        self.namespace,
                        function,
                        true,
                    )? {
                        FunctionDefinition::Complete(publication) => publication,
                        FunctionDefinition::Blocked(effects) => return Ok(Some(self.blocked_effects(effects))),
                    };
                    self.outputs.push(publication.output);
                    if let Some(export) = publication.export {
                        self.exports.push(export);
                    }
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
                ScopeForm::ProtocolImpl(protocol_impl) => match self.define_protocol_impl(protocol_impl)? {
                    ProtocolImplDefinition::Complete { mut outputs } => {
                        self.outputs.append(&mut outputs);
                    }
                    ProtocolImplDefinition::Blocked(effects) => return Ok(Some(self.blocked_effects(effects))),
                },
                ScopeForm::MacroCall(macro_call) => {
                    if let Some(blocked) = self.apply_item_macro_call(macro_call)? {
                        return Ok(Some(self.blocked_effects(blocked)));
                    }
                }
                ScopeForm::Struct(_) => {}
            }
        }
        Ok(None)
    }

    fn apply_compiler_service(&mut self, service: &CompilerServiceForm) -> Result<(), FatalError> {
        match service.service {
            CompilerService::Define => self.apply_compiler_define(service),
        }
    }

    fn apply_compiler_define(&mut self, service: &CompilerServiceForm) -> Result<(), FatalError> {
        let mut surface = self.scope_surface_from_root(&service.source, "Fz.Compiler.define source")?;
        let code_text = self.world.code_text(self.code_id).to_owned();
        let ctx = SurfaceSourceContext::new(self.code_id, &code_text);
        if !surface.attrs.is_empty() || surface.forms.len() != 1 {
            return Err(emit_job_diagnostic(
                self.world,
                Diagnostic::error(
                    codes::INTERNAL_POST_RESOLUTION_LEFTOVER,
                    "Fz.Compiler.define expected one fully expanded source definition",
                    service.span,
                ),
            ));
        }
        match surface.forms.remove(0) {
            ScopeForm::Function(function) => {
                let function_id =
                    self.world
                        .reference_function(self.current_module, function.name.clone(), function.arity);
                let symbol = if function.is_macro {
                    NamespaceSymbol::Macro(function_id)
                } else {
                    NamespaceSymbol::Function(function_id)
                };
                self.local_callables
                    .insert((function.name.clone(), function.arity), symbol.clone());
                self.namespace = self.world.bind_namespace(self.namespace, function.name.clone(), symbol);
                let publication = publish_function_source(
                    self.world,
                    self.code_id,
                    self.current_module,
                    self.current_module,
                    self.namespace,
                    &function,
                    true,
                    &service.env,
                );
                self.outputs.push(publication.output);
                if let Some(export) = publication.export {
                    self.exports.push(export);
                }
                Ok(())
            }
            ScopeForm::Module(module) => {
                let module_id = self.world.reference_child_module(self.current_module, &module.name);
                let nested = read_module_body_surface(&module, &ctx).map_err(|error| {
                    emit_internal_surface_error(
                        self.world,
                        format!("Fz.Compiler.define module body read failed: {error}"),
                    )
                })?;
                let revision = self.world.index_module_body(
                    module_id,
                    self.code_id,
                    self.current_module,
                    module.name.clone(),
                    module.source.clone(),
                    nested.clone(),
                );
                self.outputs.push((FactKey::ModuleIndexed(module_id), revision));
                discover_modules(self.world, self.code_id, module_id, &nested, &ctx, &mut self.outputs)?;
                self.namespace =
                    self.world
                        .bind_namespace(self.namespace, module.name.clone(), NamespaceSymbol::Module(module_id));
                self.world.scope_module(module_id, self.namespace);
                Ok(())
            }
            ScopeForm::Protocol(protocol) => {
                let protocol_id = reference_declared_protocol_module(self.world, self.current_module, &protocol.name);
                let protocol_surface = read_protocol_body_surface(&protocol, &ctx).map_err(|error| {
                    emit_internal_surface_error(
                        self.world,
                        format!("Fz.Compiler.define protocol body read failed: {error}"),
                    )
                })?;
                let revision = self.world.index_protocol_module(
                    protocol_id,
                    self.code_id,
                    self.current_module,
                    protocol.name.last_segment().to_string(),
                    protocol.source.clone(),
                    protocol_surface,
                );
                self.outputs.push((FactKey::ModuleIndexed(protocol_id), revision));
                self.namespace = self.world.bind_namespace(
                    self.namespace,
                    protocol.name.last_segment().to_string(),
                    NamespaceSymbol::Module(protocol_id),
                );
                self.world.scope_module(protocol_id, self.namespace);
                Ok(())
            }
            ScopeForm::ProtocolImpl(protocol_impl) => match self.define_protocol_impl(&protocol_impl)? {
                ProtocolImplDefinition::Complete { mut outputs } => {
                    self.outputs.append(&mut outputs);
                    Ok(())
                }
                ProtocolImplDefinition::Blocked(_) => Err(emit_job_diagnostic(
                    self.world,
                    Diagnostic::error(
                        codes::INTERNAL_POST_RESOLUTION_LEFTOVER,
                        "Fz.Compiler.define cannot block while applying a protocol implementation",
                        service.span,
                    ),
                )),
            },
            ScopeForm::Alias(alias) => {
                let module_id = self.world.reference_module(alias.path.join("."));
                self.namespace = self.world.bind_namespace(
                    self.namespace,
                    alias.as_name.clone(),
                    NamespaceSymbol::Module(module_id),
                );
                Ok(())
            }
            ScopeForm::Import(import) => {
                if self.apply_import(&import)?.is_some() {
                    return Err(emit_job_diagnostic(
                        self.world,
                        Diagnostic::error(
                            codes::INTERNAL_POST_RESOLUTION_LEFTOVER,
                            "Fz.Compiler.define cannot block while applying nested import/require",
                            service.span,
                        ),
                    ));
                }
                Ok(())
            }
            ScopeForm::Require(import) => {
                if self.apply_require(&import)?.is_some() {
                    return Err(emit_job_diagnostic(
                        self.world,
                        Diagnostic::error(
                            codes::INTERNAL_POST_RESOLUTION_LEFTOVER,
                            "Fz.Compiler.define cannot block while applying nested import/require",
                            service.span,
                        ),
                    ));
                }
                Ok(())
            }
            ScopeForm::Struct(_) => Ok(()),
            ScopeForm::CompilerService(_) | ScopeForm::MacroCall(_) => Err(emit_job_diagnostic(
                self.world,
                Diagnostic::error(
                    codes::INTERNAL_POST_RESOLUTION_LEFTOVER,
                    "Fz.Compiler.define expected one fully expanded source definition",
                    service.span,
                ),
            )),
        }
    }

    fn define_source_function(
        &mut self,
        function_module: ModuleId,
        owner_module: ModuleId,
        namespace: Namespace,
        function: &FunctionForm,
        export_public: bool,
    ) -> Result<FunctionDefinition, FatalError> {
        let function_id = self
            .world
            .reference_function(function_module, function.name.clone(), function.arity);
        let function_scope = ScopeSnapshot::function(function_module, namespace, function_id);
        let function = match self.expand_function_form(function, function_scope)? {
            ExpandedFunction::Complete(function) => function,
            ExpandedFunction::Blocked(effects) => return Ok(FunctionDefinition::Blocked(effects)),
        };
        let env = self.project_compiler_define_env(&function.source, function_scope)?;
        Ok(FunctionDefinition::Complete(publish_function_source(
            self.world,
            self.code_id,
            function_module,
            owner_module,
            namespace,
            &function,
            export_public,
            &env,
        )))
    }

    fn project_compiler_define_env(
        &self,
        source: &QuotedSourceRoot,
        scope: ScopeSnapshot,
    ) -> Result<QuotedSourceRoot, FatalError> {
        let builder = source.builder();
        let env = self
            .world
            .project_env_value(&builder, scope, QuotedLexicalContextKind::Definition)
            .map_err(|error| emit_internal_surface_error(self.world, format!("__ENV__ projection failed: {error}")))?;
        Ok(source.subroot(env))
    }

    fn apply_item_macro_call(&mut self, macro_call: &MacroCallForm) -> Result<Option<JobEffects>, FatalError> {
        let scope = ScopeSnapshot::module(self.current_module, self.namespace);
        let expanded = match self.expand_item_macro_call(macro_call, scope)? {
            ExpandedRoot::Complete(root) => root,
            ExpandedRoot::Blocked(effects) => return Ok(Some(effects)),
        };
        let surface = self.surface_from_expanded_item_macro(&expanded, macro_call.span)?;
        self.apply_surface_fragment(&surface)
    }

    fn expand_item_macro_call(
        &mut self,
        macro_call: &MacroCallForm,
        scope: ScopeSnapshot,
    ) -> Result<ExpandedRoot, FatalError> {
        let owner = &macro_call.source;
        let cursor = owner.cursor();
        let Some(node) = cursor.ast_node().map_err(|error| {
            emit_internal_surface_error(self.world, format!("item macro source read failed: {error}"))
        })?
        else {
            return Err(self.item_macro_not_defmacro("item", macro_call.span));
        };
        let Some(result) = self.expand_ast_call(owner, &cursor, &node, scope, 0)? else {
            return Err(self.item_macro_not_defmacro(&item_macro_display_name(&node), macro_call.span));
        };
        match result {
            ExpandedValue::Complete(root) => Ok(ExpandedRoot::Complete(owner.subroot(root))),
            ExpandedValue::Blocked(effects) => Ok(ExpandedRoot::Blocked(effects)),
        }
    }

    fn surface_from_expanded_item_macro(
        &self,
        root: &QuotedSourceRoot,
        span: Span,
    ) -> Result<ScopeSurface, FatalError> {
        let surface = self.scope_surface_from_root(root, "item macro expanded source")?;
        if surface.forms.iter().any(|form| matches!(form, ScopeForm::MacroCall(_))) {
            return Err(emit_job_diagnostic(
                self.world,
                Diagnostic::error(
                    codes::MACRO_NOT_A_DEFMACRO,
                    "item macro expansion returned a non-definition call",
                    span,
                ),
            ));
        }
        Ok(surface)
    }

    fn scope_surface_from_root(&self, root: &QuotedSourceRoot, context: &str) -> Result<ScopeSurface, FatalError> {
        let code_text = self.world.code_text(self.code_id).to_owned();
        let ctx = SurfaceSourceContext::new(self.code_id, &code_text);
        let source = if root.root().is_empty_list() || root.root().tag() == ValueKind::LIST {
            root.clone()
        } else {
            root.interned_list_subroot(&[root.root()]).map_err(|error| {
                emit_internal_surface_error(self.world, format!("{context} wrapper failed: {error}"))
            })?
        };
        read_scope_surface(&source, &ctx)
            .map_err(|error| emit_internal_surface_error(self.world, format!("{context} read failed: {error}")))
    }

    fn apply_surface_fragment(&mut self, surface: &ScopeSurface) -> Result<Option<JobEffects>, FatalError> {
        self.reserve_types(&surface.attrs)?;
        self.reserve_local_forms(&surface.forms)?;
        self.note_pending_types();
        self.apply_ordered_forms(&surface.forms)
    }

    fn item_macro_not_defmacro(&self, name: &str, span: Span) -> FatalError {
        emit_job_diagnostic(
            self.world,
            Diagnostic::error(
                codes::MACRO_NOT_A_DEFMACRO,
                format!("item-level call `{name}(...)` is not a defmacro"),
                span,
            ),
        )
    }

    fn expand_function_form(
        &mut self,
        function: &FunctionForm,
        scope: ScopeSnapshot,
    ) -> Result<ExpandedFunction, FatalError> {
        match self.expand_function_source(function.source.clone(), scope, 0)? {
            ExpandedRoot::Complete(source) => {
                let mut function = function.clone();
                function.source = source;
                Ok(ExpandedFunction::Complete(function))
            }
            ExpandedRoot::Blocked(effects) => Ok(ExpandedFunction::Blocked(effects)),
        }
    }

    fn expand_function_source(
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

        if changed {
            let root = source.builder().list(&expanded).map_err(|error| {
                emit_internal_surface_error(self.world, format!("grouped function source rebuild failed: {error}"))
            })?;
            Ok(ExpandedRoot::Complete(source.subroot(root)))
        } else {
            Ok(ExpandedRoot::Complete(source))
        }
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

    fn expand_root(
        &mut self,
        root: QuotedSourceRoot,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedRoot, FatalError> {
        match self.expand_cursor(&root, &root.cursor(), scope, depth)? {
            ExpandedValue::Complete(value) => Ok(ExpandedRoot::Complete(root.subroot(value))),
            ExpandedValue::Blocked(effects) => Ok(ExpandedRoot::Blocked(effects)),
        }
    }

    fn expand_cursor(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, FatalError> {
        if depth > MAX_MACRO_EXPANSION_DEPTH {
            return Err(emit_job_diagnostic(
                self.world,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    format!("compiler2 macro expansion exceeded depth budget {MAX_MACRO_EXPANSION_DEPTH}"),
                    Span::DUMMY,
                ),
            ));
        }

        if let Some(node) = cursor.ast_node().map_err(|error| {
            emit_internal_surface_error(self.world, format!("quoted expansion read failed: {error}"))
        })? {
            if let Some(rewritten) = rewrite_source_sugar(owner, &node).map_err(|error| {
                emit_internal_surface_error(self.world, format!("source sugar rewrite failed: {error}"))
            })? {
                return match self.expand_root(owner.subroot(rewritten), scope, depth)? {
                    ExpandedRoot::Complete(root) => Ok(ExpandedValue::Complete(root.root())),
                    ExpandedRoot::Blocked(effects) => Ok(ExpandedValue::Blocked(effects)),
                };
            }
            if let Some(result) = self.expand_ast_call(owner, cursor, &node, scope, depth)? {
                return Ok(result);
            }
            return self.expand_ast_node(owner, cursor, &node, scope, depth);
        }

        match cursor.root().tag() {
            ValueKind::LIST => self.expand_list(owner, cursor, scope, depth),
            ValueKind::STRUCT => self.expand_tuple(owner, cursor, scope, depth),
            ValueKind::MAP => self.expand_map(owner, cursor, scope, depth),
            _ => Ok(ExpandedValue::Complete(cursor.root())),
        }
    }

    fn expand_ast_node(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        node: &super::source::QuotedAstNode,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, FatalError> {
        let head = match self.expand_cursor(owner, &node.head, scope, depth)? {
            ExpandedValue::Complete(root) => root,
            ExpandedValue::Blocked(effects) => return Ok(ExpandedValue::Blocked(effects)),
        };
        let tail = match self.expand_cursor(owner, &node.tail, scope, depth)? {
            ExpandedValue::Complete(root) => root,
            ExpandedValue::Blocked(effects) => return Ok(ExpandedValue::Blocked(effects)),
        };
        if head == node.head.root() && tail == node.tail.root() {
            return Ok(ExpandedValue::Complete(cursor.root()));
        }
        let rebuilt = owner
            .builder()
            .tuple(&[head, node.meta.root(), tail])
            .map_err(|error| emit_internal_surface_error(self.world, format!("quoted AST rebuild failed: {error}")))?;
        Ok(ExpandedValue::Complete(rebuilt))
    }

    fn expand_ast_call(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        node: &super::source::QuotedAstNode,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<Option<ExpandedValue>, FatalError> {
        if !is_list_like(&node.tail) {
            return Ok(None);
        }
        let args = node.tail.list_items().map_err(|error| {
            emit_internal_surface_error(self.world, format!("quoted call arg read failed: {error}"))
        })?;

        if let Some(result) = self.expand_remote_ast_call(owner, node, scope, depth, cursor.root(), &args)? {
            return Ok(Some(result));
        }

        let Ok(head) = node.head.atom_name() else {
            return Ok(None);
        };
        if head == "quote" {
            return Ok(Some(ExpandedValue::Complete(cursor.root())));
        }
        let Some(symbol) = self
            .world
            .lookup_callable_namespace(scope.namespace(), &head, args.len())
        else {
            return Ok(None);
        };
        let function = match symbol {
            NamespaceSymbol::Macro(function) => function,
            NamespaceSymbol::Function(_) | NamespaceSymbol::Module(_) | NamespaceSymbol::Type(_) => return Ok(None),
        };
        self.expand_macro_invocation(owner, cursor.root(), function, scope, depth, &args)
            .map(Some)
    }

    fn expand_remote_ast_call(
        &mut self,
        owner: &QuotedSourceRoot,
        node: &super::source::QuotedAstNode,
        scope: ScopeSnapshot,
        depth: usize,
        input_root: AnyValueRef,
        args: &[QuotedSourceCursor],
    ) -> Result<Option<ExpandedValue>, FatalError> {
        let Some(head_node) = node.head.ast_node().map_err(|error| {
            emit_internal_surface_error(self.world, format!("quoted remote call read failed: {error}"))
        })?
        else {
            return Ok(None);
        };
        if head_node.head.atom_name().as_deref() != Ok(".") {
            return Ok(None);
        }
        let target = head_node.tail.list_items().map_err(|error| {
            emit_internal_surface_error(self.world, format!("quoted remote target read failed: {error}"))
        })?;
        let [module_cursor, function_cursor] = target.as_slice() else {
            return Ok(None);
        };
        let module_path = match alias_path(module_cursor) {
            Ok(path) => path,
            Err(_) => return Ok(None),
        };
        let function_name = function_cursor.atom_name().map_err(|error| {
            emit_internal_surface_error(self.world, format!("quoted remote function name read failed: {error}"))
        })?;
        let Some(module) = self.world.lookup_module_path(scope.namespace(), &module_path.join(".")) else {
            return Ok(None);
        };
        if module == self.current_module {
            return self.expand_current_module_remote_ast_call(
                owner,
                scope,
                depth,
                input_root,
                args,
                &function_name,
                &module_path,
            );
        }
        if self.world.module_defined_revision(module).is_none() {
            if self.world.is_runtime_module(module) {
                return Ok(None);
            }
            let follow_up = if module.is_global() {
                Vec::new()
            } else {
                vec![Job::DefineModule(module)]
            };
            return Ok(Some(ExpandedValue::Blocked(JobEffects::wait_on(
                FactKey::ModuleDefined(module),
                follow_up,
            ))));
        }
        self.reads.push(FactKey::ModuleDefined(module));
        let Some(NamespaceSymbol::Macro(function)) =
            self.world.lookup_module_callable(module, &function_name, args.len())
        else {
            return Ok(None);
        };
        if !self.required_remote_macros.contains(&function) {
            return Err(self.remote_macro_not_required(&function_name, args.len(), &module_path));
        }
        self.expand_macro_invocation(owner, input_root, function, scope, depth, args)
            .map(Some)
    }

    fn expand_current_module_remote_ast_call(
        &mut self,
        owner: &QuotedSourceRoot,
        scope: ScopeSnapshot,
        depth: usize,
        input_root: AnyValueRef,
        args: &[QuotedSourceCursor],
        function_name: &str,
        module_path: &[String],
    ) -> Result<Option<ExpandedValue>, FatalError> {
        let Some(symbol) = self.lookup_current_module_callable(function_name, args.len()) else {
            return Ok(None);
        };
        let NamespaceSymbol::Macro(function) = symbol else {
            return Ok(None);
        };
        if !self.required_remote_macros.contains(&function) {
            return Err(self.remote_macro_not_required(function_name, args.len(), module_path));
        }
        self.expand_macro_invocation(owner, input_root, function, scope, depth, args)
            .map(Some)
    }

    fn lookup_current_module_callable(&mut self, name: &str, arity: usize) -> Option<NamespaceSymbol> {
        match self.local_callables.get(&(name.to_string(), arity)).cloned() {
            Some(NamespaceSymbol::Function(function))
                if self.world.function_module(function) == self.current_module =>
            {
                Some(NamespaceSymbol::Function(function))
            }
            Some(NamespaceSymbol::Macro(function)) if self.world.function_module(function) == self.current_module => {
                Some(NamespaceSymbol::Macro(function))
            }
            _ => None,
        }
    }

    fn remote_macro_not_required(&mut self, function_name: &str, arity: usize, module_path: &[String]) -> FatalError {
        let module_name = module_path.join(".");
        emit_job_diagnostic(
            self.world,
            Diagnostic::error(
                codes::MACRO_NOT_REQUIRED,
                format!(
                    "remote macro `{}.{}/{}` requires `require {}` before source expansion",
                    module_name, function_name, arity, module_name
                ),
                Span::DUMMY,
            ),
        )
    }

    fn expand_macro_invocation(
        &mut self,
        owner: &QuotedSourceRoot,
        input_root: AnyValueRef,
        function: FunctionId,
        scope: ScopeSnapshot,
        depth: usize,
        args: &[QuotedSourceCursor],
    ) -> Result<ExpandedValue, FatalError> {
        let macro_fact = FactKey::MacroExecutable(function);
        if self.world.fact_revision(macro_fact.clone()).is_none() {
            return Ok(ExpandedValue::Blocked(JobEffects::wait_on(
                macro_fact,
                [Job::BuildMacroExecutable(function)],
            )));
        }
        self.reads.push(macro_fact);

        let builder = owner.builder();
        let caller = self
            .world
            .project_env_value(&builder, scope, QuotedLexicalContextKind::Caller)
            .map_err(|error| emit_internal_surface_error(self.world, format!("__ENV__ projection failed: {error}")))?;
        let arg_roots = args.iter().map(QuotedSourceCursor::root).collect::<Vec<_>>();
        let expanded = self
            .world
            .run_macro_on_source(function, owner, caller, &arg_roots)
            .map_err(|error| {
                emit_job_diagnostic(
                    self.world,
                    Diagnostic::error(codes::LOWER_UNSUPPORTED, error, Span::DUMMY),
                )
            })?;
        emit_macro_expanded(self.world, function, owner, input_root, &expanded, depth, args.len());
        match self.expand_root(expanded, scope, depth + 1)? {
            ExpandedRoot::Complete(root) => Ok(ExpandedValue::Complete(root.root())),
            ExpandedRoot::Blocked(effects) => Ok(ExpandedValue::Blocked(effects)),
        }
    }

    fn expand_list(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, FatalError> {
        let items = cursor.list_items().map_err(|error| {
            emit_internal_surface_error(self.world, format!("quoted list expansion failed: {error}"))
        })?;
        let mut changed = false;
        let mut expanded = Vec::with_capacity(items.len());
        for item in items {
            match self.expand_cursor(owner, &item, scope, depth)? {
                ExpandedValue::Complete(value) => {
                    changed |= value != item.root();
                    expanded.push(value);
                }
                ExpandedValue::Blocked(effects) => return Ok(ExpandedValue::Blocked(effects)),
            }
        }
        if changed {
            let root = owner.builder().list(&expanded).map_err(|error| {
                emit_internal_surface_error(self.world, format!("quoted list rebuild failed: {error}"))
            })?;
            Ok(ExpandedValue::Complete(root))
        } else {
            Ok(ExpandedValue::Complete(cursor.root()))
        }
    }

    fn expand_tuple(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, FatalError> {
        let items = cursor.tuple_items().map_err(|error| {
            emit_internal_surface_error(self.world, format!("quoted tuple expansion failed: {error}"))
        })?;
        let mut changed = false;
        let mut expanded = Vec::with_capacity(items.len());
        for item in items {
            match self.expand_cursor(owner, &item, scope, depth)? {
                ExpandedValue::Complete(value) => {
                    changed |= value != item.root();
                    expanded.push(value);
                }
                ExpandedValue::Blocked(effects) => return Ok(ExpandedValue::Blocked(effects)),
            }
        }
        if changed {
            let root = owner.builder().tuple(&expanded).map_err(|error| {
                emit_internal_surface_error(self.world, format!("quoted tuple rebuild failed: {error}"))
            })?;
            Ok(ExpandedValue::Complete(root))
        } else {
            Ok(ExpandedValue::Complete(cursor.root()))
        }
    }

    fn expand_map(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, FatalError> {
        let entries = cursor.map_entries().map_err(|error| {
            emit_internal_surface_error(self.world, format!("quoted map expansion failed: {error}"))
        })?;
        let mut changed = false;
        let mut expanded = Vec::with_capacity(entries.len());
        for (key, value) in entries {
            let key_root = match self.expand_cursor(owner, &key, scope, depth)? {
                ExpandedValue::Complete(root) => root,
                ExpandedValue::Blocked(effects) => return Ok(ExpandedValue::Blocked(effects)),
            };
            let value_root = match self.expand_cursor(owner, &value, scope, depth)? {
                ExpandedValue::Complete(root) => root,
                ExpandedValue::Blocked(effects) => return Ok(ExpandedValue::Blocked(effects)),
            };
            changed |= key_root != key.root() || value_root != value.root();
            expanded.push((key_root, value_root));
        }
        if changed {
            let root = owner.builder().map(&expanded).map_err(|error| {
                emit_internal_surface_error(self.world, format!("quoted map rebuild failed: {error}"))
            })?;
            Ok(ExpandedValue::Complete(root))
        } else {
            Ok(ExpandedValue::Complete(cursor.root()))
        }
    }

    fn blocked_effects(&self, mut effects: JobEffects) -> JobEffects {
        effects.reads.extend(self.reads.clone());
        effects.outputs.extend(self.outputs.clone());
        effects
    }

    fn apply_require(&mut self, import: &super::quoted_surface::ImportForm) -> Result<Option<JobEffects>, FatalError> {
        let required_module = self.world.reference_module(import.path.join("."));
        let surface_fact = FactKey::ModuleDefined(required_module);
        if self.world.module_defined_revision(required_module).is_none() {
            let follow_up = if required_module.is_global() {
                Vec::new()
            } else {
                vec![Job::DefineModule(required_module)]
            };
            return Ok(Some(JobEffects::wait_on(surface_fact, follow_up)));
        }
        self.reads.push(surface_fact);

        let exports = self.world.module_exports(required_module);
        let selected = self.select_required_macro_exports(import, &exports)?;
        if let Some(blocked) = self.wait_for_imported_macro_executables(&selected) {
            return Ok(Some(blocked));
        }
        self.record_required_remote_macros(&selected);
        Ok(None)
    }

    fn select_required_macro_exports(
        &mut self,
        import: &super::quoted_surface::ImportForm,
        exports: &[ModuleExport],
    ) -> Result<Vec<ModuleExport>, FatalError> {
        if let Some(only) = import.only.as_deref() {
            let mut selected = Vec::with_capacity(only.len());
            for (name, arity) in only {
                let Some(export) = find_export(exports, name, *arity) else {
                    return Err(emit_job_diagnostic(
                        self.world,
                        Diagnostic::error(
                            codes::RESOLVE_UNKNOWN_IMPORT,
                            format!(
                                "module `{}` does not export macro `{}/{}`",
                                import.path.join("."),
                                name,
                                arity
                            ),
                            import.span,
                        ),
                    ));
                };
                if !matches!(export.symbol, NamespaceSymbol::Macro(_)) {
                    return Err(emit_job_diagnostic(
                        self.world,
                        Diagnostic::error(
                            codes::RESOLVE_UNKNOWN_IMPORT,
                            format!(
                                "module `{}` does not export macro `{}/{}`",
                                import.path.join("."),
                                name,
                                arity
                            ),
                            import.span,
                        ),
                    ));
                }
                selected.push(export.clone());
            }
            return Ok(selected);
        }

        let mut denied = HashSet::new();
        for (name, arity) in import.except.as_deref().unwrap_or(&[]) {
            let Some(export) = find_export(exports, name, *arity) else {
                return Err(emit_job_diagnostic(
                    self.world,
                    Diagnostic::error(
                        codes::RESOLVE_UNKNOWN_IMPORT,
                        format!(
                            "module `{}` does not export macro `{}/{}`",
                            import.path.join("."),
                            name,
                            arity
                        ),
                        import.span,
                    ),
                ));
            };
            if !matches!(export.symbol, NamespaceSymbol::Macro(_)) {
                return Err(emit_job_diagnostic(
                    self.world,
                    Diagnostic::error(
                        codes::RESOLVE_UNKNOWN_IMPORT,
                        format!(
                            "module `{}` does not export macro `{}/{}`",
                            import.path.join("."),
                            name,
                            arity
                        ),
                        import.span,
                    ),
                ));
            }
            denied.insert((name.as_str(), *arity));
        }
        Ok(exports
            .iter()
            .filter(|export| matches!(export.symbol, NamespaceSymbol::Macro(_)))
            .filter(|export| !denied.contains(&(export.name.as_str(), export.arity)))
            .cloned()
            .collect())
    }

    fn apply_import(&mut self, import: &super::quoted_surface::ImportForm) -> Result<Option<JobEffects>, FatalError> {
        let imported_module = self.world.reference_module(import.path.join("."));
        let surface_fact = FactKey::ModuleDefined(imported_module);
        if self.world.module_defined_revision(imported_module).is_none() {
            if let Some(only) = import.only.as_deref() {
                if !self.world.is_runtime_prelude(self.code_id) {
                    let follow_up = if imported_module.is_global() {
                        Vec::new()
                    } else {
                        vec![Job::DefineModule(imported_module)]
                    };
                    return Ok(Some(JobEffects::wait_on(surface_fact, follow_up)));
                }
                for (name, arity) in only {
                    let function = self.world.reference_function(imported_module, name.clone(), *arity);
                    self.namespace =
                        self.world
                            .bind_namespace(self.namespace, name.clone(), NamespaceSymbol::Function(function));
                }
                return Ok(None);
            }
            let follow_up = if imported_module.is_global() {
                Vec::new()
            } else {
                vec![Job::DefineModule(imported_module)]
            };
            return Ok(Some(JobEffects::wait_on(surface_fact, follow_up)));
        }
        self.reads.push(surface_fact);

        let exports = self.world.module_exports(imported_module);
        let selected = if let Some(only) = import.only.as_deref() {
            let mut selected = Vec::with_capacity(only.len());
            for (name, arity) in only {
                let Some(export) = find_export(&exports, name, *arity) else {
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
                };
                selected.push(export.clone());
            }
            selected
        } else if let Some(except) = import.except.as_deref() {
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
            exports
                .iter()
                .filter(|export| !deny.contains(&(export.name.as_str(), export.arity)))
                .cloned()
                .collect()
        } else {
            exports
        };

        if let Some(blocked) = self.wait_for_imported_macro_executables(&selected) {
            return Ok(Some(blocked));
        }
        for export in &selected {
            self.namespace = bind_export(self.world, self.namespace, export);
        }
        Ok(None)
    }

    fn record_required_remote_macros(&mut self, exports: &[ModuleExport]) {
        for export in exports {
            if let NamespaceSymbol::Macro(function) = export.symbol {
                self.required_remote_macros.insert(function);
            }
        }
    }

    fn wait_for_imported_macro_executables(&mut self, exports: &[ModuleExport]) -> Option<JobEffects> {
        let mut effects = JobEffects::default();
        for export in exports {
            let NamespaceSymbol::Macro(function) = export.symbol else {
                continue;
            };
            let fact = FactKey::MacroExecutable(function);
            if self.world.fact_revision(fact.clone()).is_some() {
                self.reads.push(fact);
            } else {
                effects.waits.push(fact);
                effects.follow_up.push(Job::BuildMacroExecutable(function));
            }
        }
        (!effects.waits.is_empty()).then_some(effects)
    }
    fn define_protocol_impl(&mut self, protocol_impl: &ProtocolImplForm) -> Result<ProtocolImplDefinition, FatalError> {
        let protocol = reference_impl_protocol_module(
            self.world,
            self.current_module,
            &protocol_impl.protocol,
            &self.local_protocols,
        );
        let target = reference_impl_target_module(self.world, self.current_module, &protocol_impl.target);
        let impl_module = reference_protocol_impl_module(self.world, protocol, target);
        let code_text = self.world.code_text(self.code_id).to_owned();
        let ctx = SurfaceSourceContext::new(self.code_id, &code_text);
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
            let publication =
                match self.define_source_function(impl_module, self.current_module, impl_scope, &function, false)? {
                    FunctionDefinition::Complete(publication) => publication,
                    FunctionDefinition::Blocked(effects) => return Ok(ProtocolImplDefinition::Blocked(effects)),
                };
            outputs.push(publication.output);
            callbacks.insert(
                (function.name.clone(), function.arity),
                ProtocolCallbackImpl {
                    function: publication.function,
                    owner_module: self.current_module,
                },
            );
        }
        self.world.define_protocol_impl(protocol, target, callbacks);
        outputs.push(self.world.refresh_protocol_dispatch_fact(protocol));
        Ok(ProtocolImplDefinition::Complete { outputs })
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

fn build_module_info_function(exports: &[ModuleExport], module_name: &str) -> Result<FunctionForm, QuotedSourceError> {
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let meta = QuotedSourceMetadata::default();
    let functions = module_info_pairs(&builder, exports, |symbol| {
        matches!(symbol, NamespaceSymbol::Function(_))
    })?;
    let macros = module_info_pairs(&builder, exports, |symbol| matches!(symbol, NamespaceSymbol::Macro(_)))?;
    let kind = builder.variable("kind", &meta)?;
    let body = module_info_case(&builder, &meta, kind, functions, macros, builder.atom(module_name))?;
    let clause = module_info_function_clause(&builder, &meta, kind, body)?;
    Ok(FunctionForm {
        source: builder.root(builder.list(&[clause])?)?,
        name: "__info__".to_string(),
        arity: 1,
        is_macro: false,
        is_private: false,
        variadic: false,
        span: Span::DUMMY,
    })
}

fn module_info_pairs(
    builder: &super::source::QuotedSourceBuilder,
    exports: &[ModuleExport],
    keep: impl Fn(&NamespaceSymbol) -> bool,
) -> Result<AnyValueRef, QuotedSourceError> {
    let pairs = exports
        .iter()
        .filter(|export| keep(&export.symbol))
        .map(|export| builder.tuple(&[builder.atom(&export.name), builder.int(export.arity as i64)]))
        .collect::<Result<Vec<_>, _>>()?;
    builder.list(&pairs)
}

fn module_info_function_clause(
    builder: &super::source::QuotedSourceBuilder,
    meta: &QuotedSourceMetadata,
    param: AnyValueRef,
    body: AnyValueRef,
) -> Result<AnyValueRef, QuotedSourceError> {
    let head = builder.call("__info__", meta, &[param])?;
    let do_kw = builder.keyword("do", body)?;
    let kw = builder.list(&[do_kw])?;
    builder.call("fn", meta, &[head, kw])
}

fn module_info_case(
    builder: &super::source::QuotedSourceBuilder,
    meta: &QuotedSourceMetadata,
    subject: AnyValueRef,
    functions: AnyValueRef,
    macros: AnyValueRef,
    module: AnyValueRef,
) -> Result<AnyValueRef, QuotedSourceError> {
    let clauses = [
        module_info_match_clause(builder, meta, builder.atom("functions"), functions)?,
        module_info_match_clause(builder, meta, builder.atom("macros"), macros)?,
        module_info_match_clause(builder, meta, builder.atom("module"), module)?,
        module_info_match_clause(builder, meta, builder.variable("_", meta)?, builder.nil())?,
    ];
    let body = builder.list(&clauses)?;
    let kw = builder.list(&[builder.keyword("do", body)?])?;
    builder.call("case", meta, &[subject, kw])
}

fn module_info_match_clause(
    builder: &super::source::QuotedSourceBuilder,
    meta: &QuotedSourceMetadata,
    pattern: AnyValueRef,
    body: AnyValueRef,
) -> Result<AnyValueRef, QuotedSourceError> {
    let patterns = builder.list(&[pattern])?;
    builder.call("->", meta, &[patterns, body])
}

fn item_macro_display_name(node: &super::source::QuotedAstNode) -> String {
    if let Ok(name) = node.head.atom_name() {
        return name;
    }
    if let Ok(Some(head_node)) = node.head.ast_node()
        && head_node.head.atom_name().as_deref() == Ok(".")
        && let Ok(parts) = head_node.tail.list_items()
        && let [module, function] = parts.as_slice()
        && let Ok(path) = alias_path(module)
        && let Ok(function) = function.atom_name()
    {
        return format!("{}.{}", path.join("."), function);
    }
    "item".to_string()
}

fn alias_path(cursor: &QuotedSourceCursor) -> Result<Vec<String>, QuotedSourceError> {
    let Some(node) = cursor.ast_node()? else {
        return Err(QuotedSourceError::new("expected quoted module alias"));
    };
    if node.head.atom_name()? != "__aliases__" {
        return Err(QuotedSourceError::new("expected quoted module alias"));
    }
    node.tail.list_atom_names()
}

fn is_list_like(cursor: &QuotedSourceCursor) -> bool {
    cursor.root().is_empty_list() || cursor.root().tag() == ValueKind::LIST
}

struct FunctionPublication {
    function: FunctionId,
    output: Output,
    export: Option<ModuleExport>,
}

fn publish_function_source(
    world: &mut World<'_>,
    code_id: CodeId,
    function_module: ModuleId,
    owner_module: ModuleId,
    namespace: Namespace,
    function: &FunctionForm,
    export_public: bool,
    env: &super::source::QuotedSourceRoot,
) -> FunctionPublication {
    let function_id = world.reference_function(function_module, function.name.clone(), function.arity);
    let revision = world.note_function_source(
        function_id,
        FunctionSource {
            code: code_id,
            owner_module,
            namespace,
            capture_params: Vec::new(),
            variadic: function.variadic,
            source: function.source.clone(),
        },
    );

    let symbol = if function.is_macro {
        NamespaceSymbol::Macro(function_id)
    } else {
        NamespaceSymbol::Function(function_id)
    };
    let export = (export_public && !function.is_private).then(|| ModuleExport {
        name: function.name.clone(),
        arity: function.arity,
        variadic: function.variadic,
        symbol: symbol.clone(),
    });
    let source = world
        .function_source(function_id)
        .expect("function source should exist immediately after compiler service publication");
    emit_compiler_service_define(world, function_id, &source, revision, env);
    FunctionPublication {
        function: function_id,
        output: (FactKey::FunctionSource(function_id), revision),
        export,
    }
}

fn emit_compiler_service_define(
    world: &World<'_>,
    function: FunctionId,
    source: &FunctionSource,
    revision: u64,
    env: &super::source::QuotedSourceRoot,
) {
    let function_ref = world.function_ref(function);
    world.tel().execute(
        &["fz", "compiler2", "compiler_service", "define"],
        &measurements! {
            code_id: source.code.as_u32() as u64,
            module_id: function_ref.module.as_u32() as u64,
            owner_module_id: source.owner_module.as_u32() as u64,
            function_id: function.as_u32() as u64,
            revision: revision,
            namespace: source.namespace.as_u32() as u64,
            source_heap_id: source.source.key().heap_id as u64,
            source_root_ref: source.source.root().raw_word(),
            env_root_ref: env.root().raw_word(),
        },
        &metadata! {
            origin: "fz_compiler",
            function_ref: opaque_debug(function_ref),
        },
    );
}

fn emit_macro_expanded(
    world: &World<'_>,
    function: FunctionId,
    input: &QuotedSourceRoot,
    input_root: AnyValueRef,
    output: &QuotedSourceRoot,
    depth: usize,
    arg_count: usize,
) {
    let function_ref = world.function_ref(function);
    world.tel().execute(
        &["fz", "compiler2", "macro", "expanded"],
        &measurements! {
            function_id: function.as_u32() as u64,
            module_id: function_ref.module.as_u32() as u64,
            depth: depth as u64,
            depth_budget: MAX_MACRO_EXPANSION_DEPTH as u64,
            arg_count: arg_count as u64,
            input_heap_id: input.key().heap_id as u64,
            input_root_ref: input_root.raw_word(),
            output_heap_id: output.key().heap_id as u64,
            output_root_ref: output.root().raw_word(),
        },
        &metadata! {
            function_ref: opaque_debug(function_ref),
        },
    );
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
