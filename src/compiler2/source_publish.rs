//! Compiler-owned publication for quoted source forms.
//!
//! Source jobs schedule work. This module owns the source-form rules that turn
//! quoted surface readers into namespace mutations and compiler2 fact outputs.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use fz_runtime::any_value::AnyValueRef;

use crate::ast::{Attribute, SpecDecl, TypeExprBody};
use crate::diag::{Diagnostic, codes};
use crate::function_surface::FunctionSurface;
use crate::modules::identity::ModuleName;
use crate::source::Span;
use crate::telemetry::opaque_debug;
use crate::{measurements, metadata};

use super::code::CodeId;
use super::drive::{FactKey, Job, JobEffects, current_uses};
use super::identity::{FunctionId, FunctionSource, ModuleId, NotedTypeDecl, ProtocolImplSource, TypeName};
use super::module_interface::{InterfaceCallableKind, InterfaceRequester, ModuleInterface, ModuleInterfaceCallable};
use super::namespace::{Namespace, NamespaceSymbol};
use super::protocol::ProtocolCallbackImpl;
use super::quoted_expander::{
    ExpandedScopeFragment, QuotedExpansionCtx, emit_internal_surface_error, emit_job_diagnostic,
    emit_surface_read_error, expand_item_macro_fragment, read_compiler_fragment_root,
};
use super::quoted_surface::{
    CompilerService, CompilerServiceForm, FunctionForm, MacroCallForm, ProtocolImplForm, ReservedSourceDefinition,
    ScopeForm, ScopeSurface, SurfaceSourceContext, read_module_body_surface, read_protocol_body_surface,
    read_protocol_impl_body_surface, reserved_source_definition,
};
use super::scheduler::FatalError;
use super::scope::ScopeSnapshot;
use super::source::{QuotedSourceError, QuotedSourceHeap, QuotedSourceMetadata};
use super::type_expr::{NominalKind, TypeDefBody, TypeExpr, parse_type_def_body, parse_type_expr};
use super::world::World;

type Outputs = Vec<FactKey>;
type Changed = Vec<FactKey>;

pub(crate) enum ScopePublication {
    Complete {
        namespace: Namespace,
        revision_floor: u64,
        reads: Vec<FactKey>,
        outputs: Outputs,
        changed: Changed,
        interface: ModuleInterface,
    },
    Blocked(JobEffects),
}

struct PendingType {
    name: TypeName,
    params: Vec<String>,
    body: TypeDefBody,
    span: Span,
}

#[derive(Clone, Copy)]
enum FragmentDiscovery {
    AlreadyIndexed,
    DiscoverNestedModules,
}

#[derive(Clone)]
struct FragmentPublicationContext {
    owner_module: ModuleId,
    export_public: bool,
    discovery: FragmentDiscovery,
}

impl FragmentPublicationContext {
    fn module_surface(current_module: ModuleId) -> Self {
        Self {
            owner_module: current_module,
            export_public: true,
            discovery: FragmentDiscovery::AlreadyIndexed,
        }
    }

    fn expanded_fragment(current_module: ModuleId) -> Self {
        Self {
            owner_module: current_module,
            export_public: true,
            discovery: FragmentDiscovery::DiscoverNestedModules,
        }
    }

    fn compiler_define(current_module: ModuleId) -> Self {
        Self {
            owner_module: current_module,
            export_public: true,
            discovery: FragmentDiscovery::DiscoverNestedModules,
        }
    }
}

struct ScopeSession<'world, 'tel> {
    world: &'world mut World<'tel>,
    code_id: CodeId,
    current_module: ModuleId,
    namespace: Namespace,
    local_callables: HashMap<(String, usize), NamespaceSymbol>,
    pending_types: Vec<PendingType>,
    required_remote_macros: HashSet<FunctionId>,
    reads: Vec<FactKey>,
    outputs: Outputs,
    changed: Changed,
    callables: Vec<ModuleInterfaceCallable>,
    revision_floor: u64,
}

impl<'world, 'tel> QuotedExpansionCtx<'tel> for ScopeSession<'world, 'tel> {
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

    fn lookup_current_module_macro(&mut self, _scope: ScopeSnapshot, name: &str, arity: usize) -> Option<FunctionId> {
        match self.local_callables.get(&(name.to_string(), arity)).cloned() {
            Some(NamespaceSymbol::Macro(function)) if self.world.function_module(function) == self.current_module => {
                Some(function)
            }
            _ => None,
        }
    }
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
    code_id: CodeId,
    module_id: ModuleId,
    namespace: Namespace,
    surface: &ScopeSurface,
) -> Result<ScopePublication, FatalError> {
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

    let mut outputs = Vec::new();
    let mut changed = Vec::new();
    let mut callables = Vec::new();
    for form in &surface.forms {
        let ScopeForm::Function(callback) = form else {
            continue;
        };
        let function = world.reference_function(module_id, callback.name.clone(), callback.arity);
        world.define_protocol_callback(function, module_id);
        let symbol = NamespaceSymbol::Function(function);
        scope = world.bind_namespace(scope, callback.name.clone(), symbol.clone());
        callables.push(ModuleInterfaceCallable {
            function,
            reference: world.function_ref(function).clone(),
            kind: InterfaceCallableKind::PublicFunction,
            variadic: false,
        });
    }

    let module_name = world
        .module_name(module_id)
        .ok_or_else(|| {
            emit_internal_surface_error(
                world,
                "protocol modules should have reverse names before publication".to_string(),
            )
        })?
        .to_string();
    let function = build_module_info_function(&callables, &module_name)
        .map_err(|error| emit_surface_read_error(world, "protocol module info synthesis failed", &error))?;
    let function_id = world.reference_function(module_id, function.name.clone(), function.arity);
    scope = world.bind_namespace(scope, function.name.clone(), NamespaceSymbol::Function(function_id));
    let publication = publish_function_source(world, code_id, module_id, module_id, scope, &function, true, Vec::new());
    outputs.push(publication.output.clone());
    if publication.changed {
        changed.push(publication.output);
    }
    if let Some(callable) = publication.callable {
        callables.push(callable);
    }

    outputs.push(FactKey::ProtocolDispatch(module_id));
    if world.refresh_protocol_dispatch(module_id) {
        changed.push(FactKey::ProtocolDispatch(module_id));
    }
    Ok(ScopePublication::Complete {
        namespace: scope,
        revision_floor: 0,
        reads: Vec::new(),
        outputs,
        changed,
        interface: ModuleInterface::new(callables),
    })
}

pub(crate) fn publish_protocol_impl_surface(
    world: &mut World<'_>,
    code_id: CodeId,
    impl_module: ModuleId,
    namespace: Namespace,
    source: &ProtocolImplSource,
) -> Result<ScopePublication, FatalError> {
    let mut session = ScopeSession::new(world, code_id, ScopeSnapshot::module(impl_module, namespace));
    session.publish_resolved_protocol_impl(impl_module, source)?;
    Ok(session.complete())
}

pub(crate) fn discover_modules(
    world: &mut World<'_>,
    code_id: CodeId,
    parent_module: ModuleId,
    surface: &ScopeSurface,
    ctx: &SurfaceSourceContext,
    outputs: &mut Outputs,
    changed: &mut Changed,
) -> Result<(), FatalError> {
    for form in &surface.forms {
        match form {
            ScopeForm::Module(module) => {
                let module_id = world.reference_child_module(parent_module, &module.name);
                let nested = read_module_body_surface(module, ctx)
                    .map_err(|error| emit_surface_read_error(world, "nested module body read failed", &error))?;
                let revision = world.index_module_body(
                    module_id,
                    code_id,
                    parent_module,
                    module.name.clone(),
                    module.source.clone(),
                    nested.clone(),
                );
                outputs.push(FactKey::ModuleIndexed(module_id));
                if revision {
                    changed.push(FactKey::ModuleIndexed(module_id));
                }
                discover_modules(world, code_id, module_id, &nested, ctx, outputs, changed)?;
            }
            ScopeForm::Protocol(protocol) => {
                let module_id = reference_declared_protocol_module(world, parent_module, &protocol.name);
                let protocol_surface = read_protocol_body_surface(protocol, ctx)
                    .map_err(|error| emit_surface_read_error(world, "quoted protocol body read failed", &error))?;
                let revision = world.index_protocol_module(
                    module_id,
                    code_id,
                    parent_module,
                    protocol.name.last_segment().to_string(),
                    protocol.source.clone(),
                    protocol_surface,
                );
                outputs.push(FactKey::ModuleIndexed(module_id));
                if revision {
                    changed.push(FactKey::ModuleIndexed(module_id));
                }
            }
            ScopeForm::MacroCall(macro_call) => {
                let Some(definition) = reserved_source_definition(&macro_call.source)
                    .map_err(|error| emit_surface_read_error(world, "raw discovery reservation failed", &error))?
                else {
                    continue;
                };
                let fragment =
                    read_compiler_fragment_root(world, code_id, &macro_call.source, "raw scope-definition fragment")?;
                let Some(fragment_form) = fragment.forms.first() else {
                    continue;
                };
                match (definition, fragment_form) {
                    (ReservedSourceDefinition::Module { .. }, ScopeForm::Module(module)) => {
                        let module_id = world.reference_child_module(parent_module, &module.name);
                        let nested = read_module_body_surface(module, ctx).map_err(|error| {
                            emit_surface_read_error(world, "nested module body read failed", &error)
                        })?;
                        let revision = world.index_module_body(
                            module_id,
                            code_id,
                            parent_module,
                            module.name.clone(),
                            module.source.clone(),
                            nested.clone(),
                        );
                        outputs.push(FactKey::ModuleIndexed(module_id));
                        if revision {
                            changed.push(FactKey::ModuleIndexed(module_id));
                        }
                        discover_modules(world, code_id, module_id, &nested, ctx, outputs, changed)?;
                    }
                    (ReservedSourceDefinition::Protocol { .. }, ScopeForm::Protocol(protocol)) => {
                        let module_id = reference_declared_protocol_module(world, parent_module, &protocol.name);
                        let protocol_surface = read_protocol_body_surface(protocol, ctx).map_err(|error| {
                            emit_surface_read_error(world, "quoted protocol body read failed", &error)
                        })?;
                        let revision = world.index_protocol_module(
                            module_id,
                            code_id,
                            parent_module,
                            protocol.name.last_segment().to_string(),
                            protocol.source.clone(),
                            protocol_surface,
                        );
                        outputs.push(FactKey::ModuleIndexed(module_id));
                        if revision {
                            changed.push(FactKey::ModuleIndexed(module_id));
                        }
                    }
                    _ => {}
                }
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
            local_callables: HashMap::new(),
            pending_types: Vec::new(),
            required_remote_macros: HashSet::new(),
            reads: Vec::new(),
            outputs: Vec::new(),
            changed: Vec::new(),
            callables: Vec::new(),
            revision_floor: 0,
        }
    }

    /// Walks one scope in source order and publishes every source-form fact it
    /// defines through this session's accumulated state.
    fn publish(mut self, surface: &ScopeSurface) -> Result<ScopePublication, FatalError> {
        let context = FragmentPublicationContext::module_surface(self.current_module);
        if let Some(blocked) = self.apply_surface_fragment(surface, &context)? {
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
                .callables
                .iter()
                .any(|callable| callable.matches_name_arity("__info__", 1))
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
        let function = build_module_info_function(&self.callables, &module_name).map_err(|error| {
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
        let context = FragmentPublicationContext::module_surface(self.current_module);
        let publication = self.define_source_function(
            self.current_module,
            self.current_module,
            self.namespace,
            &function,
            &context,
        )?;
        self.outputs.push(publication.output.clone());
        if publication.changed {
            self.changed.push(publication.output);
        }
        if let Some(callable) = publication.callable {
            self.callables.push(callable);
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
                | ScopeForm::ProtocolImpl(_) => {}
                ScopeForm::MacroCall(macro_call) => {
                    let Some(definition) = reserved_source_definition(&macro_call.source).map_err(|error| {
                        emit_internal_surface_error(self.world, format!("raw definition reservation failed: {error}"))
                    })?
                    else {
                        continue;
                    };
                    match definition {
                        ReservedSourceDefinition::Function { name, arity, is_macro } => {
                            let function_id = self.world.reference_function(self.current_module, name.clone(), arity);
                            let symbol = if is_macro {
                                NamespaceSymbol::Macro(function_id)
                            } else {
                                NamespaceSymbol::Function(function_id)
                            };
                            self.local_callables.insert((name.clone(), arity), symbol.clone());
                            self.namespace = self.world.bind_namespace(self.namespace, name, symbol);
                        }
                        ReservedSourceDefinition::Module { local_name } => {
                            let module_id = self.world.reference_child_module(self.current_module, &local_name);
                            self.namespace = self.world.bind_namespace(
                                self.namespace,
                                local_name,
                                NamespaceSymbol::Module(module_id),
                            );
                        }
                        ReservedSourceDefinition::Protocol { name } => {
                            let protocol_id =
                                reference_declared_protocol_module(self.world, self.current_module, &name);
                            self.namespace = self.world.bind_namespace(
                                self.namespace,
                                name.last_segment().to_string(),
                                NamespaceSymbol::Module(protocol_id),
                            );
                        }
                        // A `defimpl` binds no local name; its provider mapping is
                        // resolved at scope time where the namespace is available.
                        ReservedSourceDefinition::ProtocolImpl => {}
                    }
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

    fn apply_ordered_forms(
        &mut self,
        forms: &[ScopeForm],
        context: &FragmentPublicationContext,
    ) -> Result<Option<JobEffects>, FatalError> {
        for form in forms {
            if let Some(blocked) = self.apply_scope_form(form, context)? {
                return Ok(Some(self.blocked_effects(blocked)));
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
        let surface =
            read_compiler_fragment_root(self.world, self.code_id, &service.source, "Fz.Compiler.define source")?;
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
        let Some(form) = surface.forms.first() else {
            return Err(emit_job_diagnostic(
                self.world,
                Diagnostic::error(
                    codes::INTERNAL_POST_RESOLUTION_LEFTOVER,
                    "Fz.Compiler.define expected one fully expanded source definition",
                    service.span,
                ),
            ));
        };
        if matches!(form, ScopeForm::CompilerService(_) | ScopeForm::MacroCall(_)) {
            return Err(emit_job_diagnostic(
                self.world,
                Diagnostic::error(
                    codes::INTERNAL_POST_RESOLUTION_LEFTOVER,
                    "Fz.Compiler.define expected one fully expanded source definition",
                    service.span,
                ),
            ));
        }
        let context = FragmentPublicationContext::compiler_define(self.current_module);
        if let Some(blocked) = self.apply_surface_fragment(&surface, &context)? {
            return Err(emit_job_diagnostic(
                self.world,
                Diagnostic::error(
                    codes::INTERNAL_POST_RESOLUTION_LEFTOVER,
                    format!(
                        "Fz.Compiler.define cannot block while applying a source fragment: waits={:?}",
                        blocked.waits
                    ),
                    service.span,
                ),
            ));
        }
        Ok(())
    }

    fn define_source_function(
        &mut self,
        function_module: ModuleId,
        owner_module: ModuleId,
        namespace: Namespace,
        function: &FunctionForm,
        context: &FragmentPublicationContext,
    ) -> Result<FunctionPublication, FatalError> {
        Ok(publish_function_source(
            self.world,
            self.code_id,
            function_module,
            owner_module,
            namespace,
            function,
            context.export_public,
            required_remote_macro_list(&self.required_remote_macros),
        ))
    }

    fn apply_item_macro_call(&mut self, macro_call: &MacroCallForm) -> Result<Option<JobEffects>, FatalError> {
        let scope = ScopeSnapshot::module(self.current_module, self.namespace);
        let surface = match expand_item_macro_fragment(self, self.code_id, macro_call, scope)? {
            ExpandedScopeFragment::Complete(surface) => surface,
            ExpandedScopeFragment::Blocked(effects) => return Ok(Some(effects)),
        };
        let context = FragmentPublicationContext::expanded_fragment(self.current_module);
        self.apply_surface_fragment(&surface, &context)
    }

    fn apply_surface_fragment(
        &mut self,
        surface: &ScopeSurface,
        context: &FragmentPublicationContext,
    ) -> Result<Option<JobEffects>, FatalError> {
        if matches!(context.discovery, FragmentDiscovery::DiscoverNestedModules) {
            let ctx = SurfaceSourceContext::new(self.code_id);
            discover_modules(
                self.world,
                self.code_id,
                self.current_module,
                surface,
                &ctx,
                &mut self.outputs,
                &mut self.changed,
            )?;
        }
        self.reserve_types(&surface.attrs)?;
        self.reserve_local_forms(&surface.forms)?;
        self.note_pending_types();
        self.apply_ordered_forms(&surface.forms, context)
    }

    fn apply_scope_form(
        &mut self,
        form: &ScopeForm,
        context: &FragmentPublicationContext,
    ) -> Result<Option<JobEffects>, FatalError> {
        match form {
            ScopeForm::Alias(alias) => {
                let module_id = self.world.reference_module(alias.path.join("."));
                self.namespace = self.world.bind_namespace(
                    self.namespace,
                    alias.as_name.clone(),
                    NamespaceSymbol::Module(module_id),
                );
                Ok(None)
            }
            ScopeForm::Import(import) => self.apply_import(import),
            ScopeForm::Require(import) => self.apply_require(import),
            ScopeForm::CompilerService(service) => {
                self.apply_compiler_service(service)?;
                Ok(None)
            }
            ScopeForm::Function(function) => {
                let publication = self.define_source_function(
                    self.current_module,
                    context.owner_module,
                    self.namespace,
                    function,
                    context,
                )?;
                self.outputs.push(publication.output.clone());
                if publication.changed {
                    self.changed.push(publication.output);
                }
                if let Some(callable) = publication.callable {
                    self.callables.push(callable);
                }
                Ok(None)
            }
            ScopeForm::Module(module) => {
                let module_id = self.world.reference_child_module(self.current_module, &module.name);
                self.world.scope_module(module_id, self.namespace);
                let ctx = SurfaceSourceContext::new(self.code_id);
                let body = read_module_body_surface(module, &ctx)
                    .map_err(|error| emit_surface_read_error(self.world, "module body read failed", &error))?;
                self.register_protocol_impl_providers(module_id, &body, &ctx)?;
                Ok(None)
            }
            ScopeForm::Protocol(protocol) => {
                let protocol_id = reference_declared_protocol_module(self.world, self.current_module, &protocol.name);
                self.world.scope_module(protocol_id, self.namespace);
                Ok(None)
            }
            ScopeForm::ProtocolImpl(protocol_impl) => {
                let ctx = SurfaceSourceContext::new(self.code_id);
                self.register_protocol_impl(protocol_impl, &ctx)?;
                Ok(None)
            }
            ScopeForm::MacroCall(macro_call) => self.apply_item_macro_call(macro_call),
            ScopeForm::Struct(_) => Ok(None),
        }
    }

    /// Resolves the `defimpl`s declared in a scoped module's body to ids and
    /// records `module` as their provider. This is the one place the impl's
    /// protocol/target names touch the namespace — semantics reads only ids.
    /// It records the provider relation without defining the module: the
    /// `defimpl` is pulled (its callbacks registered) only when a concrete
    /// receiver later demands `DefineModule(provider)`.
    fn register_protocol_impl_providers(
        &mut self,
        module: ModuleId,
        body: &ScopeSurface,
        ctx: &SurfaceSourceContext,
    ) -> Result<(), FatalError> {
        for form in &body.forms {
            match form {
                ScopeForm::ProtocolImpl(impl_form) => {
                    self.register_protocol_impl(impl_form, ctx)?;
                }
                ScopeForm::Module(child) => {
                    let child_id = self.world.reference_child_module(module, &child.name);
                    let nested = read_module_body_surface(child, ctx).map_err(|error| {
                        emit_surface_read_error(self.world, "nested module body read failed", &error)
                    })?;
                    self.register_protocol_impl_providers(child_id, &nested, ctx)?;
                }
                ScopeForm::MacroCall(macro_call) => {
                    let Some(definition) = reserved_source_definition(&macro_call.source).map_err(|error| {
                        emit_surface_read_error(self.world, "impl discovery reservation failed", &error)
                    })?
                    else {
                        continue;
                    };
                    match definition {
                        ReservedSourceDefinition::ProtocolImpl => {
                            let fragment = read_compiler_fragment_root(
                                self.world,
                                self.code_id,
                                &macro_call.source,
                                "raw scope-definition fragment",
                            )?;
                            if let Some(ScopeForm::ProtocolImpl(impl_form)) = fragment.forms.first() {
                                let impl_form = impl_form.clone();
                                self.register_protocol_impl(&impl_form, ctx)?;
                            }
                        }
                        ReservedSourceDefinition::Module { .. } => {
                            let fragment = read_compiler_fragment_root(
                                self.world,
                                self.code_id,
                                &macro_call.source,
                                "raw scope-definition fragment",
                            )?;
                            if let Some(ScopeForm::Module(child)) = fragment.forms.first() {
                                let child_id = self.world.reference_child_module(module, &child.name);
                                let nested = read_module_body_surface(child, ctx).map_err(|error| {
                                    emit_surface_read_error(self.world, "nested module body read failed", &error)
                                })?;
                                self.register_protocol_impl_providers(child_id, &nested, ctx)?;
                            }
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn blocked_effects(&self, mut effects: JobEffects) -> JobEffects {
        effects.reads.extend(current_uses(self.reads.clone()));
        effects.outputs.extend(self.outputs.clone());
        effects.changed.extend(self.changed.clone());
        effects
    }

    fn apply_require(&mut self, import: &super::quoted_surface::ImportForm) -> Result<Option<JobEffects>, FatalError> {
        let required_module = self.resolve_import_module(import);
        let selected = if self.world.module_interface_revision(required_module).is_none() {
            if let Some(only) = import.only.as_deref() {
                only.iter()
                    .map(|(name, arity)| {
                        let function = self.world.reference_module_interface_callable(
                            required_module,
                            name.clone(),
                            *arity,
                            InterfaceCallableKind::Macro,
                            Some(self.interface_requester(import.span)),
                        );
                        ModuleInterfaceCallable {
                            function,
                            reference: self.world.function_ref(function).clone(),
                            kind: InterfaceCallableKind::Macro,
                            variadic: false,
                        }
                    })
                    .collect()
            } else {
                return Ok(Some(self.wait_for_module_interface(required_module)));
            }
        } else {
            let fact = FactKey::ModuleInterface(required_module);
            self.reads.push(fact);
            let interface = self.world.module_interface(required_module);
            self.select_required_macro_exports(import, interface.callables())?
        };
        self.record_required_remote_macros(&selected);
        Ok(None)
    }

    fn select_required_macro_exports(
        &mut self,
        import: &super::quoted_surface::ImportForm,
        callables: &[ModuleInterfaceCallable],
    ) -> Result<Vec<ModuleInterfaceCallable>, FatalError> {
        if let Some(only) = import.only.as_deref() {
            let mut selected = Vec::with_capacity(only.len());
            for (name, arity) in only {
                let Some(callable) = find_callable(callables, name, *arity) else {
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
                if !matches!(callable.kind, InterfaceCallableKind::Macro) {
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
                selected.push(callable.clone());
            }
            return Ok(selected);
        }

        let mut denied = HashSet::new();
        for (name, arity) in import.except.as_deref().unwrap_or(&[]) {
            let Some(callable) = find_callable(callables, name, *arity) else {
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
            if !matches!(callable.kind, InterfaceCallableKind::Macro) {
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
        Ok(callables
            .iter()
            .filter(|callable| matches!(callable.kind, InterfaceCallableKind::Macro))
            .filter(|callable| !denied.contains(&(callable.reference.name.as_str(), callable.reference.arity)))
            .cloned()
            .collect())
    }

    fn apply_import(&mut self, import: &super::quoted_surface::ImportForm) -> Result<Option<JobEffects>, FatalError> {
        let imported_module = self.resolve_import_module(import);
        let selected = if self.world.module_interface_revision(imported_module).is_none() {
            if let Some(only) = import.only.as_deref() {
                only.iter()
                    .map(|(name, arity)| {
                        let function = self.world.reference_module_interface_callable(
                            imported_module,
                            name.clone(),
                            *arity,
                            InterfaceCallableKind::Callable,
                            Some(self.interface_requester(import.span)),
                        );
                        ModuleInterfaceCallable {
                            function,
                            reference: self.world.function_ref(function).clone(),
                            kind: InterfaceCallableKind::Callable,
                            variadic: false,
                        }
                    })
                    .collect()
            } else {
                return Ok(Some(self.wait_for_module_interface(imported_module)));
            }
        } else {
            let fact = FactKey::ModuleInterface(imported_module);
            self.reads.push(fact);
            let interface = self.world.module_interface(imported_module);
            let callables = interface.callables();
            if let Some(only) = import.only.as_deref() {
                let mut selected = Vec::with_capacity(only.len());
                for (name, arity) in only {
                    let Some(callable) = find_callable(callables, name, *arity) else {
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
                    selected.push(callable.clone());
                }
                selected
            } else if let Some(except) = import.except.as_deref() {
                let mut deny = HashSet::new();
                for (name, arity) in except {
                    if find_callable(callables, name, *arity).is_none() {
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
                callables
                    .iter()
                    .filter(|callable| !deny.contains(&(callable.reference.name.as_str(), callable.reference.arity)))
                    .cloned()
                    .collect()
            } else {
                callables.to_vec()
            }
        };

        for export in &selected {
            self.namespace = bind_callable(self.world, self.namespace, export);
        }
        Ok(None)
    }

    fn resolve_import_module(&mut self, import: &super::quoted_surface::ImportForm) -> ModuleId {
        let path = ModuleName::from_segments(import.path.clone());
        self.world
            .resolve_module_name(self.current_module, self.namespace, &path)
            .expect("module resolution should always mint a module id for import/require paths")
    }

    fn interface_requester(&self, span: Span) -> InterfaceRequester {
        InterfaceRequester {
            code: self.code_id,
            module: self.current_module,
            span,
        }
    }

    fn wait_for_module_interface(&self, module: ModuleId) -> JobEffects {
        let follow_up = if self.world.module_has_source_state(module) || self.world.is_runtime_module(module) {
            Job::DefineModule(module)
        } else {
            Job::DefineModuleInterface(module)
        };
        JobEffects::wait_on_current(FactKey::ModuleInterface(module), [follow_up])
    }

    fn record_required_remote_macros(&mut self, callables: &[ModuleInterfaceCallable]) {
        for callable in callables {
            if callable.kind == InterfaceCallableKind::Macro {
                self.required_remote_macros.insert(callable.function);
            }
        }
    }
    /// Hoist a `defimpl Protocol, for: Target` to its own independently-
    /// demandable module `Protocol.Target` (Elixir's `__concat__`). Discovery
    /// records the impl as a `ProtocolImpl` module source resolved
    /// name-accurately at its lexical site; `DefineModule(Protocol.Target)`
    /// later publishes it without defining its lexical host. The provider index
    /// points at `Protocol.Target` so dispatch demands exactly the impl.
    fn register_protocol_impl(
        &mut self,
        form: &ProtocolImplForm,
        ctx: &SurfaceSourceContext,
    ) -> Result<(), FatalError> {
        let protocol = reference_impl_protocol_module(self.world, self.current_module, self.namespace, &form.protocol);
        let target = reference_impl_target_module(self.world, self.current_module, self.namespace, &form.target);
        let impl_module = reference_protocol_impl_module(self.world, protocol, target);
        let body = read_protocol_impl_body_surface(form, ctx).map_err(|error| {
            emit_internal_surface_error(self.world, format!("quoted protocol impl body read failed: {error}"))
        })?;
        let impl_name = self
            .world
            .module_name(impl_module)
            .expect("protocol impl modules should have reverse names")
            .to_string();
        // The hoisted impl module `Protocol.Target` is conceptually a child of the
        // protocol (Elixir's `Enumerable.List`), not of its lexical host: that is
        // the parent that reconstructs its qualified name and keeps it independent.
        let revision = self.world.index_protocol_impl_module(
            impl_module,
            self.code_id,
            protocol,
            last_segment(&impl_name).to_string(),
            form.source.clone(),
            ProtocolImplSource { protocol, target, body },
        );
        self.world.scope_module(impl_module, self.namespace);
        self.outputs.push(FactKey::ModuleIndexed(impl_module));
        if revision {
            self.changed.push(FactKey::ModuleIndexed(impl_module));
        }
        let grew = self
            .world
            .register_protocol_impl_provider(protocol, target, impl_module);
        self.outputs.push(FactKey::ProtocolImplProviders(protocol));
        if grew {
            self.changed.push(FactKey::ProtocolImplProviders(protocol));
        }
        Ok(())
    }

    /// Publish a hoisted impl module from its settled `ProtocolImplSource`: define
    /// each callback under the impl module, key them by the protocol's callback
    /// identity, and refresh the protocol's dispatch. This is the define-tier
    /// counterpart of `register_protocol_impl`, run by `DefineModule(Protocol.Target)`.
    fn publish_resolved_protocol_impl(
        &mut self,
        impl_module: ModuleId,
        source: &ProtocolImplSource,
    ) -> Result<(), FatalError> {
        let mut impl_scope = self.namespace;
        let mut functions = Vec::new();
        for form in &source.body.forms {
            let ScopeForm::Function(function) = form else {
                return Err(emit_job_diagnostic(
                    self.world,
                    Diagnostic::error(
                        codes::LOWER_UNSUPPORTED,
                        "compiler2 protocol implementations only support callback functions",
                        Span::DUMMY,
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

        // The hoisted impl is its own module: its callbacks are owned by the
        // impl module and resolve against the lexical namespace captured at the
        // defimpl site — never the lexical host, which must not be pulled.
        let context = FragmentPublicationContext {
            owner_module: impl_module,
            export_public: false,
            discovery: FragmentDiscovery::AlreadyIndexed,
        };
        let mut callbacks = HashMap::new();
        for function in functions {
            let publication = self.define_source_function(impl_module, impl_module, impl_scope, &function, &context)?;
            self.outputs.push(publication.output.clone());
            if publication.changed {
                self.changed.push(publication.output);
            }
            // Key by the protocol's callback identity — the same interned
            // FunctionId a callsite resolves to — not by (name, arity).
            let callback = self
                .world
                .reference_function(source.protocol, function.name.clone(), function.arity);
            callbacks.insert(
                callback,
                ProtocolCallbackImpl {
                    function: publication.function,
                    owner_module: impl_module,
                },
            );
            self.callables.push(ModuleInterfaceCallable {
                function: publication.function,
                reference: self.world.function_ref(publication.function).clone(),
                kind: InterfaceCallableKind::PublicFunction,
                variadic: false,
            });
        }
        self.world
            .define_protocol_impl(source.protocol, source.target, callbacks);
        self.outputs.push(FactKey::ProtocolDispatch(source.protocol));
        if self.world.refresh_protocol_dispatch(source.protocol) {
            self.changed.push(FactKey::ProtocolDispatch(source.protocol));
        }
        Ok(())
    }

    fn complete(self) -> ScopePublication {
        ScopePublication::Complete {
            namespace: self.namespace,
            revision_floor: self.revision_floor,
            reads: self.reads,
            outputs: self.outputs,
            changed: self.changed,
            interface: ModuleInterface::new(self.callables),
        }
    }
}

fn build_module_info_function(
    callables: &[ModuleInterfaceCallable],
    module_name: &str,
) -> Result<FunctionForm, QuotedSourceError> {
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let meta = QuotedSourceMetadata::default();
    let functions = module_info_pairs(&builder, callables, |kind| {
        matches!(kind, InterfaceCallableKind::PublicFunction)
    })?;
    let macros = module_info_pairs(&builder, callables, |kind| matches!(kind, InterfaceCallableKind::Macro))?;
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
    callables: &[ModuleInterfaceCallable],
    keep: impl Fn(InterfaceCallableKind) -> bool,
) -> Result<AnyValueRef, QuotedSourceError> {
    let pairs = callables
        .iter()
        .filter(|callable| keep(callable.kind))
        .map(|callable| {
            builder.tuple(&[
                builder.atom(&callable.reference.name),
                builder.int(callable.reference.arity as i64),
            ])
        })
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

fn required_remote_macro_list(required_remote_macros: &HashSet<FunctionId>) -> Vec<FunctionId> {
    let mut macros = required_remote_macros.iter().copied().collect::<Vec<_>>();
    macros.sort_by_key(|function| function.as_u32());
    macros
}

struct FunctionPublication {
    function: FunctionId,
    output: FactKey,
    changed: bool,
    callable: Option<ModuleInterfaceCallable>,
}

fn publish_function_source(
    world: &mut World<'_>,
    code_id: CodeId,
    function_module: ModuleId,
    owner_module: ModuleId,
    namespace: Namespace,
    function: &FunctionForm,
    export_public: bool,
    required_remote_macros: Vec<FunctionId>,
) -> FunctionPublication {
    let function_id = world.reference_function(function_module, function.name.clone(), function.arity);
    let revision = world.note_function_source(
        function_id,
        FunctionSource {
            code: code_id,
            owner_module,
            namespace,
            capture_params: Vec::new(),
            required_remote_macros,
            variadic: function.variadic,
            source: function.source.clone(),
        },
    );

    let callable = (export_public && !function.is_private).then(|| ModuleInterfaceCallable {
        function: function_id,
        reference: world.function_ref(function_id).clone(),
        kind: if function.is_macro {
            InterfaceCallableKind::Macro
        } else {
            InterfaceCallableKind::PublicFunction
        },
        variadic: function.variadic,
    });
    let source = world
        .function_source(function_id)
        .expect("function source should exist immediately after compiler service publication");
    emit_compiler_service_define(world, function_id, &source, revision);
    FunctionPublication {
        function: function_id,
        output: FactKey::FunctionSource(function_id),
        changed: revision,
        callable,
    }
}

fn emit_compiler_service_define(world: &World<'_>, function: FunctionId, source: &FunctionSource, changed: bool) {
    let function_ref = world.function_ref(function);
    world.tel().execute(
        &["fz", "compiler2", "compiler_service", "define"],
        &measurements! {
            code_id: source.code.as_u32() as u64,
            module_id: function_ref.module.as_u32() as u64,
            owner_module_id: source.owner_module.as_u32() as u64,
            function_id: function.as_u32() as u64,
            changed: changed as u64,
            namespace: source.namespace.as_u32() as u64,
            source_heap_id: source.source.key().heap_id as u64,
            source_root_ref: source.source.root().raw_word(),
        },
        &metadata! {
            origin: "fz_compiler",
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

fn find_callable<'a>(
    callables: &'a [ModuleInterfaceCallable],
    name: &str,
    arity: usize,
) -> Option<&'a ModuleInterfaceCallable> {
    callables
        .iter()
        .find(|callable| callable.matches_name_arity(name, arity))
}

fn bind_callable(world: &mut World<'_>, scope: Namespace, callable: &ModuleInterfaceCallable) -> Namespace {
    world.bind_namespace(scope, callable.reference.name.clone(), callable.namespace_symbol())
}

fn reference_declared_protocol_module(world: &mut World<'_>, current_module: ModuleId, name: &ModuleName) -> ModuleId {
    world.reference_module(qualified_child_module_name(world, current_module, name))
}

fn reference_impl_protocol_module(
    world: &mut World<'_>,
    current_module: ModuleId,
    head: Namespace,
    name: &ModuleName,
) -> ModuleId {
    world
        .resolve_module_name(current_module, head, name)
        .expect("module resolution should always mint a module id for defimpl protocol names")
}

fn reference_impl_target_module(
    world: &mut World<'_>,
    current_module: ModuleId,
    head: Namespace,
    name: &ModuleName,
) -> ModuleId {
    world
        .resolve_module_name(current_module, head, name)
        .expect("module resolution should always mint a module id for defimpl target names")
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

fn last_segment(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
}
