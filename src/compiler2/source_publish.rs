//! Compiler-owned publication for quoted source forms.
//!
//! Source jobs schedule work. This module owns the source-form rules that turn
//! quoted surface readers into namespace mutations and compiler2 fact outputs.

use crate::fast_hash::{HashMap, HashSet};
use std::collections::hash_map::Entry;
use std::rc::Rc;

use fz_runtime::any_value::AnyValueRef;

use crate::ast::{Attribute, SpecDecl, TypeExprBody, Var};
use crate::diag::{Diagnostic, codes};
use crate::function_surface::FunctionSurface;
use crate::modules::identity::ModuleName;
use crate::source::{SourceMap, Span};
use crate::telemetry::TelemetryExt as _;

use super::code::SourceOwner;
use super::definition_time::{self, Evaluated, Evaluation};
use super::drive::{DerivationKey, FactKey, JobDerivation, JobEffects, current_uses, emit_job_diagnostic};
use super::identity::{
    DeclaredCallableKind, FunctionBody, FunctionId, FunctionSource, ModuleId, NotedTypeDecl, ProtocolImplSource,
    TypeName,
};
use super::module_interface::{InterfaceCallableKind, InterfaceRequester, ModuleInterface, ModuleInterfaceCallable};
use super::namespace::{Namespace, NamespaceSymbol};
use super::protocol::ProtocolCallbackImpl;
use super::quoted_expander::{
    ExpandedScopeFragment, ExpandedValue, ExpansionContext, QuotedExpansionCtx, emit_internal_surface_error,
    emit_surface_read_error, expand_item_macro_fragment, item_macro_expanded_to_a_non_definition,
    item_macro_not_defmacro, read_compiler_fragment_root, read_expanded_items,
};
use super::quoted_surface::{
    AttributeForm, CompilerService, CompilerServiceForm, FragmentForm, FunctionForm, MacroCallForm, OverridableForm,
    ProtocolImplForm, ReservedSourceDefinition, ScopeForm, ScopeSurface, StatementForm, StructFields, StructForm,
    attribute_symbol, defines_a_function, function_doc_attributes, is_documentation_attribute, is_documentation_value,
    is_written_literal, read_module_body_surface, read_protocol_body_surface, read_protocol_impl_body_surface,
    read_struct_fields, reserved_source_definition,
};
use super::scope::ScopeSnapshot;
use super::source::{QuotedSourceError, QuotedSourceHeap, QuotedSourceMetadata, QuotedSourceRoot};
use super::structdef::StructDef;
use super::type_expr::{NominalKind, TypeDefBody, TypeExpr, parse_type_def_body, parse_type_expr};
use super::world::{ProtocolCallbackSurface, World};
use fz_engine::FatalError;

type Outputs = Vec<FactKey>;
type Changed = Vec<FactKey>;
use super::drive::ProductAddress;
use super::pull::ProductSessions;

pub(crate) enum ScopePublication {
    Complete {
        namespace: Namespace,
        revision_floor: u64,
        reads: Vec<FactKey>,
        product_reads: Vec<ProductAddress>,
        /// One answer per function the walk reached, each standing on the
        /// ground above it.
        derivations: Vec<JobDerivation>,
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
    /// Whether a function form of this fragment is a definition the walk has
    /// not counted yet. The fragment `Fz.Compiler.define` hands back is the
    /// `def` the walk already reserved.
    functions_are_new: bool,
    origin: ClauseOrigin,
}

/// Who wrote the clauses of a fragment. The module body's own `def`s are
/// written, and a function of them is defined once: a second written
/// definition of it is refused. What a macro expands to, or an unquote
/// fragment evaluates to, is expanded, and its clauses join the function of
/// the same name and arity the module already has, as Elixir's do.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ClauseOrigin {
    Written,
    Expanded,
}

impl FragmentPublicationContext {
    fn module_surface(current_module: ModuleId) -> Self {
        Self {
            owner_module: current_module,
            export_public: true,
            discovery: FragmentDiscovery::AlreadyIndexed,
            functions_are_new: true,
            origin: ClauseOrigin::Written,
        }
    }

    fn expanded_fragment(current_module: ModuleId) -> Self {
        Self {
            owner_module: current_module,
            export_public: true,
            discovery: FragmentDiscovery::DiscoverNestedModules,
            functions_are_new: true,
            origin: ClauseOrigin::Expanded,
        }
    }

    /// The definition `Fz.Compiler.define` hands back, which the walk reserved
    /// when it reached the call that made it, written or expanded as that
    /// call was.
    fn compiler_define(current_module: ModuleId, origin: ClauseOrigin) -> Self {
        Self {
            owner_module: current_module,
            export_public: true,
            discovery: FragmentDiscovery::DiscoverNestedModules,
            functions_are_new: false,
            origin,
        }
    }
}

/// What the walk knows about one function of the module it is walking.
struct LocalCallable {
    symbol: NamespaceSymbol,
    /// The definitions of this function the walk has reserved and has yet to
    /// reach.
    to_come: usize,
    standing: Standing,
    /// How many of this function's definitions a later one has replaced.
    replaced: usize,
    /// The sources of replaced definitions published since this function's
    /// last answer. The definition that stands is the answer they belong to.
    superseded: Vec<FunctionPublication>,
}

/// Where a function stands as the walk reaches each of its forms.
enum Standing {
    NotDefined,
    Defined(ReachedDefinition),
    /// Defined, and marked by `defoverridable`: the next definition replaces
    /// this one.
    Overridable(ReachedDefinition),
}

impl Standing {
    /// Marks a defined function overridable, and answers whether it was
    /// defined.
    fn mark_overridable(&mut self) -> bool {
        match std::mem::replace(self, Standing::NotDefined) {
            Standing::Defined(definition) => {
                *self = Standing::Overridable(definition);
                true
            }
            unmarked => {
                *self = unmarked;
                false
            }
        }
    }
}

/// A definition the walk has reached, kept with the scope it was reached in
/// until the walk knows whether it stands or a later definition replaces it.
/// A replaced definition is still the one its replacement's `super` calls.
struct ReachedDefinition {
    function: FunctionForm,
    namespace: Namespace,
    owner_module: ModuleId,
    origin: ClauseOrigin,
}

impl ReachedDefinition {
    /// Whether `later`, reached from `origin`, adds clauses to this function:
    /// it is the same kind of definition, and one of the two is expanded.
    fn takes_clauses_of(&self, later: &FunctionForm, origin: ClauseOrigin) -> bool {
        let same_kind = self.function.is_macro == later.is_macro && self.function.is_private == later.is_private;
        same_kind && (self.origin == ClauseOrigin::Expanded || origin == ClauseOrigin::Expanded)
    }
}

/// A definition the walk has reached and the scope it stands in, ready to
/// publish.
struct ReachedFunction {
    function: FunctionForm,
    namespace: Namespace,
}

struct ScopeSession<'world, 'tel, T: crate::telemetry::Telemetry> {
    world: &'world mut World,
    telemetry: &'tel T,
    products: Option<&'world ProductSessions>,
    product_reads: Vec<ProductAddress>,
    source_owner: SourceOwner,
    current_module: ModuleId,
    namespace: Namespace,
    local_callables: HashMap<(String, usize), LocalCallable>,
    pending_types: Vec<PendingType>,
    reads: Vec<FactKey>,
    /// One answer per function the walk has reached, each carrying the ground
    /// that stood above it at that point.
    derivations: Vec<JobDerivation>,
    outputs: Outputs,
    changed: Changed,
    callables: Vec<ModuleInterfaceCallable>,
    revision_floor: u64,
    struct_form_seen: bool,
    /// How many definition-time expressions this walk has evaluated.
    definition_time_evaluations: usize,
    /// The expressions a submitted file's top level holds, in walk order. They
    /// become the file's `main/0` once every definition is published.
    statements: Vec<StatementForm>,
    /// How many macro invocations this session has visited, whether or not
    /// an expansion hit the memoization cache (`next_expansion_number` on
    /// `QuotedExpansionCtx`). Local to this job attempt, reset with it.
    expansions_visited: i64,
    /// Where the expansion in progress stands; see
    /// `QuotedExpansionCtx::expansion_context`.
    expansion_context: ExpansionContext,
}

impl<'world, 'tel, T: crate::telemetry::Telemetry> QuotedExpansionCtx for ScopeSession<'world, 'tel, T> {
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

    fn expanding_function(&self) -> Option<FunctionId> {
        None
    }

    fn note_read(&mut self, fact: FactKey) {
        self.reads.push(fact);
    }

    fn products(&self) -> Option<&ProductSessions> {
        self.products
    }
    fn note_product_read(&mut self, product: ProductAddress) {
        self.product_reads.push(product);
    }

    fn lookup_current_module_macro(&mut self, _scope: ScopeSnapshot, name: &str, arity: usize) -> Option<FunctionId> {
        match self.local_callables.get(&(name.to_string(), arity))?.symbol {
            NamespaceSymbol::Macro(function) if self.world.function_module(function) == self.current_module => {
                Some(function)
            }
            _ => None,
        }
    }

    fn expansion_context(&mut self) -> &mut ExpansionContext {
        &mut self.expansion_context
    }

    fn next_expansion_number(&mut self) -> i64 {
        let number = self.expansions_visited;
        self.expansions_visited = self
            .expansions_visited
            .checked_add(1)
            .expect("expansion number space exhausted");
        number
    }
}

pub(crate) fn publish_scope(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    products: Option<&ProductSessions>,
    source_owner: SourceOwner,
    current_scope: ScopeSnapshot,
    surface: &ScopeSurface,
) -> Result<ScopePublication, FatalError> {
    ScopeSession::new(world, tel, products, source_owner, current_scope).publish(surface)
}

pub(crate) fn publish_protocol_surface(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    source_owner: SourceOwner,
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
    note_protocol_domain_type(world, tel, protocol_t, scope, Vec::new());
    note_protocol_domain_type(
        world,
        tel,
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
        super::drive::ExecutionContext::new(world, tel).define_protocol_callback(&function, &module_id);
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
                tel,
                "protocol modules should have reverse names before publication".to_string(),
            )
        })?
        .to_string();
    let function = build_module_info_function(&callables, &module_name)
        .map_err(|error| emit_surface_read_error(tel, "protocol module info synthesis failed", &error))?;
    let function_id = world.reference_function(module_id, function.name.clone(), function.arity);
    scope = world.bind_namespace(scope, function.name.clone(), NamespaceSymbol::Function(function_id));
    let publication = publish_function_source(world, tel, source_owner, module_id, module_id, scope, &function, true);
    outputs.push(FactKey::FunctionSource(publication.function));
    if publication.source_changed {
        changed.push(FactKey::FunctionSource(publication.function));
    }
    if let Some(callable) = publication.callable {
        callables.push(callable);
    }

    outputs.push(FactKey::ProtocolDispatch(module_id));
    if super::drive::ExecutionContext::new(world, tel).refresh_protocol_dispatch(module_id) {
        changed.push(FactKey::ProtocolDispatch(module_id));
    }
    Ok(ScopePublication::Complete {
        namespace: scope,
        revision_floor: 0,
        reads: Vec::new(),
        product_reads: Vec::new(),
        derivations: Vec::new(),
        outputs,
        changed,
        interface: ModuleInterface::new(callables),
    })
}

pub(crate) fn publish_protocol_impl_surface(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    products: Option<&ProductSessions>,
    source_owner: SourceOwner,
    impl_module: ModuleId,
    namespace: Namespace,
    source: &ProtocolImplSource,
) -> Result<ScopePublication, FatalError> {
    let mut session = ScopeSession::new(
        world,
        tel,
        products,
        source_owner,
        ScopeSnapshot::module(impl_module, namespace),
    );
    session.publish_resolved_protocol_impl(impl_module, source)?;
    Ok(session.complete())
}

/// Publishes that `module` is indexed. A module with source is one a value
/// can name, so the set of those is published beside it.
fn publish_module_indexed(
    world: &mut World,
    module: ModuleId,
    revision: bool,
    outputs: &mut Outputs,
    changed: &mut Changed,
) {
    outputs.push(FactKey::ModuleIndexed(module));
    if revision {
        changed.push(FactKey::ModuleIndexed(module));
    }
    outputs.push(FactKey::NameableModules);
    if world.note_nameable_module(module) {
        changed.push(FactKey::NameableModules);
    }
}

/// Warns at each clause the surface wrote apart from the clauses of its own
/// name and arity, as Elixir does when it stores the definition.
fn warn_ungrouped_clauses(world: &mut World, tel: &impl crate::telemetry::Telemetry, surface: &ScopeSurface) {
    let source_map = world.source_map();
    let diagnostics: Vec<_> = {
        let source_map = source_map.borrow();
        surface
            .ungrouped
            .iter()
            .map(|clause| {
                let first = source_map.locate(clause.first_span);
                let file = source_map.name(first.source_version).unwrap_or("<unnamed>");
                super::source_diagnostics::ungrouped_clause_diagnostic(clause, file, first.line)
            })
            .collect()
    };
    for diagnostic in diagnostics {
        super::drive::ExecutionContext::new(world, tel).emit_warning_once(diagnostic);
    }
}

pub(crate) fn discover_modules(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    source_owner: SourceOwner,
    parent_module: ModuleId,
    surface: &ScopeSurface,
    outputs: &mut Outputs,
    changed: &mut Changed,
) -> Result<(), FatalError> {
    warn_ungrouped_clauses(world, tel, surface);
    for form in &surface.forms {
        match form {
            ScopeForm::Module(module) => {
                let module_id = reference_declared_module(world, parent_module, &module.name);
                let source_map = world.source_map();
                let nested = read_module_body_surface(module, &source_map.borrow())
                    .map_err(|error| emit_surface_read_error(tel, "nested module body read failed", &error))?;
                let revision = world.index_module_body(
                    module_id,
                    source_owner,
                    parent_module,
                    module.source.clone(),
                    module.span,
                    nested.clone(),
                );
                publish_module_indexed(world, module_id, revision, outputs, changed);
                discover_modules(world, tel, source_owner, module_id, &nested, outputs, changed)?;
            }
            ScopeForm::Protocol(protocol) => {
                let module_id = reference_declared_module(world, parent_module, &protocol.name);
                let source_map = world.source_map();
                let protocol_surface = read_protocol_body_surface(protocol, &source_map.borrow())
                    .map_err(|error| emit_surface_read_error(tel, "quoted protocol body read failed", &error))?;
                let revision = world.index_protocol_module(
                    module_id,
                    source_owner,
                    parent_module,
                    protocol.source.clone(),
                    protocol.span,
                    protocol_surface,
                );
                publish_module_indexed(world, module_id, revision, outputs, changed);
            }
            ScopeForm::MacroCall(macro_call) => {
                let source_map = world.source_map();
                let Some(definition) = reserved_source_definition(&macro_call.source, &source_map.borrow())
                    .map_err(|error| emit_surface_read_error(tel, "raw discovery reservation failed", &error))?
                else {
                    continue;
                };
                let fragment = read_compiler_fragment_root(
                    tel,
                    &macro_call.source,
                    "raw scope-definition fragment",
                    &source_map.borrow(),
                )?;
                let Some(fragment_form) = fragment.forms.first() else {
                    continue;
                };
                match (definition, fragment_form) {
                    (ReservedSourceDefinition::Module { .. }, ScopeForm::Module(module)) => {
                        let module_id = reference_declared_module(world, parent_module, &module.name);
                        let source_map = world.source_map();
                        let nested = read_module_body_surface(module, &source_map.borrow())
                            .map_err(|error| emit_surface_read_error(tel, "nested module body read failed", &error))?;
                        let revision = world.index_module_body(
                            module_id,
                            source_owner,
                            parent_module,
                            module.source.clone(),
                            module.span,
                            nested.clone(),
                        );
                        publish_module_indexed(world, module_id, revision, outputs, changed);
                        discover_modules(world, tel, source_owner, module_id, &nested, outputs, changed)?;
                    }
                    (ReservedSourceDefinition::Protocol { .. }, ScopeForm::Protocol(protocol)) => {
                        let module_id = reference_declared_module(world, parent_module, &protocol.name);
                        let protocol_surface =
                            read_protocol_body_surface(protocol, &source_map.borrow()).map_err(|error| {
                                emit_surface_read_error(tel, "quoted protocol body read failed", &error)
                            })?;
                        let revision = world.index_protocol_module(
                            module_id,
                            source_owner,
                            parent_module,
                            protocol.source.clone(),
                            protocol.span,
                            protocol_surface,
                        );
                        publish_module_indexed(world, module_id, revision, outputs, changed);
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
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    function: FunctionId,
    surface: &FunctionSurface,
) -> Result<(), FatalError> {
    let (namespace, owner, module) = {
        let source = world
            .function_source(function)
            .expect("function type refs should only be recorded after function source is noted");
        (source.namespace, source.owner, source.owner_module)
    };
    let mut refs = TypeReferences::default();
    for attr in &surface.attrs {
        if let Attribute::Spec(spec) = attr {
            collect_spec_references(world, tel, namespace, spec, owner, module, &mut refs)?;
        }
    }
    if let Some(extern_spec) = surface.extern_contract_decl() {
        collect_spec_references(world, tel, namespace, &extern_spec, owner, module, &mut refs)?;
    }
    for clause in &surface.clauses {
        for annotation in clause.param_annotations.iter().flatten() {
            collect_body_references(world, tel, namespace, annotation, owner, module, &mut refs)?;
        }
    }
    super::drive::ExecutionContext::new(world, tel).record_function_type_refs(&function, refs.types);
    world.record_function_type_struct_refs(function, refs.structs);
    Ok(())
}

fn type_expr_body_span(body: &TypeExprBody) -> Span {
    body.0.iter().map(|token| token.span).fold(Span::DUMMY, Span::merge)
}

impl<'world, 'tel, T: crate::telemetry::Telemetry> ScopeSession<'world, 'tel, T> {
    fn new(
        world: &'world mut World,
        telemetry: &'tel T,
        products: Option<&'world ProductSessions>,
        source_owner: SourceOwner,
        current_scope: ScopeSnapshot,
    ) -> Self {
        Self {
            world,
            telemetry,
            products,
            product_reads: Vec::new(),
            source_owner,
            current_module: current_scope.module_id(),
            namespace: current_scope.namespace(),
            local_callables: HashMap::default(),
            pending_types: Vec::new(),
            reads: Vec::new(),
            derivations: Vec::new(),
            outputs: Vec::new(),
            changed: Vec::new(),
            callables: Vec::new(),
            revision_floor: 0,
            struct_form_seen: false,
            definition_time_evaluations: 0,
            statements: Vec::new(),
            expansions_visited: 0,
            expansion_context: ExpansionContext::Expression,
        }
    }

    /// Walks one scope in source order and publishes every source-form fact it
    /// defines through this session's accumulated state.
    fn publish(mut self, surface: &ScopeSurface) -> Result<ScopePublication, FatalError> {
        let context = FragmentPublicationContext::module_surface(self.current_module);
        if let Some(blocked) = self.apply_surface_fragment(surface, &context)? {
            return Ok(ScopePublication::Blocked(blocked));
        }
        self.publish_script_main()?;
        self.publish_program_entry()?;
        if let Some(blocked) = self.publish_module_info()? {
            return Ok(ScopePublication::Blocked(self.blocked_effects(blocked)));
        }
        Ok(self.complete())
    }

    /// A submitted file's top level is a script when it holds expressions:
    /// they are the body of the program's `main/0`.
    fn is_script_scope(&self) -> bool {
        self.current_module.is_global() && !self.world.is_prelude(self.source_owner)
    }

    fn publish_script_main(&mut self) -> Result<(), FatalError> {
        let (Some(first), Some(last)) = (self.statements.first(), self.statements.last()) else {
            return Ok(());
        };
        let span = first.span.merge(last.span);
        if let Some(main) = self.local_callables.get(&("main".to_string(), 0)) {
            return Err(self.script_and_main_diagnostic(first.span, main.symbol.clone()));
        }
        let function = build_script_main(&self.statements, span).map_err(|error| {
            emit_internal_surface_error(self.telemetry, format!("script main synthesis failed: {error}"))
        })?;
        let context = FragmentPublicationContext::module_surface(self.current_module);
        let publication = self.define_source_function(
            self.current_module,
            self.current_module,
            self.namespace,
            &function,
            &context,
        )?;
        if let Some(callable) = publication.callable {
            self.callables.push(callable);
        }
        Ok(())
    }

    /// A submitted file that has a `main/0`, written or made from its top-level
    /// expressions, also gets the entry its first process starts in.
    fn publish_program_entry(&mut self) -> Result<(), FatalError> {
        let has_main = self.local_callables.contains_key(&("main".to_string(), 0))
            || self
                .callables
                .iter()
                .any(|callable| callable.matches_name_arity("main", 0));
        if !self.is_script_scope() || !has_main {
            return Ok(());
        }
        let function = build_program_entry().map_err(|error| {
            emit_internal_surface_error(self.telemetry, format!("program entry synthesis failed: {error}"))
        })?;
        let main = self
            .world
            .reference_function(self.current_module, "main".to_string(), 0);
        let namespace = self
            .world
            .bind_namespace(self.namespace, "main".to_string(), NamespaceSymbol::Function(main));
        let context = FragmentPublicationContext::module_surface(self.current_module);
        let publication =
            self.define_source_function(self.current_module, self.current_module, namespace, &function, &context)?;
        if let Some(callable) = publication.callable {
            self.callables.push(callable);
        }
        Ok(())
    }

    fn script_and_main_diagnostic(&self, first_statement: Span, main: NamespaceSymbol) -> FatalError {
        let mut diagnostic = Diagnostic::error(
            codes::RESOLVE_SCRIPT_AND_MAIN,
            "a file with top-level expressions cannot also define `main/0`",
            first_statement,
        );
        if let Some(span) = self.definition_span(&main) {
            diagnostic = diagnostic.with_secondary(span, "the file's own `main/0` is defined here");
        }
        emit_job_diagnostic(self.telemetry, diagnostic)
    }

    fn definition_span(&self, symbol: &NamespaceSymbol) -> Option<Span> {
        let (NamespaceSymbol::Function(function)
        | NamespaceSymbol::Macro(function)
        | NamespaceSymbol::Callable(function)) = symbol
        else {
            return None;
        };
        let source = self.world.function_source(*function)?;
        let source_map = self.world.source_map();
        first_clause_span(source.declared_root()?, &source_map.borrow())
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
                    self.telemetry,
                    "module info synthesis expected a named current module".to_string(),
                )
            })?
            .to_string();
        let function = build_module_info_function(&self.callables, &module_name).map_err(|error| {
            emit_internal_surface_error(self.telemetry, format!("module info source synthesis failed: {error}"))
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
                    self.telemetry,
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

    /// Binds the name of a definition the walk will reach, and counts the
    /// definition unless the walk counted it already.
    fn reserve_local_callable(&mut self, name: &str, arity: usize, is_macro: bool, is_new: bool) {
        let callable = match self.local_callables.entry((name.to_string(), arity)) {
            Entry::Occupied(callable) => callable.into_mut(),
            Entry::Vacant(vacant) => {
                let kind = declared_callable_kind(is_macro);
                let function =
                    self.world
                        .reference_declared_callable(self.current_module, name.to_string(), arity, kind);
                vacant.insert(LocalCallable {
                    symbol: kind.namespace_symbol(function),
                    to_come: 0,
                    standing: Standing::NotDefined,
                    replaced: 0,
                    superseded: Vec::new(),
                })
            }
        };
        if is_new {
            callable.to_come += 1;
        }
        // Bound wherever the name does not already reach this function, so the
        // module's own function stands in front of a name an `import` above it
        // bound.
        if self.world.lookup_namespace(self.namespace, name).as_ref() != Some(&callable.symbol) {
            let symbol = callable.symbol.clone();
            self.namespace = self.world.bind_namespace(self.namespace, name.to_string(), symbol);
        }
    }

    fn reserve_local_forms(
        &mut self,
        forms: &[ScopeForm],
        context: &FragmentPublicationContext,
    ) -> Result<(), FatalError> {
        for form in forms {
            match form {
                ScopeForm::Function(function) => {
                    self.reserve_local_callable(
                        &function.name,
                        function.arity,
                        function.is_macro,
                        context.functions_are_new,
                    );
                }
                ScopeForm::Module(module) => {
                    let module_id = reference_declared_module(self.world, self.current_module, &module.name);
                    self.namespace =
                        bind_declared_module(self.world, self.namespace, self.current_module, &module.name, module_id);
                }
                ScopeForm::Protocol(protocol) => {
                    let protocol_id = reference_declared_module(self.world, self.current_module, &protocol.name);
                    self.namespace = bind_declared_module(
                        self.world,
                        self.namespace,
                        self.current_module,
                        &protocol.name,
                        protocol_id,
                    );
                }
                // A `Fz.Compiler.define` call written into a fragment is a
                // definition the walk has not met as a `def`.
                ScopeForm::CompilerService(service) if context.functions_are_new => {
                    let source_map = self.world.source_map();
                    let definition =
                        reserved_source_definition(&service.source, &source_map.borrow()).map_err(|error| {
                            emit_internal_surface_error(
                                self.telemetry,
                                format!("compiler service reservation failed: {error}"),
                            )
                        })?;
                    if let Some(ReservedSourceDefinition::Function { name, arity, is_macro }) = definition {
                        self.reserve_local_callable(&name, arity, is_macro, true);
                    }
                }
                // A `defstruct` defines the module's `__struct__/0`.
                ScopeForm::Struct(_) => {
                    self.reserve_local_callable(STRUCT_FUNCTION, 0, false, true);
                }
                // A fragment's head names what it defines when its name is
                // written; a name that computes is bound once it has run.
                ScopeForm::Fragment(fragment) => {
                    if let Some(head) = &fragment.head {
                        self.reserve_local_callable(&head.name, head.arity, head.is_macro, true);
                    }
                }
                ScopeForm::Alias(_)
                | ScopeForm::Import(_)
                | ScopeForm::Require(_)
                | ScopeForm::CompilerService(_)
                | ScopeForm::Overridable(_)
                | ScopeForm::Statement(_)
                | ScopeForm::ProtocolImpl(_)
                | ScopeForm::Attribute(_) => {}
                ScopeForm::MacroCall(macro_call) => {
                    let source_map = self.world.source_map();
                    let Some(definition) = reserved_source_definition(&macro_call.source, &source_map.borrow())
                        .map_err(|error| {
                            emit_internal_surface_error(
                                self.telemetry,
                                format!("raw definition reservation failed: {error}"),
                            )
                        })?
                    else {
                        continue;
                    };
                    match definition {
                        ReservedSourceDefinition::Function { name, arity, is_macro } => {
                            self.reserve_local_callable(&name, arity, is_macro, true);
                        }
                        ReservedSourceDefinition::Module { name } => {
                            let module_id = reference_declared_module(self.world, self.current_module, &name);
                            self.namespace =
                                bind_declared_module(self.world, self.namespace, self.current_module, &name, module_id);
                        }
                        ReservedSourceDefinition::Protocol { name } => {
                            let protocol_id = reference_declared_module(self.world, self.current_module, &name);
                            self.namespace = bind_declared_module(
                                self.world,
                                self.namespace,
                                self.current_module,
                                &name,
                                protocol_id,
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

    fn note_pending_types(&mut self) -> Result<(), FatalError> {
        let pending = std::mem::take(&mut self.pending_types);
        for PendingType {
            name,
            params,
            body,
            span,
        } in pending
        {
            let requester = self.interface_requester(span);
            let mut refs = TypeReferences::default();
            collect_type_references(
                self.world,
                self.telemetry,
                self.namespace,
                &body.inner,
                &requester,
                &mut refs,
            )?;
            super::drive::ExecutionContext::new(self.world, self.telemetry).record_type_def_refs(&name, refs.types);
            self.world.record_type_def_struct_refs(name.clone(), refs.structs);
            self.world.note_declared_type(self.source_owner, &name);

            super::drive::ExecutionContext::new(self.world, self.telemetry).note_type_decl(
                &name,
                NotedTypeDecl {
                    params,
                    body,
                    namespace: self.namespace,
                    span,
                },
            );
        }
        Ok(())
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

    fn apply_compiler_service(
        &mut self,
        service: &CompilerServiceForm,
        origin: ClauseOrigin,
    ) -> Result<Option<JobEffects>, FatalError> {
        match service.service {
            CompilerService::Define => self.apply_compiler_define(service, origin),
        }
    }

    fn apply_compiler_define(
        &mut self,
        service: &CompilerServiceForm,
        origin: ClauseOrigin,
    ) -> Result<Option<JobEffects>, FatalError> {
        let source_map = self.world.source_map();
        let surface = read_compiler_fragment_root(
            self.telemetry,
            &service.source,
            "Fz.Compiler.define source",
            &source_map.borrow(),
        )?;
        if !surface.attrs.is_empty() || surface.forms.len() != 1 {
            return Err(emit_job_diagnostic(
                self.telemetry,
                Diagnostic::error(
                    codes::INTERNAL_POST_RESOLUTION_LEFTOVER,
                    "Fz.Compiler.define expected one fully expanded source definition",
                    service.span,
                ),
            ));
        }
        let Some(form) = surface.forms.first() else {
            return Err(emit_job_diagnostic(
                self.telemetry,
                Diagnostic::error(
                    codes::INTERNAL_POST_RESOLUTION_LEFTOVER,
                    "Fz.Compiler.define expected one fully expanded source definition",
                    service.span,
                ),
            ));
        };
        if matches!(form, ScopeForm::CompilerService(_) | ScopeForm::MacroCall(_)) {
            return Err(emit_job_diagnostic(
                self.telemetry,
                Diagnostic::error(
                    codes::INTERNAL_POST_RESOLUTION_LEFTOVER,
                    "Fz.Compiler.define expected one fully expanded source definition",
                    service.span,
                ),
            ));
        }
        let context = FragmentPublicationContext::compiler_define(self.current_module, origin);
        self.apply_surface_fragment(&surface, &context)
    }

    fn define_source_function(
        &mut self,
        function_module: ModuleId,
        owner_module: ModuleId,
        namespace: Namespace,
        function: &FunctionForm,
        context: &FragmentPublicationContext,
    ) -> Result<FunctionPublication, FatalError> {
        self.define_source_function_superseding(function_module, owner_module, namespace, function, context, Vec::new())
    }

    /// Publishes `function`'s source as one answer of the walk, together
    /// with the sources of the definitions it replaced: they were published
    /// when the walk reached it, from the same ground.
    fn define_source_function_superseding(
        &mut self,
        function_module: ModuleId,
        owner_module: ModuleId,
        namespace: Namespace,
        function: &FunctionForm,
        context: &FragmentPublicationContext,
        superseded: Vec<FunctionPublication>,
    ) -> Result<FunctionPublication, FatalError> {
        let publication = publish_function_source(
            self.world,
            self.telemetry,
            self.source_owner,
            function_module,
            owner_module,
            namespace,
            function,
            context.export_public,
        );
        // Reaching this definition is one answer of the walk: whatever the
        // rest of the scope turns out to need, this function's source follows
        // from the ground the walk has read so far and nothing below it.
        // A function that gains clauses is published again, and this answer
        // stands in place of the one it supersedes.
        self.derivations
            .retain(|derivation| derivation.key != DerivationKey::Function(publication.function));
        self.derivations.push(JobDerivation {
            key: DerivationKey::Function(publication.function),
            reads: current_uses(self.reads.clone()),
            product_reads: self.product_reads.clone(),
            outputs: std::iter::once(&publication)
                .chain(&superseded)
                .map(|published| FactKey::FunctionSource(published.function))
                .collect(),
            changed: std::iter::once(&publication)
                .chain(&superseded)
                .filter(|published| published.source_changed)
                .map(|published| FactKey::FunctionSource(published.function))
                .collect(),
        });
        Ok(publication)
    }

    fn apply_item_macro_call(&mut self, macro_call: &MacroCallForm) -> Result<Option<JobEffects>, FatalError> {
        let scope = ScopeSnapshot::module(self.current_module, self.namespace);
        let surface = match expand_item_macro_fragment(self, macro_call, scope)? {
            ExpandedScopeFragment::Complete(surface) => surface,
            ExpandedScopeFragment::NotAMacro { display_name } => {
                if !self.is_script_scope() {
                    return Err(item_macro_not_defmacro(self.telemetry, &display_name, macro_call.span));
                }
                self.statements.push(StatementForm {
                    source: macro_call.source.clone(),
                    span: macro_call.span,
                });
                return Ok(None);
            }
            ExpandedScopeFragment::Blocked(effects) => return Ok(Some(*effects)),
        };
        if !self.is_script_scope() && surface.forms.iter().any(is_expression_form) {
            return Err(item_macro_expanded_to_a_non_definition(self.telemetry, macro_call.span));
        }
        // The fragment a `def` expands to is the definition the walk counted
        // when it reserved the `def`.
        let source_map = self.world.source_map();
        let functions_are_new = !defines_a_function(&macro_call.source, &source_map.borrow())
            .map_err(|error| emit_surface_read_error(self.telemetry, "item macro call read failed", &error))?;
        let origin = if functions_are_new {
            ClauseOrigin::Expanded
        } else {
            ClauseOrigin::Written
        };
        let context = FragmentPublicationContext {
            functions_are_new,
            origin,
            ..FragmentPublicationContext::expanded_fragment(self.current_module)
        };
        self.apply_surface_fragment(&surface, &context)
    }

    /// Runs an unquote fragment: the definition is quoted in the module as
    /// the walk has it, each `unquote` takes its value, and what comes back
    /// is defined as if it had been written.
    fn apply_fragment(&mut self, fragment: &FragmentForm) -> Result<Option<JobEffects>, FatalError> {
        let expansion = match self.evaluate_at_definition(&fragment.source, Evaluation::Quote, fragment.span)? {
            Evaluated::Value(expansion) => expansion,
            Evaluated::Blocked(effects) => return Ok(Some(*effects)),
        };
        let source_map = self.world.source_map();
        let surface = read_expanded_items(self.telemetry, &expansion, &source_map.borrow())?;
        self.require_fragment_definition(fragment, &surface)?;
        let context = FragmentPublicationContext {
            functions_are_new: fragment.head.is_none(),
            ..FragmentPublicationContext::expanded_fragment(self.current_module)
        };
        self.apply_surface_fragment(&surface, &context)
    }

    /// A fragment defines the one function its head names, so a result that
    /// defines anything else is a fault in the walk's reading of the head.
    fn require_fragment_definition(&self, fragment: &FragmentForm, surface: &ScopeSurface) -> Result<(), FatalError> {
        let defined = match surface.forms.as_slice() {
            [ScopeForm::Function(function)] => Some(function),
            _ => None,
        };
        let agrees = defined.is_some_and(|function| {
            fragment.head.as_ref().is_none_or(|head| {
                head.name == function.name && head.arity == function.arity && head.is_macro == function.is_macro
            })
        });
        if agrees {
            return Ok(());
        }
        Err(emit_job_diagnostic(
            self.telemetry,
            Diagnostic::error(
                codes::INTERNAL_POST_RESOLUTION_LEFTOVER,
                "an unquote fragment evaluated to something other than the one function its head names",
                fragment.span,
            ),
        ))
    }

    fn apply_statement(&mut self, statement: &StatementForm) -> Result<Option<JobEffects>, FatalError> {
        if !self.is_script_scope() {
            return Err(item_macro_expanded_to_a_non_definition(self.telemetry, statement.span));
        }
        self.statements.push(statement.clone());
        Ok(None)
    }

    fn apply_surface_fragment(
        &mut self,
        surface: &ScopeSurface,
        context: &FragmentPublicationContext,
    ) -> Result<Option<JobEffects>, FatalError> {
        if matches!(context.discovery, FragmentDiscovery::DiscoverNestedModules) {
            discover_modules(
                self.world,
                self.telemetry,
                self.source_owner,
                self.current_module,
                surface,
                &mut self.outputs,
                &mut self.changed,
            )?;
        }
        self.reserve_types(&surface.attrs)?;
        self.reserve_local_forms(&surface.forms, context)?;
        self.note_pending_types()?;
        self.apply_ordered_forms(&surface.forms, context)
    }

    fn apply_scope_form(
        &mut self,
        form: &ScopeForm,
        context: &FragmentPublicationContext,
    ) -> Result<Option<JobEffects>, FatalError> {
        match form {
            ScopeForm::Alias(alias) => {
                let module_id = self
                    .world
                    .reference_module(ModuleName::from_segments(alias.path.clone()));
                self.namespace = self.world.bind_namespace(
                    self.namespace,
                    alias.as_name.clone(),
                    NamespaceSymbol::Module(module_id),
                );
                Ok(None)
            }
            ScopeForm::Import(import) => self.apply_import(import),
            ScopeForm::Require(import) => self.apply_require(import),
            ScopeForm::CompilerService(service) => self.apply_compiler_service(service, context.origin),
            ScopeForm::Overridable(overridable) => {
                self.mark_overridable(overridable)?;
                Ok(None)
            }
            ScopeForm::Function(function) => self.apply_function(function, context),
            ScopeForm::Module(module) => {
                let module_id = reference_declared_module(self.world, self.current_module, &module.name);
                self.world.scope_module(module_id, self.namespace);
                let source_map = self.world.source_map();
                let body = read_module_body_surface(module, &source_map.borrow())
                    .map_err(|error| emit_surface_read_error(self.telemetry, "module body read failed", &error))?;
                self.register_protocol_impl_providers(module_id, &body)
            }
            ScopeForm::Protocol(protocol) => {
                let protocol_id = reference_declared_module(self.world, self.current_module, &protocol.name);
                self.world.scope_module(protocol_id, self.namespace);
                Ok(None)
            }
            ScopeForm::ProtocolImpl(protocol_impl) => self.register_protocol_impl(protocol_impl),
            ScopeForm::MacroCall(macro_call) => self.apply_item_macro_call(macro_call),
            ScopeForm::Fragment(fragment) => self.apply_fragment(fragment),
            ScopeForm::Statement(statement) => self.apply_statement(statement),
            ScopeForm::Attribute(attribute) => self.apply_attribute(attribute),
            ScopeForm::Struct(form) => {
                let def = match self.struct_def(form)? {
                    Evaluated::Value(def) => def,
                    Evaluated::Blocked(effects) => return Ok(Some(*effects)),
                };
                self.publish_struct_def(&def)?;
                let function = build_struct_function(def.span).map_err(|error| {
                    emit_internal_surface_error(self.telemetry, format!("struct function synthesis failed: {error}"))
                })?;
                self.apply_function(&function, context)
            }
        }
    }

    /// Binds `@name` to the attribute's value for every definition after it
    /// in the module, as Elixir's `Module.put_attribute/3` does.
    fn apply_attribute(&mut self, attribute: &AttributeForm) -> Result<Option<JobEffects>, FatalError> {
        let value = match self.attribute_value(attribute)? {
            Evaluated::Value(value) => value,
            Evaluated::Blocked(effects) => return Ok(Some(*effects)),
        };
        self.require_documentation_value(attribute, &value)?;
        self.namespace = self.world.bind_namespace(
            self.namespace,
            attribute_symbol(&attribute.name),
            NamespaceSymbol::Splice(value),
        );
        Ok(None)
    }

    /// Runs the `@doc` expressions written above a function, in the module as
    /// the walk has defined it so far, and refuses a value that documents
    /// nothing.
    fn evaluate_function_docs(&mut self, function: &FunctionForm) -> Result<Option<JobEffects>, FatalError> {
        let source_map = self.world.source_map();
        let docs = function_doc_attributes(&function.source, &source_map.borrow())
            .map_err(|error| emit_surface_read_error(self.telemetry, "function documentation read failed", &error))?;
        for doc in &docs {
            let value = match self.attribute_value(doc)? {
                Evaluated::Value(value) => value,
                Evaluated::Blocked(effects) => return Ok(Some(*effects)),
            };
            self.require_documentation_value(doc, &value)?;
        }
        Ok(None)
    }

    /// A documentation attribute holds a binary, `false`, `nil` or a keyword
    /// list; any other value is the author's error, reported as Elixir does.
    fn require_documentation_value(
        &self,
        attribute: &AttributeForm,
        value: &QuotedSourceRoot,
    ) -> Result<(), FatalError> {
        if !is_documentation_attribute(&attribute.name) {
            return Ok(());
        }
        let valid = is_documentation_value(&value.cursor())
            .map_err(|error| emit_surface_read_error(self.telemetry, "documentation attribute read failed", &error))?;
        if valid {
            return Ok(());
        }
        Err(emit_job_diagnostic(
            self.telemetry,
            Diagnostic::error(
                codes::LOWER_INVALID_DOCUMENTATION,
                format!(
                    "@{} is a built-in module attribute for documentation. It should be either false, nil, a string, or a keyword list",
                    attribute.name
                ),
                attribute.span,
            ),
        ))
    }

    /// The quoted code that rebuilds an attribute's value. A written literal
    /// is its own; an expression that computes runs now, once, and its value
    /// is escaped.
    fn attribute_value(&mut self, attribute: &AttributeForm) -> Result<Evaluated<QuotedSourceRoot>, FatalError> {
        let source_map = self.world.source_map();
        let written = is_written_literal(&attribute.value, attribute.span, &source_map.borrow())
            .map_err(|error| emit_surface_read_error(self.telemetry, "module attribute read failed", &error))?;
        if written {
            return Ok(Evaluated::Value(attribute.value.clone()));
        }
        self.evaluate_at_definition(&attribute.value, MACRO_ESCAPE, attribute.span)
    }

    /// The definition a `defstruct` makes. A field list that computes is
    /// evaluated now, and its value read as a written list.
    fn struct_def(&mut self, form: &StructForm) -> Result<Evaluated<StructDef>, FatalError> {
        let source_map = self.world.source_map();
        let read = |fields: &QuotedSourceRoot| {
            read_struct_fields(fields, form.span, &source_map.borrow())
                .map_err(|error| emit_surface_read_error(self.telemetry, "defstruct read failed", &error))
        };
        if let StructFields::Written(def) = read(&form.fields)? {
            return Ok(Evaluated::Value(def));
        }
        let fields = match self.evaluate_at_definition(&form.fields, DEFSTRUCT_FIELDS, form.span)? {
            Evaluated::Value(fields) => fields,
            Evaluated::Blocked(effects) => return Ok(Evaluated::Blocked(effects)),
        };
        match read(&fields)? {
            StructFields::Written(def) => Ok(Evaluated::Value(def)),
            StructFields::Computed => Err(emit_internal_surface_error(
                self.telemetry,
                "an evaluated defstruct field list is a list of names and escaped defaults".to_string(),
            )),
        }
    }

    /// Runs `expr` in the module as the walk has defined it so far, and gives
    /// back the quoted code `escape` makes of its value.
    fn evaluate_at_definition(
        &mut self,
        expr: &QuotedSourceRoot,
        evaluation: Evaluation,
        span: Span,
    ) -> Result<Evaluated<QuotedSourceRoot>, FatalError> {
        let name = definition_time::evaluator_name(self.definition_time_evaluations);
        self.definition_time_evaluations += 1;
        let evaluator = definition_time::evaluator(expr, evaluation, &name, span).map_err(|error| {
            emit_internal_surface_error(
                self.telemetry,
                format!("definition-time evaluator synthesis failed: {error}"),
            )
        })?;
        let function = FunctionForm {
            source: evaluator.definition,
            name,
            arity: 0,
            is_macro: true,
            is_private: true,
            variadic: false,
            span,
        };
        let context = FragmentPublicationContext::module_surface(self.current_module);
        let publication = self.define_source_function(
            self.current_module,
            self.current_module,
            self.namespace,
            &function,
            &context,
        )?;
        let scope = ScopeSnapshot::module(self.current_module, self.namespace);
        let owner = expr.clone();
        match self.expand_macro_invocation(&owner, evaluator.invocation, publication.function, scope, 0, &[])? {
            ExpandedValue::Complete(value) => Ok(Evaluated::Value(owner.subroot(value))),
            ExpandedValue::Blocked(effects) => Ok(Evaluated::Blocked(effects)),
        }
    }

    fn apply_function(
        &mut self,
        function: &FunctionForm,
        context: &FragmentPublicationContext,
    ) -> Result<Option<JobEffects>, FatalError> {
        if let Some(effects) = self.evaluate_function_docs(function)? {
            return Ok(Some(effects));
        }
        let Some(reached) = self.reach_definition(function, context)? else {
            return Ok(None);
        };
        let superseded = std::mem::take(&mut self.local_callable(&function.name, function.arity).superseded);
        let publication = self.define_source_function_superseding(
            self.current_module,
            context.owner_module,
            reached.namespace,
            &reached.function,
            context,
            superseded,
        )?;
        self.callables
            .retain(|callable| callable.function != publication.function);
        if let Some(callable) = publication.callable {
            self.callables.push(callable);
        }
        Ok(None)
    }

    /// Records that the walk has reached `function`, and answers what to
    /// publish and the scope it stands in, or `None` when it does not stand:
    /// a definition with another still to come is replaced by it or refused.
    /// A definition that replaces one marked overridable sees that one as
    /// `super`. A definition whose clauses join the function's earlier ones
    /// answers all of them, in the order they were reached.
    fn reach_definition(
        &mut self,
        function: &FunctionForm,
        context: &FragmentPublicationContext,
    ) -> Result<Option<ReachedFunction>, FatalError> {
        let callable = self.local_callable(&function.name, function.arity);
        callable.to_come = callable
            .to_come
            .checked_sub(1)
            .expect("the walk reaches each definition it counted once");
        let mut function = function.clone();
        let mut origin = context.origin;
        let namespace = match std::mem::replace(&mut callable.standing, Standing::NotDefined) {
            Standing::NotDefined => self.namespace,
            Standing::Overridable(replaced) if replaced.function.is_macro == function.is_macro => {
                callable.replaced += 1;
                let ordinal = callable.replaced;
                self.publish_super(replaced, ordinal, context)?
            }
            Standing::Overridable(replaced) => {
                return Err(emit_job_diagnostic(
                    self.telemetry,
                    overridden_as_another_kind(&function, &replaced.function),
                ));
            }
            Standing::Defined(first) if first.takes_clauses_of(&function, context.origin) => {
                function = first.function.followed_by(&function).map_err(|error| {
                    emit_internal_surface_error(self.telemetry, format!("function clause join failed: {error}"))
                })?;
                origin = ClauseOrigin::Expanded;
                self.namespace
            }
            Standing::Defined(first) => {
                return Err(emit_job_diagnostic(
                    self.telemetry,
                    defined_again(&function, &first.function),
                ));
            }
        };
        let owner_module = context.owner_module;
        let callable = self.local_callable(&function.name, function.arity);
        callable.standing = Standing::Defined(ReachedDefinition {
            function: function.clone(),
            namespace,
            owner_module,
            origin,
        });
        Ok((callable.to_come == 0).then_some(ReachedFunction { function, namespace }))
    }

    fn local_callable(&mut self, name: &str, arity: usize) -> &mut LocalCallable {
        self.local_callables
            .get_mut(&(name.to_string(), arity))
            .expect("a definition is reserved before the walk reaches it")
    }

    /// Publishes a replaced definition as a private function named the way
    /// Elixir names it, `name (overridable N)`, and answers the walk's scope
    /// with `super` bound to it, for the definition that replaces it.
    fn publish_super(
        &mut self,
        replaced: ReachedDefinition,
        ordinal: usize,
        context: &FragmentPublicationContext,
    ) -> Result<Namespace, FatalError> {
        let name = replaced.function.name.clone();
        let function = FunctionForm {
            name: format!("{name} (overridable {ordinal})"),
            is_private: true,
            ..replaced.function
        };
        let publication = publish_function_source(
            self.world,
            self.telemetry,
            self.source_owner,
            self.current_module,
            replaced.owner_module,
            replaced.namespace,
            &function,
            context.export_public,
        );
        let symbol = declared_callable_kind(function.is_macro).namespace_symbol(publication.function);
        self.local_callable(&name, function.arity).superseded.push(publication);
        Ok(self.world.bind_namespace(self.namespace, "super", symbol))
    }

    fn mark_overridable(&mut self, overridable: &OverridableForm) -> Result<(), FatalError> {
        for (name, arity) in &overridable.functions {
            let marked = self
                .local_callables
                .get_mut(&(name.clone(), *arity))
                .is_some_and(|callable| callable.standing.mark_overridable());
            if !marked {
                return Err(emit_job_diagnostic(
                    self.telemetry,
                    Diagnostic::error(
                        codes::RESOLVE_OVERRIDABLE,
                        format!("cannot make function `{name}/{arity}` overridable because it was not defined"),
                        overridable.span,
                    ),
                ));
            }
        }
        Ok(())
    }

    /// Publishes `def`'s ordered fields under the enclosing module and emits
    /// `FactKey::StructDefined` alongside `ModuleDefined`/`ModuleInterface`
    /// when this module body settles — the same co-output timing those two
    /// facts already use (`define_module`'s `ScopePublication::Complete`
    /// branch). Mirrors `TypeDefined`'s store shape. Once published, this is
    /// the validate-on-settle half of the struct obligation store: every
    /// field expectation recorded on `module` so far (including one this same
    /// module body's own `@type t` recorded against itself, one inch above in
    /// source order) is checked against the freshly defined schema, mirroring
    /// `jobs::source::define_module`'s `validate_module_interface_expectations`
    /// call.
    ///
    /// fz's grammar is one `defstruct` per module (mirroring Elixir). A
    /// second `defstruct` in the same module body is diagnosed at its own
    /// span rather than silently overwriting the first: `StructDefMap::define`
    /// is a plain `HashMap::insert` (last-wins), so without this guard a
    /// malformed duplicate-defstruct module would silently flip which struct
    /// "wins" from one publish to the next, with no diagnostic either way.
    fn publish_struct_def(&mut self, def: &StructDef) -> Result<(), FatalError> {
        let module = self.current_module;
        // A second `defstruct` form reached while publishing THIS module
        // body -- one `ScopeSession` covers exactly one execution of one
        // body, including every `defstruct` a macro expansion applies into
        // it (`apply_item_macro_call` recurses back into `apply_scope_form`
        // without ever changing `self.current_module`) -- is always a
        // genuine duplicate, independent of whether its fields happen to
        // agree with the first. That content-independence matters because a
        // macro invoked twice from a literal (non-`unquote`) `defstruct`
        // template carries no source span of its own (the validated AST read
        // returns absent provenance for metadata without a `__fz_span__` entry),
        // so two macro-emitted defstructs in one module compare
        // span-and-fields-EQUAL whenever the macro's argument happens to
        // repeat the same fields -- exactly the case the fields-comparison
        // check below cannot see. Checking occurrence count first, before
        // ever comparing content, catches that case without relying on span
        // or fields at all.
        if self.struct_form_seen {
            return Err(self.duplicate_struct_diagnostic(module, def.span));
        }
        self.struct_form_seen = true;
        // A job re-running this same module body (incremental recompute,
        // multiple demanders) starts a fresh `ScopeSession` and re-publishes
        // the byte-identical `defstruct` every time -- that is idempotent,
        // not a duplicate. A genuine second `defstruct` from an EARLIER
        // execution's stored definition DIFFERS from the incoming one, so we
        // compare the whole `StructDef` rather than the span alone: any
        // difference against an already-recorded struct is diagnosed here,
        // before `define_struct_def` could overwrite the kept-first
        // definition.
        if let Some(existing) = self.world.struct_def(module)
            && existing != def
        {
            return Err(self.duplicate_struct_diagnostic(module, def.span));
        }
        let changed =
            super::drive::ExecutionContext::new(self.world, self.telemetry).define_struct_def(module, def.clone());
        self.outputs.push(FactKey::StructDefined(module));
        if changed {
            self.changed.push(FactKey::StructDefined(module));
        }
        super::drive::ExecutionContext::new(self.world, self.telemetry).validate_struct_field_expectations(module)
    }

    fn duplicate_struct_diagnostic(&mut self, module: ModuleId, span: Span) -> FatalError {
        let module_name = self
            .world
            .module_name(module)
            .map(ToString::to_string)
            .unwrap_or_else(|| format!("<unnamed module {}>", module.as_u32()));
        emit_job_diagnostic(
            self.telemetry,
            Diagnostic::error(
                codes::RESOLVE_DUPLICATE_STRUCT,
                format!("module `{}` already defines a struct", module_name),
                span,
            ),
        )
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
    ) -> Result<Option<JobEffects>, FatalError> {
        let outer_namespace = self.namespace;
        let bound = self.bind_sibling_module_names(module, self.namespace, &body.forms);
        let result = match bound {
            Ok((namespace, definitions)) => {
                self.namespace = namespace;
                self.register_protocol_impl_providers_walk(module, body, &definitions)
            }
            Err(error) => Err(error),
        };
        self.namespace = outer_namespace;
        result
    }

    /// Binds `forms`' own `defmodule`/`defprotocol` declarations into
    /// `namespace` as `module`'s children. A real scoping session builds this
    /// same binding for its own module as part of `reserve_local_forms`,
    /// before walking its forms in order; this discovery walk visits a nested
    /// module's body without ever running that session for it, so a nested
    /// `defimpl`'s bare protocol or target name -- naming a sibling declared
    /// right next to it, such as a protocol defined in the same enclosing
    /// module -- would otherwise resolve against the outer file's namespace
    /// instead of its own.
    ///
    /// Every `MacroCall` form's reservation is decoded here, once, and handed
    /// back alongside the namespace it produced (`None` for a form that
    /// isn't a `MacroCall`, or that reserved nothing): `register_protocol_impl_providers_walk`
    /// needs that same reservation, by form, to register providers, and reads
    /// it from here rather than decoding its source a second time.
    fn bind_sibling_module_names(
        &mut self,
        module: ModuleId,
        namespace: Namespace,
        forms: &[ScopeForm],
    ) -> Result<(Namespace, Vec<Option<ReservedSourceDefinition>>), FatalError> {
        let mut namespace = namespace;
        let mut definitions = Vec::with_capacity(forms.len());
        for form in forms {
            let definition = match form {
                ScopeForm::Module(child) => {
                    let child_id = reference_declared_module(self.world, module, &child.name);
                    namespace = bind_declared_module(self.world, namespace, module, &child.name, child_id);
                    None
                }
                ScopeForm::Protocol(protocol) => {
                    let protocol_id = reference_declared_module(self.world, module, &protocol.name);
                    namespace = bind_declared_module(self.world, namespace, module, &protocol.name, protocol_id);
                    None
                }
                ScopeForm::MacroCall(macro_call) => {
                    let source_map = self.world.source_map();
                    let definition =
                        reserved_source_definition(&macro_call.source, &source_map.borrow()).map_err(|error| {
                            emit_surface_read_error(self.telemetry, "impl discovery reservation failed", &error)
                        })?;
                    match &definition {
                        Some(ReservedSourceDefinition::Module { name }) => {
                            let child_id = reference_declared_module(self.world, module, name);
                            namespace = bind_declared_module(self.world, namespace, module, name, child_id);
                        }
                        Some(ReservedSourceDefinition::Protocol { name }) => {
                            let protocol_id = reference_declared_module(self.world, module, name);
                            namespace = bind_declared_module(self.world, namespace, module, name, protocol_id);
                        }
                        Some(ReservedSourceDefinition::Function { .. } | ReservedSourceDefinition::ProtocolImpl)
                        | None => {}
                    }
                    definition
                }
                _ => None,
            };
            definitions.push(definition);
        }
        Ok((namespace, definitions))
    }

    fn register_protocol_impl_providers_walk(
        &mut self,
        module: ModuleId,
        body: &ScopeSurface,
        definitions: &[Option<ReservedSourceDefinition>],
    ) -> Result<Option<JobEffects>, FatalError> {
        for (form, definition) in body.forms.iter().zip(definitions) {
            match form {
                ScopeForm::ProtocolImpl(impl_form) => {
                    if let Some(blocked) = self.register_protocol_impl(impl_form)? {
                        return Ok(Some(blocked));
                    }
                }
                ScopeForm::Module(child) => {
                    let child_id = reference_declared_module(self.world, module, &child.name);
                    let source_map = self.world.source_map();
                    let nested = read_module_body_surface(child, &source_map.borrow()).map_err(|error| {
                        emit_surface_read_error(self.telemetry, "nested module body read failed", &error)
                    })?;
                    if let Some(blocked) = self.register_protocol_impl_providers(child_id, &nested)? {
                        return Ok(Some(blocked));
                    }
                }
                ScopeForm::MacroCall(macro_call) => {
                    let Some(definition) = definition else {
                        continue;
                    };
                    match definition {
                        ReservedSourceDefinition::ProtocolImpl => {
                            let fragment = read_compiler_fragment_root(
                                self.telemetry,
                                &macro_call.source,
                                "raw scope-definition fragment",
                                &self.world.source_map().borrow(),
                            )?;
                            if let Some(ScopeForm::ProtocolImpl(impl_form)) = fragment.forms.first() {
                                let impl_form = impl_form.clone();
                                if let Some(blocked) = self.register_protocol_impl(&impl_form)? {
                                    return Ok(Some(blocked));
                                }
                            }
                        }
                        ReservedSourceDefinition::Module { .. } => {
                            let fragment = read_compiler_fragment_root(
                                self.telemetry,
                                &macro_call.source,
                                "raw scope-definition fragment",
                                &self.world.source_map().borrow(),
                            )?;
                            if let Some(ScopeForm::Module(child)) = fragment.forms.first() {
                                let child_id = reference_declared_module(self.world, module, &child.name);
                                let source_map = self.world.source_map();
                                let nested =
                                    read_module_body_surface(child, &source_map.borrow()).map_err(|error| {
                                        emit_surface_read_error(
                                            self.telemetry,
                                            "nested module body read failed",
                                            &error,
                                        )
                                    })?;
                                if let Some(blocked) = self.register_protocol_impl_providers(child_id, &nested)? {
                                    return Ok(Some(blocked));
                                }
                            }
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }
        Ok(None)
    }

    /// The effects of a walk that has blocked, with everything the walk
    /// accumulated moved in. A blocked walk ends the session, so the session
    /// hands its collections over rather than copying them.
    fn blocked_effects(&mut self, mut effects: JobEffects) -> JobEffects {
        effects.reads.extend(current_uses(std::mem::take(&mut self.reads)));
        effects.product_reads.append(&mut self.product_reads);
        // The answers the walk reached before it blocked are complete, and each
        // stands on the ground above it, so they are published as their own
        // derivations rather than left dirty behind the wait.
        effects.derivations.append(&mut self.derivations);
        effects.outputs.append(&mut self.outputs);
        effects.changed.append(&mut self.changed);
        effects
    }

    fn apply_require(&mut self, import: &super::quoted_surface::ImportForm) -> Result<Option<JobEffects>, FatalError> {
        let required_module = self.resolve_import_module(import);
        self.refuse_module_defined_in_this_scope(import, required_module)?;
        self.world
            .note_module_reference_expectation(required_module, self.interface_requester(import.span));
        self.bind_required_module_path(import, required_module);
        self.namespace = self.world.bind_required_module(self.namespace, required_module);
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
            Self::select_required_macro_exports(self.telemetry, import, interface.callables())?
        };
        self.record_required_remote_macros(&selected);
        Ok(None)
    }

    fn bind_required_module_path(&mut self, import: &super::quoted_surface::ImportForm, module: ModuleId) {
        let Some((first, rest)) = import.path.split_first() else {
            return;
        };
        let bound_module = if rest.is_empty() {
            module
        } else {
            match self.world.lookup_namespace(self.namespace, first) {
                Some(NamespaceSymbol::Module(prefix)) => prefix,
                _ => self
                    .world
                    .reference_module(ModuleName::from_segments(vec![first.clone()])),
            }
        };
        self.namespace =
            self.world
                .bind_namespace(self.namespace, first.clone(), NamespaceSymbol::Module(bound_module));
    }

    fn select_required_macro_exports(
        telemetry: &T,
        import: &super::quoted_surface::ImportForm,
        callables: &[ModuleInterfaceCallable],
    ) -> Result<Vec<ModuleInterfaceCallable>, FatalError> {
        if let Some(only) = import.only.as_deref() {
            let mut selected = Vec::with_capacity(only.len());
            for (name, arity) in only {
                let Some(callable) = find_callable(callables, name, *arity) else {
                    return Err(emit_job_diagnostic(
                        telemetry,
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
                        telemetry,
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

        let mut denied = HashSet::default();
        for (name, arity) in import.except.as_deref().unwrap_or(&[]) {
            let Some(callable) = find_callable(callables, name, *arity) else {
                return Err(emit_job_diagnostic(
                    telemetry,
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
                    telemetry,
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
            .filter(|callable| !denied.contains(&(callable.reference.name(), callable.reference.arity)))
            .cloned()
            .collect())
    }

    fn apply_import(&mut self, import: &super::quoted_surface::ImportForm) -> Result<Option<JobEffects>, FatalError> {
        let imported_module = self.resolve_import_module(import);
        self.refuse_module_defined_in_this_scope(import, imported_module)?;
        self.world
            .note_module_reference_expectation(imported_module, self.interface_requester(import.span));
        if self.world.module_interface_revision(imported_module).is_some() {
            self.reads.push(FactKey::ModuleInterface(imported_module));
            self.bind_interface_imports(import, imported_module)?;
            return Ok(None);
        }
        let Some(only) = import.only.as_deref() else {
            return Ok(Some(self.wait_for_module_interface(imported_module)));
        };
        let selected: Vec<ModuleInterfaceCallable> = only
            .iter()
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
            .collect();
        for export in &selected {
            self.namespace = bind_callable(self.world, self.namespace, export);
        }
        Ok(None)
    }

    /// Binds the callables an `import` selects from `module`'s published
    /// interface: the `only` list in its order, or every callable `except`
    /// does not deny.
    fn bind_interface_imports(
        &mut self,
        import: &super::quoted_surface::ImportForm,
        module: ModuleId,
    ) -> Result<(), FatalError> {
        let unknown_import = |telemetry, name: &str, arity: usize| {
            emit_job_diagnostic(
                telemetry,
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
            )
        };
        if let Some(only) = import.only.as_deref() {
            for (name, arity) in only {
                self.namespace = self
                    .world
                    .bind_interface_callable(self.namespace, module, name, *arity)
                    .ok_or_else(|| unknown_import(self.telemetry, name, *arity))?;
            }
        } else if let Some(except) = import.except.as_deref() {
            let callables = self.world.module_interface(module).callables();
            let mut deny = HashSet::default();
            for (name, arity) in except {
                if find_callable(callables, name, *arity).is_none() {
                    return Err(unknown_import(self.telemetry, name, *arity));
                }
                deny.insert((name.as_str(), *arity));
            }
            self.namespace = self.world.bind_interface_callables(self.namespace, module, |callable| {
                !deny.contains(&(callable.reference.name(), callable.reference.arity))
            });
        } else {
            self.namespace = self.world.bind_interface_callables(self.namespace, module, |_| true);
        }
        Ok(())
    }

    /// A module is not loaded until the scope that defines it has finished,
    /// so that scope cannot require or import it.
    fn refuse_module_defined_in_this_scope(
        &self,
        import: &super::quoted_surface::ImportForm,
        module: ModuleId,
    ) -> Result<(), FatalError> {
        if !self
            .world
            .module_defined_within(module, self.current_module, self.source_owner)
        {
            return Ok(());
        }
        Err(emit_job_diagnostic(
            self.telemetry,
            Diagnostic::error(
                codes::RESOLVE_MODULE_NOT_LOADED,
                format!(
                    "module {} is not loaded but was defined. This happens when you depend on a module in the same context in which it is defined. Try defining the module outside the context that uses it.",
                    self.world
                        .module_name(module)
                        .expect("a module with a recorded source has a name")
                ),
                import.span,
            ),
        ))
    }

    fn resolve_import_module(&mut self, import: &super::quoted_surface::ImportForm) -> ModuleId {
        let path = ModuleName::from_segments(import.path.clone());
        self.world.resolve_module_name(self.namespace, &path)
    }

    fn interface_requester(&self, span: Span) -> InterfaceRequester {
        InterfaceRequester {
            owner: self.source_owner,
            module: self.current_module,
            span,
        }
    }

    fn wait_for_module_interface(&self, module: ModuleId) -> JobEffects {
        // `FactKey::ModuleInterface`'s producer is demand-selected in
        // `World::demand_fact_producer` (Job::DefineModule when the module has
        // source state or is a runtime module, else Job::DefineModuleInterface)
        // -- the same selection this site used to push directly.
        JobEffects::wait_on_current(FactKey::ModuleInterface(module))
    }

    fn record_required_remote_macros(&mut self, callables: &[ModuleInterfaceCallable]) {
        for callable in callables {
            if callable.kind == InterfaceCallableKind::Macro {
                self.namespace = self.world.bind_required_macro(self.namespace, callable.function);
            }
        }
    }
    /// Hoist a `defimpl Protocol, for: Target` to its own independently-
    /// demandable module identified by the typed `(protocol, target)` pair. Discovery
    /// records the impl as a `ProtocolImpl` module source resolved
    /// at its lexical site; `DefineModule(impl_module)`
    /// later publishes it without defining its lexical host. The provider index
    /// points at that module so dispatch demands exactly the impl.
    ///
    /// The provider registration below runs unconditionally, whether or not
    /// the protocol it names ever resolves: a forward-declared or genuinely
    /// undefined protocol must still get a provider entry, so later dispatch
    /// has something to point at rather than nothing. The missing-callback
    /// check that follows is the only part that can wait.
    fn register_protocol_impl(&mut self, form: &ProtocolImplForm) -> Result<Option<JobEffects>, FatalError> {
        let protocol = self.world.resolve_module_name(self.namespace, &form.protocol);
        self.world
            .note_module_reference_expectation(protocol, self.interface_requester(form.span));
        let target = self.world.resolve_module_name(self.namespace, &form.target);
        let impl_module = self.world.reference_protocol_impl_module(protocol, target);
        let source_map = self.world.source_map();
        let body = Rc::new(
            read_protocol_impl_body_surface(form, &source_map.borrow()).map_err(|error| {
                emit_internal_surface_error(
                    self.telemetry,
                    format!("quoted protocol impl body read failed: {error}"),
                )
            })?,
        );
        // The protocol owns this typed implementation pair, not its lexical
        // host. This edge keeps the implementation independently demandable.
        let revision = self.world.index_protocol_impl_module(
            impl_module,
            self.source_owner,
            protocol,
            form.source.clone(),
            form.span,
            ProtocolImplSource {
                protocol,
                target,
                body: Rc::clone(&body),
            },
        );
        self.world.scope_module(impl_module, self.namespace);
        publish_module_indexed(self.world, impl_module, revision, &mut self.outputs, &mut self.changed);
        let grew = self
            .world
            .register_protocol_impl_provider(protocol, target, impl_module);
        self.outputs.push(FactKey::ProtocolImplProviders(protocol));
        if grew {
            self.changed.push(FactKey::ProtocolImplProviders(protocol));
        }
        if let Some(blocked) = self.warn_missing_protocol_callbacks(protocol, impl_module, form.span, &body)? {
            return Ok(Some(blocked));
        }
        Ok(None)
    }

    /// Compares the protocol's declared `(name, arity)` callback set against
    /// this impl body's own, using each side's already-indexed surface --
    /// the same forms `publish_protocol_surface` and
    /// `publish_resolved_protocol_impl` walk. A declared callback the impl
    /// never defines warns under `protocol/missing-callback`, naming the
    /// arity the impl defines instead when that name exists at one.
    ///
    /// The protocol may live in a file this submission has not indexed yet
    /// -- a library protocol most of all, always in its own file. Rather
    /// than comparing against nothing and staying quiet, this waits on
    /// whatever fact would bring the protocol's index into existence
    /// (`ExecutionContext::wait_for_module_indexed`, the same escalation
    /// `Job::DefineModule` climbs for any other unresolved module) and runs
    /// again once the protocol's declared surface exists to compare against.
    /// `register_protocol_impl` already noted a reference expectation for
    /// `protocol` at this impl's own span, so a name that never resolves to
    /// a real protocol settles into the ordinary "module is not defined"
    /// diagnostic there instead of leaving this wait stuck forever.
    ///
    /// A name that *does* resolve, to a module indexed as something other
    /// than a `defprotocol`, is a different, definite answer -- not a
    /// missing surface to keep waiting on, an impossible one. Elixir raises
    /// this immediately, at compile time; this reports it the same way,
    /// as an error rather than the missing-callback warning above.
    fn warn_missing_protocol_callbacks(
        &mut self,
        protocol: ModuleId,
        impl_module: ModuleId,
        span: Span,
        impl_body: &ScopeSurface,
    ) -> Result<Option<JobEffects>, FatalError> {
        let declared = match self.world.protocol_callback_surface(protocol) {
            ProtocolCallbackSurface::Unindexed => {
                let effects =
                    super::drive::ExecutionContext::new(self.world, self.telemetry).wait_for_module_indexed(protocol);
                return Ok(Some(effects));
            }
            ProtocolCallbackSurface::NotAProtocol => {
                let name = self
                    .world
                    .module_name(protocol)
                    .expect("indexed module has a denotation")
                    .to_string();
                return Err(emit_job_diagnostic(
                    self.telemetry,
                    super::source_diagnostics::not_a_protocol_diagnostic(span, &name),
                ));
            }
            ProtocolCallbackSurface::Declared(surface) => surface,
        };
        let declared_callbacks: Vec<(String, usize)> = declared
            .forms
            .iter()
            .filter_map(|form| match form {
                ScopeForm::Function(callback) => Some((callback.name.clone(), callback.arity)),
                _ => None,
            })
            .collect();
        let impl_callbacks: Vec<(&str, usize)> = impl_body
            .forms
            .iter()
            .filter_map(|form| match form {
                ScopeForm::Function(callback) => Some((callback.name.as_str(), callback.arity)),
                _ => None,
            })
            .collect();
        let protocol_display = self
            .world
            .module_name(protocol)
            .expect("referenced protocol module")
            .to_string();
        let implementation_display = self
            .world
            .module_name(impl_module)
            .expect("just-referenced impl module")
            .to_string();
        for (name, arity) in declared_callbacks {
            if impl_callbacks
                .iter()
                .any(|(impl_name, impl_arity)| *impl_name == name && *impl_arity == arity)
            {
                continue;
            }
            let other_arity = impl_callbacks
                .iter()
                .find(|(impl_name, _)| *impl_name == name)
                .map(|(_, impl_arity)| *impl_arity);
            let diagnostic = super::source_diagnostics::protocol_missing_callback_diagnostic(
                span,
                &name,
                arity,
                &protocol_display,
                &implementation_display,
                other_arity,
            );
            super::drive::ExecutionContext::new(self.world, self.telemetry).emit_warning_once(diagnostic);
        }
        Ok(None)
    }

    /// Publish a hoisted impl module from its settled `ProtocolImplSource`: define
    /// each callback under the impl module, key them by the protocol's callback
    /// identity, and refresh the protocol's dispatch. This is the define-tier
    /// counterpart of `register_protocol_impl`, run by `DefineModule(impl_module)`.
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
                    self.telemetry,
                    Diagnostic::error(
                        codes::LOWER_UNSUPPORTED,
                        "compiler2 protocol implementations only support callback functions",
                        Span::DUMMY,
                    ),
                ));
            };
            if function.is_macro {
                return Err(emit_job_diagnostic(
                    self.telemetry,
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
            functions_are_new: true,
            origin: ClauseOrigin::Written,
        };
        let mut callbacks = HashMap::default();
        for function in functions {
            let publication = self.define_source_function(impl_module, impl_module, impl_scope, &function, &context)?;
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
        super::drive::ExecutionContext::new(self.world, self.telemetry).define_protocol_impl(
            &source.protocol,
            &source.target,
            callbacks,
        );
        self.outputs.push(FactKey::ProtocolDispatch(source.protocol));
        if super::drive::ExecutionContext::new(self.world, self.telemetry).refresh_protocol_dispatch(source.protocol) {
            self.changed.push(FactKey::ProtocolDispatch(source.protocol));
        }
        Ok(())
    }

    fn complete(self) -> ScopePublication {
        ScopePublication::Complete {
            namespace: self.namespace,
            revision_floor: self.revision_floor,
            reads: self.reads,
            product_reads: self.product_reads,
            derivations: self.derivations,
            outputs: self.outputs,
            changed: self.changed,
            interface: ModuleInterface::new(self.callables),
        }
    }
}

fn is_expression_form(form: &ScopeForm) -> bool {
    matches!(form, ScopeForm::MacroCall(_) | ScopeForm::Statement(_))
}

pub(super) fn first_clause_span(source: &QuotedSourceRoot, sources: &SourceMap) -> Option<Span> {
    let clause = source.cursor().list_items().ok()?.into_iter().next()?;
    clause.ast_node(sources).ok()??.span
}

/// `def main() do <statements> end`: one statement is the body as written,
/// several are one `__block__` in walk order.
fn build_script_main(statements: &[StatementForm], span: Span) -> Result<FunctionForm, QuotedSourceError> {
    let builder = statements[0].source.builder();
    let meta = QuotedSourceMetadata {
        span: Some(span),
        ..QuotedSourceMetadata::default()
    };
    let roots: Vec<AnyValueRef> = statements.iter().map(|statement| statement.source.root()).collect();
    let body = match roots.as_slice() {
        [only] => *only,
        _ => builder.call("__block__", &meta, &roots)?,
    };
    let head = builder.call("main", &meta, &[])?;
    let do_kw = builder.list(&[builder.keyword("do", body)?])?;
    let clause = builder.call("def", &meta, &[head, do_kw])?;
    Ok(FunctionForm {
        source: statements[0].source.subroot(builder.list(&[clause])?),
        name: "main".to_string(),
        arity: 0,
        is_macro: false,
        is_private: false,
        variadic: false,
        span,
    })
}

/// The library function that escapes an evaluated `defstruct` field list,
/// as Elixir's `Kernel.Utils.defstruct` does.
const DEFSTRUCT_FIELDS: Evaluation = Evaluation::Escape("Kernel.Utils", "defstruct_fields");
const MACRO_ESCAPE: Evaluation = Evaluation::Escape("Macro", "escape");

/// The function a program's first process starts in.
pub(crate) const PROGRAM_ENTRY: &str = "__entry__";

/// `main/0` under the handler that renders an error nothing rescued:
///
/// ```text
/// def __entry__() do
///   try do
///     main()
///   catch
///     :error, reason -> Exception.__uncaught__(reason)
///   end
/// end
/// ```
fn build_program_entry() -> Result<FunctionForm, QuotedSourceError> {
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let meta = QuotedSourceMetadata::default();
    let reason = builder.variable(&Var::user("reason"), &meta)?;
    let exception = builder.alias(&meta, &["Exception"])?;
    let uncaught = builder.call(".", &meta, &[exception, builder.atom("__uncaught__")])?;
    let rendered = builder.call_callee(uncaught, &meta, &[reason])?;
    let caught = builder.call(
        "->",
        &meta,
        &[builder.list(&[builder.atom("error"), reason])?, rendered],
    )?;
    let clauses = builder.list(&[
        builder.keyword("do", builder.call("main", &meta, &[])?)?,
        builder.keyword("catch", builder.list(&[caught])?)?,
    ])?;
    let body = builder.call("try", &meta, &[clauses])?;
    let clause = def_clause(&builder, &meta, PROGRAM_ENTRY, &[], body)?;
    Ok(FunctionForm {
        source: builder.root(builder.list(&[clause])?)?,
        name: PROGRAM_ENTRY.to_string(),
        arity: 0,
        is_macro: false,
        is_private: false,
        variadic: false,
        span: Span::DUMMY,
    })
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
    let kind = builder.variable(&Var::user("kind"), &meta)?;
    let body = module_info_case(&builder, &meta, kind, functions, macros, builder.atom(module_name))?;
    let clause = def_clause(&builder, &meta, "__info__", &[kind], body)?;
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
                builder.atom(callable.reference.name()),
                builder.int(callable.reference.arity as i64),
            ])
        })
        .collect::<Result<Vec<_>, _>>()?;
    builder.list(&pairs)
}

/// The function a `defstruct` gives its module.
const STRUCT_FUNCTION: &str = "__struct__";

/// `def __struct__(), do: %__MODULE__{}`: the struct the module declares, each
/// field at its default.
fn build_struct_function(span: Span) -> Result<FunctionForm, QuotedSourceError> {
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let meta = QuotedSourceMetadata::default();
    let module = builder.user_variable("__MODULE__", &meta)?;
    let fields = builder.call("%{}", &meta, &[])?;
    let body = builder.call("%", &meta, &[module, fields])?;
    let clause = def_clause(&builder, &meta, STRUCT_FUNCTION, &[], body)?;
    Ok(FunctionForm {
        source: builder.root(builder.list(&[clause])?)?,
        name: STRUCT_FUNCTION.to_string(),
        arity: 0,
        is_macro: false,
        is_private: false,
        variadic: false,
        span,
    })
}

fn def_clause(
    builder: &super::source::QuotedSourceBuilder,
    meta: &QuotedSourceMetadata,
    name: &str,
    params: &[AnyValueRef],
    body: AnyValueRef,
) -> Result<AnyValueRef, QuotedSourceError> {
    let head = builder.call(name, meta, params)?;
    let do_kw = builder.keyword("do", body)?;
    let kw = builder.list(&[do_kw])?;
    builder.call("def", meta, &[head, kw])
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
        module_info_match_clause(builder, meta, builder.variable(&Var::user("_"), meta)?, builder.nil())?,
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

fn defined_again(function: &FunctionForm, first: &FunctionForm) -> Diagnostic {
    Diagnostic::error(
        codes::RESOLVE_DUPLICATE_FUNCTION,
        format!("`{}/{}` is already defined", function.name, function.arity),
        function.span,
    )
    .with_secondary(first.span, "first defined here")
    .with_help("`defoverridable` after the first definition lets a later one replace it")
}

fn overridden_as_another_kind(function: &FunctionForm, replaced: &FunctionForm) -> Diagnostic {
    let (was, now) = if replaced.is_macro {
        ("macro", "a function")
    } else {
        ("function", "a macro")
    };
    Diagnostic::error(
        codes::RESOLVE_OVERRIDABLE,
        format!("cannot override {was} `{}/{}` as {now}", function.name, function.arity),
        function.span,
    )
    .with_secondary(replaced.span, "the definition it would replace")
}

fn declared_callable_kind(is_macro: bool) -> DeclaredCallableKind {
    if is_macro {
        DeclaredCallableKind::Macro
    } else {
        DeclaredCallableKind::Function
    }
}

struct FunctionPublication {
    function: FunctionId,
    callable: Option<ModuleInterfaceCallable>,
    /// Whether this walk changed `function`'s source. Callers fold this into
    /// their job's `FactKey::FunctionSource(function)` output/changed pair, so
    /// a re-scope that supersedes a body reaches every consumer through the
    /// standing changed-revision path rather than a manual enqueue.
    source_changed: bool,
}

fn publish_function_source(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    source_owner: SourceOwner,
    function_module: ModuleId,
    owner_module: ModuleId,
    namespace: Namespace,
    function: &FunctionForm,
    export_public: bool,
) -> FunctionPublication {
    let function_id = world.reference_declared_callable(
        function_module,
        function.name.clone(),
        function.arity,
        declared_callable_kind(function.is_macro),
    );
    // The walk notes the source as it reaches the definition, so the fact is
    // this walk's own conclusion. Noting a source is not body work: the
    // expansion, surface and lowering below it stay pulled by consumers, and a
    // function the program never reaches goes no further than here.
    let source = FunctionSource {
        owner: source_owner,
        owner_module,
        namespace,
        capture_params: Vec::new(),
        variadic: function.variadic,
        body: FunctionBody::Declared(function.source.clone()),
    };
    let source_changed =
        super::drive::ExecutionContext::new(world, tel).note_function_source(function_id, source.clone());
    if source_changed {
        emit_compiler_service_define(world, tel, &function_id, &source);
    }

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
    FunctionPublication {
        function: function_id,
        callable,
        source_changed,
    }
}

fn emit_compiler_service_define(
    world: &World,
    tel: &impl crate::telemetry::Telemetry,
    function: &FunctionId,
    source: &FunctionSource,
) {
    tel.raw_event3(
        &["fz", "compiler2", "compiler_service", "define"],
        world,
        function,
        source,
    );
}

/// What a declaration's type expressions refer to: the named types its
/// consumer waits on (`TypeDefined`), and the modules its `%Mod{...}` records
/// name (`StructDefined`).
#[derive(Default)]
struct TypeReferences {
    types: Vec<TypeName>,
    structs: Vec<ModuleId>,
}

/// Walks a parsed type expression, collecting what it refers to and noting
/// where each reference is written, so a name that never resolves is
/// reported under it. Builtins, free type variables and unresolvable bare
/// names are not references: resolution decides them, under their own
/// spans. A `%Mod{...}` record also obliges `Mod` to be a struct with the
/// fields it names, from `requester` (the enclosing declaration).
fn collect_type_references(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    scope: Namespace,
    expr: &TypeExpr,
    requester: &InterfaceRequester,
    refs: &mut TypeReferences,
) -> Result<(), FatalError> {
    match expr {
        TypeExpr::Name { path, args, span } => {
            if let Some(type_name) = world.reference_type(scope, path, args.len()) {
                let written = InterfaceRequester {
                    span: *span,
                    ..requester.clone()
                };
                if path.len() > 1 {
                    world.note_module_reference_expectation(type_name.module, written.clone());
                }
                world.note_type_reference(&type_name, written.span);
                refs.types.push(type_name);
            }
            for arg in args {
                collect_type_references(world, tel, scope, arg, requester, refs)?;
            }
        }
        TypeExpr::List(inner) => collect_type_references(world, tel, scope, inner, requester, refs)?,
        TypeExpr::Tuple(elems) | TypeExpr::Union(elems) => {
            for elem in elems {
                collect_type_references(world, tel, scope, elem, requester, refs)?;
            }
        }
        TypeExpr::Arrow { params, result } => {
            for param in params {
                collect_type_references(world, tel, scope, param, requester, refs)?;
            }
            collect_type_references(world, tel, scope, result, requester, refs)?;
        }
        TypeExpr::StructRecord { module, span, fields } => {
            let module_name = ModuleName::from_segments(module.clone());
            let module_id = world.resolve_module_name(scope, &module_name);
            refs.structs.push(module_id);
            world.note_struct_reference_expectation(
                module_id,
                InterfaceRequester {
                    span: *span,
                    ..requester.clone()
                },
            );
            for (field, value) in fields {
                super::drive::ExecutionContext::new(world, tel).note_struct_field_expectation(
                    module_id,
                    field.clone(),
                    requester.clone(),
                )?;
                collect_type_references(world, tel, scope, value, requester, refs)?;
            }
        }
        TypeExpr::Map(pairs) => {
            for pair in pairs {
                collect_type_references(world, tel, scope, &pair.key, requester, refs)?;
                collect_type_references(world, tel, scope, &pair.value, requester, refs)?;
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
    Ok(())
}

/// Walks every type-position of a spec: each parameter, the result, and each
/// constraint bound.
fn collect_spec_references(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    scope: Namespace,
    spec: &SpecDecl,
    owner: SourceOwner,
    module: ModuleId,
    refs: &mut TypeReferences,
) -> Result<(), FatalError> {
    for body in spec
        .param_body_tokens
        .iter()
        .chain(std::iter::once(&spec.result_body_tokens))
        .chain(spec.bounds().map(|(_, bound)| bound))
    {
        collect_body_references(world, tel, scope, body, owner, module, refs)?;
    }
    Ok(())
}

/// Parses one type-expression body of a function's declaration and walks it,
/// from the function's `owner`/`module`, at the body's own span.
fn collect_body_references(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    scope: Namespace,
    body: &TypeExprBody,
    owner: SourceOwner,
    module: ModuleId,
    refs: &mut TypeReferences,
) -> Result<(), FatalError> {
    if body.0.is_empty() {
        return Ok(());
    }
    let expr = parse_type_expr(&body.0).map_err(|error| {
        emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::RESOLVE_TYPE_ALIAS,
                format!("compiler2 could not parse a type expression: {}", error.msg),
                error.span,
            ),
        )
    })?;
    let requester = InterfaceRequester {
        owner,
        module,
        span: type_expr_body_span(body),
    };
    collect_type_references(world, tel, scope, &expr, &requester, refs)
}

fn note_protocol_domain_type(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    name: TypeName,
    namespace: Namespace,
    params: Vec<String>,
) {
    super::drive::ExecutionContext::new(world, tel).note_type_decl(
        &name,
        NotedTypeDecl {
            params,
            body: TypeDefBody {
                kind: NominalKind::ProtocolDomain,
                inner: TypeExpr::Wildcard,
            },
            namespace,
            span: Span::DUMMY,
        },
    );
    super::drive::ExecutionContext::new(world, tel).record_type_def_refs(&name, Vec::new());
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

fn bind_callable(world: &mut World, scope: Namespace, callable: &ModuleInterfaceCallable) -> Namespace {
    world.bind_namespace(
        scope,
        callable.reference.name().to_string(),
        callable.namespace_symbol(),
    )
}

/// The namespace binding a module declaration makes in the scope that
/// declares it, as Elixir's `defmodule` does: a single-segment name binds
/// itself to the declared module; a dotted name declared at the root binds
/// nothing; a dotted name nested in a module binds its first segment to the
/// parent's child of that segment, so `H.T.me()` inside `M` reaches `M.H.T`.
fn declared_module_binding(
    world: &mut World,
    parent: ModuleId,
    name: &ModuleName,
    declared: ModuleId,
) -> Option<(String, ModuleId)> {
    if name.is_bare_atom() {
        return None;
    }
    let first = name.segments().first()?.clone();
    if name.segments().len() == 1 {
        return Some((first, declared));
    }
    if parent.is_global() {
        return None;
    }
    let first_module = world.reference_child_module(parent, &first);
    Some((first, first_module))
}

fn bind_declared_module(
    world: &mut World,
    namespace: Namespace,
    parent: ModuleId,
    name: &ModuleName,
    declared: ModuleId,
) -> Namespace {
    match declared_module_binding(world, parent, name, declared) {
        Some((local, module)) => world.bind_namespace(namespace, local, NamespaceSymbol::Module(module)),
        None => namespace,
    }
}

fn reference_declared_module(world: &mut World, parent: ModuleId, name: &ModuleName) -> ModuleId {
    let name = match world.module_name(parent) {
        Some(parent) if !name.is_bare_atom() => {
            ModuleName::from_segments(parent.segments().iter().chain(name.segments()).cloned().collect())
        }
        _ => name.clone(),
    };
    world.reference_module(name)
}

#[cfg(test)]
#[path = "source_publish_test.rs"]
mod source_publish_test;
