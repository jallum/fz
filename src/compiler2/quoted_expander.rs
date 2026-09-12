use std::collections::HashSet;

use fz_runtime::any_value::{AnyValueRef, ValueKind};

use crate::diag::driver::emit_through;
use crate::diag::{Diagnostic, codes};
use crate::modules::identity::ModuleName;
use crate::source::{SourceMap, Span};
use crate::telemetry::TelemetryExt as _;

use super::drive::{FactKey, JobEffects, ProductAddress};
use super::identity::{FunctionId, ModuleId};
use super::namespace::NamespaceSymbol;
use super::pull::{ProductKey, ProductSessions, ProductValue};
use super::quoted_surface::{
    MacroCallForm, ScopeForm, ScopeSurface, is_scope_definition_head, read_compiler_fragment_surface,
};
use super::scope::ScopeSnapshot;
use super::source::{QuotedAstNode, QuotedLexicalContextKind, QuotedSourceCursor, QuotedSourceError, QuotedSourceRoot};
use super::source_sugar::rewrite_source_sugar;
use super::world::World;

pub(crate) const MAX_MACRO_EXPANSION_DEPTH: usize = 64;

pub(crate) enum ExpandedRoot {
    Complete(QuotedSourceRoot),
    Blocked(Box<JobEffects>),
}

pub(crate) enum ExpandedValue {
    Complete(AnyValueRef),
    Blocked(Box<JobEffects>),
}

pub(crate) enum ExpandedScopeFragment {
    Complete(ScopeSurface),
    Blocked(Box<JobEffects>),
}

pub(crate) trait QuotedExpansionCtx {
    type Telemetry: crate::telemetry::Telemetry;
    fn world(&mut self) -> &mut World;
    fn telemetry(&self) -> &Self::Telemetry;
    fn split(&mut self) -> (&mut World, &Self::Telemetry);
    fn current_module(&self) -> ModuleId;
    fn required_remote_macros(&self) -> &HashSet<FunctionId>;
    fn note_read(&mut self, fact: FactKey);
    fn products(&self) -> Option<&ProductSessions>;
    fn note_product_read(&mut self, product: ProductAddress);

    /// The source-visible caller scope for macro execution and memoization.
    /// Expansion may layer transient compiler bindings onto `scope`; those
    /// bindings must not change `__CALLER__` or the identity of a call site.
    fn macro_caller_scope(&self, scope: ScopeSnapshot) -> ScopeSnapshot {
        scope
    }
    fn lookup_current_module_macro(&mut self, scope: ScopeSnapshot, name: &str, arity: usize) -> Option<FunctionId>;
    fn wait_for_callable_module_interface(&mut self, function: FunctionId) -> JobEffects {
        let world = self.world();
        let module = world.function_module(function);
        // `FactKey::ModuleInterface`'s producer is demand-selected in
        // `World::demand_fact_producer` (Job::DefineModule when the module has
        // source state or is a runtime module, else Job::DefineModuleInterface)
        // -- the same selection this site used to push directly.
        JobEffects::wait_on_current(FactKey::ModuleInterface(module))
    }

    fn expand_root(
        &mut self,
        root: QuotedSourceRoot,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedRoot, super::scheduler::FatalError> {
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
    ) -> Result<ExpandedValue, super::scheduler::FatalError> {
        if depth > MAX_MACRO_EXPANSION_DEPTH {
            return Err(emit_job_diagnostic(
                self.telemetry(),
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    format!("compiler2 macro expansion exceeded depth budget {MAX_MACRO_EXPANSION_DEPTH}"),
                    Span::DUMMY,
                ),
            ));
        }

        let source_map = self.world().source_map();
        if let Some(node) = cursor.ast_node(&source_map.borrow()).map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted expansion read failed: {error}"))
        })? {
            if node
                .meta
                .module_denotation()
                .map_err(|error| {
                    emit_internal_surface_error(
                        self.telemetry(),
                        format!("quoted module reference read failed: {error}"),
                    )
                })?
                .is_some()
            {
                return Ok(ExpandedValue::Complete(cursor.root()));
            }
            if let Some(name) = splice_candidate_name(&node).map_err(|error| {
                emit_internal_surface_error(
                    self.telemetry(),
                    format!("quoted splice candidate read failed: {error}"),
                )
            })? && let Some(NamespaceSymbol::Splice(snippet)) =
                self.world().lookup_namespace(scope.namespace(), &name)
            {
                return Ok(ExpandedValue::Complete(snippet.root()));
            }
            if let Some(rewritten) =
                rewrite_source_sugar(owner, cursor.root(), &node, &source_map.borrow()).map_err(|error| {
                    emit_internal_surface_error(self.telemetry(), format!("source sugar rewrite failed: {error}"))
                })?
            {
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
        node: &QuotedAstNode,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, super::scheduler::FatalError> {
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
            .map_err(|error| {
                emit_internal_surface_error(self.telemetry(), format!("quoted AST rebuild failed: {error}"))
            })?;
        Ok(ExpandedValue::Complete(rebuilt))
    }

    fn expand_ast_call(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        node: &QuotedAstNode,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<Option<ExpandedValue>, super::scheduler::FatalError> {
        if !is_list_like(&node.tail) {
            return Ok(None);
        }
        let args = node.tail.list_items().map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted call arg read failed: {error}"))
        })?;
        let source_map = self.world().source_map();
        if is_compiler_define_call(node, &args, &source_map.borrow()).map_err(|error| {
            emit_internal_surface_error(
                self.telemetry(),
                format!("quoted compiler-service detection failed: {error}"),
            )
        })? {
            return Ok(Some(ExpandedValue::Complete(cursor.root())));
        }

        let invocation = owner.subroot(cursor.root());
        if let Some(result) = self.expand_remote_ast_call(owner, &invocation, node, scope, depth, &args)? {
            return Ok(Some(result));
        }

        if node.head.root().tag() != ValueKind::ATOM {
            return Ok(None);
        }
        let head = node.head.atom_name().map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted call head read failed: {error}"))
        })?;
        if head == "quote" {
            return Ok(Some(ExpandedValue::Complete(cursor.root())));
        }
        if is_scope_definition_head(&head) {
            return Ok(None);
        }
        let symbol = {
            let world = self.world();
            world.lookup_callable_namespace(scope.namespace(), &head, args.len())
        };
        let Some(symbol) = symbol else {
            return Ok(None);
        };
        let function = match symbol {
            NamespaceSymbol::Macro(function) => function,
            NamespaceSymbol::Callable(function) => {
                return Ok(Some(ExpandedValue::Blocked(Box::new(
                    self.wait_for_callable_module_interface(function),
                ))));
            }
            NamespaceSymbol::Function(_)
            | NamespaceSymbol::Module(_)
            | NamespaceSymbol::Type(_)
            | NamespaceSymbol::Splice(_) => return Ok(None),
        };
        self.expand_macro_invocation(owner, invocation, function, scope, depth, &args)
            .map(Some)
    }

    fn expand_remote_ast_call(
        &mut self,
        owner: &QuotedSourceRoot,
        invocation: &QuotedSourceRoot,
        node: &QuotedAstNode,
        scope: ScopeSnapshot,
        depth: usize,
        args: &[QuotedSourceCursor],
    ) -> Result<Option<ExpandedValue>, super::scheduler::FatalError> {
        let source_map = self.world().source_map();
        let Some(head_node) = node.head.ast_node(&source_map.borrow()).map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted remote call read failed: {error}"))
        })?
        else {
            return Ok(None);
        };
        let call_span = node.span.unwrap_or(Span::DUMMY);
        if !is_remote_dot_callee(&head_node).map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted remote callee read failed: {error}"))
        })? {
            return Ok(None);
        }
        let target = head_node.tail.list_items().map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted remote target read failed: {error}"))
        })?;
        let [module_cursor, function_cursor] = target.as_slice() else {
            return Ok(None);
        };
        let denotation = module_cursor
            .ast_node(&source_map.borrow())
            .and_then(|node| node.map(|node| node.meta.module_denotation()).transpose())
            .map_err(|error| {
                emit_internal_surface_error(
                    self.telemetry(),
                    format!("quoted module reference read failed: {error}"),
                )
            })?
            .flatten();
        let module_path = match &denotation {
            Some(module) => module.display_segments().cloned().collect(),
            None => match alias_path(module_cursor, &source_map.borrow()).map_err(|error| {
                emit_internal_surface_error(self.telemetry(), format!("quoted remote module read failed: {error}"))
            })? {
                Some(path) => path,
                None => return Ok(None),
            },
        };
        let function_name = function_cursor.atom_name().map_err(|error| {
            emit_internal_surface_error(
                self.telemetry(),
                format!("quoted remote function name read failed: {error}"),
            )
        })?;
        let module = {
            let world = self.world();
            match denotation {
                Some(module) => Some(world.reference_module_denotation(module)),
                None => world.lookup_module_path(scope.namespace(), &ModuleName::from_segments(module_path.clone())),
            }
        };
        let Some(module) = module else {
            return Ok(None);
        };
        if module == self.current_module() {
            return self.expand_current_module_remote_ast_call(
                owner,
                invocation,
                scope,
                depth,
                args,
                &function_name,
                &module_path,
                call_span,
            );
        }
        let module_defined = self.world().module_defined_revision(module);
        if module_defined.is_none() {
            if self.world().is_runtime_module(module) {
                return Ok(None);
            }
            // `FactKey::ModuleDefined`'s sole producer arm is `Job::DefineModule`
            // (`World::demand_fact_producer`); the `is_global()` split this bare
            // wait used to make (never pushing for a global module) is defensive,
            // not reachable in practice -- `ModuleId::GLOBAL` is defined before
            // any expansion runs, so `module_defined.is_none()` is never true for
            // it here.
            return Ok(Some(ExpandedValue::Blocked(Box::new(JobEffects::wait_on_current(
                FactKey::ModuleDefined(module),
            )))));
        }
        self.note_read(FactKey::ModuleDefined(module));
        let function = {
            let world = self.world();
            match world.lookup_module_callable(module, &function_name, args.len()) {
                Some(NamespaceSymbol::Macro(function)) => Some(function),
                Some(NamespaceSymbol::Callable(function)) => {
                    return Ok(Some(ExpandedValue::Blocked(Box::new(
                        self.wait_for_callable_module_interface(function),
                    ))));
                }
                _ => None,
            }
        };
        let Some(function) = function else {
            return Ok(None);
        };
        if !self.required_remote_macros().contains(&function) {
            return Err(remote_macro_not_required(
                self.telemetry(),
                &function_name,
                args.len(),
                &module_path,
                call_span,
            ));
        }
        self.expand_macro_invocation(owner, invocation.clone(), function, scope, depth, args)
            .map(Some)
    }

    fn expand_current_module_remote_ast_call(
        &mut self,
        owner: &QuotedSourceRoot,
        invocation: &QuotedSourceRoot,
        scope: ScopeSnapshot,
        depth: usize,
        args: &[QuotedSourceCursor],
        function_name: &str,
        module_path: &[String],
        call_span: Span,
    ) -> Result<Option<ExpandedValue>, super::scheduler::FatalError> {
        let Some(function) = self.lookup_current_module_macro(scope, function_name, args.len()) else {
            return Ok(None);
        };
        if !self.required_remote_macros().contains(&function) {
            return Err(remote_macro_not_required(
                self.telemetry(),
                function_name,
                args.len(),
                module_path,
                call_span,
            ));
        }
        self.expand_macro_invocation(owner, invocation.clone(), function, scope, depth, args)
            .map(Some)
    }

    fn expand_macro_invocation(
        &mut self,
        owner: &QuotedSourceRoot,
        invocation: QuotedSourceRoot,
        function: FunctionId,
        scope: ScopeSnapshot,
        depth: usize,
        args: &[QuotedSourceCursor],
    ) -> Result<ExpandedValue, super::scheduler::FatalError> {
        let definition = FactKey::FunctionDefined(function);
        if self.world().fact_revision(&definition).is_none() {
            return Ok(ExpandedValue::Blocked(Box::new(JobEffects::wait_on_current(
                definition,
            ))));
        }
        self.note_read(definition);
        let root = self.world().macro_root(function);
        let address = ProductAddress {
            root,
            key: ProductKey::RootBackendProduct(root),
        };
        let Some(ProductValue::RootBackendProduct(program)) =
            self.products().and_then(|products| products.product(&address))
        else {
            return Ok(ExpandedValue::Blocked(Box::new(JobEffects {
                product_waits: vec![address],
                ..JobEffects::default()
            })));
        };
        self.note_product_read(address);

        let caller_scope = self.macro_caller_scope(scope);
        if let Some(expanded) = self
            .world()
            .memoized_macro_expansion(function, &invocation, caller_scope, &program)
        {
            return match self.expand_root(expanded, scope, depth + 1)? {
                ExpandedRoot::Complete(root) => Ok(ExpandedValue::Complete(root.root())),
                ExpandedRoot::Blocked(effects) => Ok(ExpandedValue::Blocked(effects)),
            };
        }

        let builder = owner.builder();
        let caller = self
            .world()
            .project_env_value(&builder, caller_scope, QuotedLexicalContextKind::Caller)
            .map_err(|error| {
                emit_internal_surface_error(self.telemetry(), format!("__ENV__ projection failed: {error}"))
            })?;
        let arg_roots = args.iter().map(QuotedSourceCursor::root).collect::<Vec<_>>();
        let (world, tel) = self.split();
        let expanded = super::drive::ExecutionContext::new(world, tel)
            .run_macro_on_source(function, &program, owner, caller, &arg_roots)
            .map_err(|error| {
                emit_job_diagnostic(tel, Diagnostic::error(codes::LOWER_UNSUPPORTED, error, Span::DUMMY))
            })?;
        emit_macro_expanded(world, tel, &function, &expanded);
        world.memoize_macro_expansion(function, invocation, caller_scope, &program, expanded.clone());
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
    ) -> Result<ExpandedValue, super::scheduler::FatalError> {
        let items = cursor.list_items().map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted list expansion failed: {error}"))
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
        if !changed {
            return Ok(ExpandedValue::Complete(cursor.root()));
        }
        let root = owner.builder().list(&expanded).map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted list rebuild failed: {error}"))
        })?;
        Ok(ExpandedValue::Complete(root))
    }

    fn expand_tuple(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, super::scheduler::FatalError> {
        let items = cursor.tuple_items().map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted tuple expansion failed: {error}"))
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
        if !changed {
            return Ok(ExpandedValue::Complete(cursor.root()));
        }
        let root = owner.builder().tuple(&expanded).map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted tuple rebuild failed: {error}"))
        })?;
        Ok(ExpandedValue::Complete(root))
    }

    fn expand_map(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, super::scheduler::FatalError> {
        let entries = cursor.map_entries().map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted map expansion failed: {error}"))
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
        if !changed {
            return Ok(ExpandedValue::Complete(cursor.root()));
        }
        let root = owner.builder().map(&expanded).map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted map rebuild failed: {error}"))
        })?;
        Ok(ExpandedValue::Complete(root))
    }
}

pub(crate) fn alias_path(
    cursor: &QuotedSourceCursor,
    sources: &SourceMap,
) -> Result<Option<Vec<String>>, QuotedSourceError> {
    let Some(node) = cursor.ast_node(sources)? else {
        return Ok(None);
    };
    if node.head.root().tag() != ValueKind::ATOM || node.head.atom_name()? != "__aliases__" {
        return Ok(None);
    }
    node.tail.list_atom_names().map(Some)
}

pub(crate) fn is_list_like(cursor: &QuotedSourceCursor) -> bool {
    cursor.root().is_empty_list() || cursor.root().tag() == ValueKind::LIST
}

/// The name of a splice-candidate variable: a compiler-reserved `__`-prefixed
/// identifier (e.g. `__ENV__`), i.e. an AST node whose head atom starts with
/// `__` and whose tail is the variable context, not a call's argument list. The
/// `__` gate keeps this off the hot path for ordinary variables; a name that is
/// not actually bound to a [`NamespaceSymbol::Splice`] is left untouched.
fn splice_candidate_name(node: &QuotedAstNode) -> Result<Option<String>, QuotedSourceError> {
    if node.head.root().tag() != ValueKind::ATOM {
        return Ok(None);
    }
    let name = node.head.atom_name()?;
    Ok((name.starts_with("__") && !is_list_like(&node.tail)).then_some(name))
}

pub(crate) fn expand_item_macro_fragment<C: QuotedExpansionCtx>(
    ctx: &mut C,
    macro_call: &MacroCallForm,
    scope: ScopeSnapshot,
) -> Result<ExpandedScopeFragment, super::scheduler::FatalError> {
    let owner = &macro_call.source;
    let invocation = {
        let (world, tel) = ctx.split();
        item_macro_invocation(world, tel, owner, scope, macro_call.span)?
    };
    let result = if let Some(node) = invocation.node.as_ref() {
        ctx.expand_ast_call(owner, &owner.cursor(), node, scope, 0)?
    } else {
        ctx.expand_macro_invocation(
            owner,
            owner.clone(),
            invocation
                .function
                .expect("grouped item macro should resolve a compiler macro"),
            scope,
            0,
            &invocation.args,
        )
        .map(Some)?
    };
    let Some(result) = result else {
        return Err(item_macro_not_defmacro(
            ctx.telemetry(),
            &invocation.display_name,
            macro_call.span,
        ));
    };
    let expanded = match result {
        ExpandedValue::Complete(root) => item_macro_fragment_root(ctx.telemetry(), &owner.subroot(root))?,
        ExpandedValue::Blocked(effects) => return Ok(ExpandedScopeFragment::Blocked(effects)),
    };
    let source_map = ctx.world().source_map();
    let surface = read_compiler_fragment_root(
        ctx.telemetry(),
        &expanded,
        "item macro expanded source",
        &source_map.borrow(),
    )?;
    if surface.forms.iter().any(|form| matches!(form, ScopeForm::MacroCall(_))) {
        return Err(emit_job_diagnostic(
            ctx.telemetry(),
            Diagnostic::error(
                codes::MACRO_NOT_A_DEFMACRO,
                "item macro expansion returned a non-definition call",
                macro_call.span,
            ),
        ));
    }
    Ok(ExpandedScopeFragment::Complete(surface))
}

fn item_macro_fragment_root(
    tel: &impl crate::telemetry::Telemetry,
    root: &QuotedSourceRoot,
) -> Result<QuotedSourceRoot, super::scheduler::FatalError> {
    if root.root().tag() == ValueKind::LIST {
        return Ok(root.clone());
    }
    root.interned_list_subroot(&[root.root()])
        .map_err(|error| emit_internal_surface_error(tel, format!("item macro fragment root wrapping failed: {error}")))
}

struct ItemMacroInvocation {
    function: Option<FunctionId>,
    args: Vec<QuotedSourceCursor>,
    display_name: String,
    node: Option<QuotedAstNode>,
}

fn item_macro_invocation(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    owner: &QuotedSourceRoot,
    scope: ScopeSnapshot,
    span: Span,
) -> Result<ItemMacroInvocation, super::scheduler::FatalError> {
    let source_map = world.source_map();
    let cursor = owner.cursor();
    if let Some(node) = cursor
        .ast_node(&source_map.borrow())
        .map_err(|error| emit_internal_surface_error(tel, format!("item macro source read failed: {error}")))?
    {
        if node.head.root().tag() == ValueKind::ATOM {
            let head = node
                .head
                .atom_name()
                .map_err(|error| emit_internal_surface_error(tel, format!("item macro head read failed: {error}")))?;
            if !is_scope_definition_head(&head) {
                return Ok(ItemMacroInvocation {
                    function: None,
                    args: Vec::new(),
                    display_name: head,
                    node: Some(node),
                });
            }
            let args = node
                .tail
                .list_items()
                .map_err(|error| emit_internal_surface_error(tel, format!("item macro arg read failed: {error}")))?;
            let Some(symbol) = world.lookup_callable_namespace(scope.namespace(), &head, args.len()) else {
                return Err(item_macro_not_defmacro(tel, &head, span));
            };
            if let NamespaceSymbol::Callable(_function) = symbol {
                return Ok(ItemMacroInvocation {
                    function: None,
                    args: Vec::new(),
                    display_name: head,
                    node: Some(node),
                });
            }
            let NamespaceSymbol::Macro(function) = symbol else {
                return Err(item_macro_not_defmacro(tel, &head, span));
            };
            return Ok(ItemMacroInvocation {
                function: Some(function),
                args,
                display_name: head,
                node: None,
            });
        }
        return Ok(ItemMacroInvocation {
            function: None,
            args: Vec::new(),
            display_name: item_macro_display_name(&node, &source_map.borrow()).map_err(|error| {
                emit_internal_surface_error(tel, format!("item macro display name read failed: {error}"))
            })?,
            node: Some(node),
        });
    }

    let items = cursor
        .list_items()
        .map_err(|error| emit_internal_surface_error(tel, format!("grouped item macro read failed: {error}")))?;
    let mut display_name = "item".to_string();
    for item in items {
        let Some(node) = item.ast_node(&source_map.borrow()).map_err(|error| {
            emit_internal_surface_error(tel, format!("grouped item macro item read failed: {error}"))
        })?
        else {
            return Err(item_macro_not_defmacro(tel, "item", span));
        };
        if node.head.root().tag() != ValueKind::ATOM {
            return Err(item_macro_not_defmacro(tel, "item", span));
        }
        let head = node.head.atom_name().map_err(|error| {
            emit_internal_surface_error(tel, format!("grouped item macro head read failed: {error}"))
        })?;
        if head.starts_with('@') {
            continue;
        }
        display_name = head.clone();
        let Some(symbol) = world.lookup_callable_namespace(scope.namespace(), &head, 1) else {
            return Err(item_macro_not_defmacro(tel, &display_name, span));
        };
        if let NamespaceSymbol::Callable(_function) = symbol {
            return Ok(ItemMacroInvocation {
                function: None,
                args: Vec::new(),
                display_name,
                node: Some(node),
            });
        }
        let NamespaceSymbol::Macro(function) = symbol else {
            return Err(item_macro_not_defmacro(tel, &display_name, span));
        };
        return Ok(ItemMacroInvocation {
            function: Some(function),
            args: vec![owner.cursor()],
            display_name,
            node: None,
        });
    }

    Err(item_macro_not_defmacro(tel, &display_name, span))
}

pub(crate) fn read_compiler_fragment_root(
    tel: &impl crate::telemetry::Telemetry,
    root: &QuotedSourceRoot,
    context: &str,
    sources: &crate::source::SourceMap,
) -> Result<ScopeSurface, super::scheduler::FatalError> {
    read_surface_root_with(tel, root, context, sources, read_compiler_fragment_surface)
}

fn read_surface_root_with(
    tel: &impl crate::telemetry::Telemetry,
    root: &QuotedSourceRoot,
    context: &str,
    sources: &crate::source::SourceMap,
    read: fn(&QuotedSourceRoot, &crate::source::SourceMap) -> Result<ScopeSurface, QuotedSourceError>,
) -> Result<ScopeSurface, super::scheduler::FatalError> {
    let source = if root.root().is_empty_list() || root.root().tag() == ValueKind::LIST {
        root.clone()
    } else {
        root.interned_list_subroot(&[root.root()])
            .map_err(|error| emit_internal_surface_error(tel, format!("{context} wrapper failed: {error}")))?
    };
    read(&source, sources).map_err(|error| emit_surface_read_error(tel, &format!("{context} read failed"), &error))
}

pub(crate) fn emit_macro_expanded(
    world: &super::World,
    tel: &impl crate::telemetry::Telemetry,
    function: &FunctionId,
    output: &QuotedSourceRoot,
) {
    tel.raw_event3(&["fz", "compiler2", "macro", "expanded"], world, function, output);
}

pub(crate) fn emit_job_diagnostic(
    tel: &impl crate::telemetry::Telemetry,
    diagnostic: Diagnostic,
) -> super::scheduler::FatalError {
    emit_through(tel, std::slice::from_ref(&diagnostic));
    super::scheduler::FatalError
}

/// Route a failed surface read to the right diagnostic: a user-coded error
/// (malformed source surface) carries its own code; everything else is an
/// internal invariant failure.
pub(crate) fn emit_surface_read_error(
    tel: &impl crate::telemetry::Telemetry,
    context: &str,
    error: &super::source::QuotedSourceError,
) -> super::scheduler::FatalError {
    emit_job_diagnostic(tel, surface_read_diagnostic(context, error))
}

pub(crate) fn surface_read_diagnostic(context: &str, error: &QuotedSourceError) -> Diagnostic {
    match error.user_code() {
        Some(code) => Diagnostic::error(code, error.to_string(), error.span().unwrap_or(Span::DUMMY)),
        None => Diagnostic::error(
            codes::INTERNAL_POST_RESOLUTION_LEFTOVER,
            format!("{context}: {error}"),
            Span::DUMMY,
        ),
    }
}

pub(crate) fn emit_internal_surface_error(
    tel: &impl crate::telemetry::Telemetry,
    message: String,
) -> super::scheduler::FatalError {
    emit_job_diagnostic(
        tel,
        Diagnostic::error(codes::INTERNAL_POST_RESOLUTION_LEFTOVER, message, Span::DUMMY),
    )
}

fn remote_macro_not_required(
    tel: &impl crate::telemetry::Telemetry,
    function_name: &str,
    arity: usize,
    module_path: &[String],
    span: Span,
) -> super::scheduler::FatalError {
    let module_name = module_path.join(".");
    emit_job_diagnostic(
        tel,
        Diagnostic::error(
            codes::MACRO_NOT_REQUIRED,
            format!(
                "remote macro `{}.{}/{}` requires `require {}` before source expansion",
                module_name, function_name, arity, module_name
            ),
            span,
        ),
    )
}

fn item_macro_not_defmacro(
    tel: &impl crate::telemetry::Telemetry,
    name: &str,
    span: Span,
) -> super::scheduler::FatalError {
    let message = format!("item-level call `{name}(...)` is not a defmacro");
    emit_job_diagnostic(tel, Diagnostic::error(codes::MACRO_NOT_A_DEFMACRO, message, span))
}

fn item_macro_display_name(node: &QuotedAstNode, sources: &SourceMap) -> Result<String, QuotedSourceError> {
    if node.head.root().tag() == ValueKind::ATOM {
        return node.head.atom_name();
    }
    let Some(head_node) = node.head.ast_node(sources)? else {
        return Ok("item".to_string());
    };
    let parts = head_node.tail.list_items()?;
    let [module, function] = parts.as_slice() else {
        return Ok("item".to_string());
    };
    if head_node.head.root().tag() == ValueKind::ATOM
        && head_node.head.atom_name()? == "."
        && let Some(path) = alias_path(module, sources)?
        && function.root().tag() == ValueKind::ATOM
    {
        return Ok(format!("{}.{}", path.join("."), function.atom_name()?));
    }
    Ok("item".to_string())
}

fn is_compiler_define_call(
    node: &QuotedAstNode,
    args: &[QuotedSourceCursor],
    sources: &SourceMap,
) -> Result<bool, QuotedSourceError> {
    if args.len() != 2 {
        return Ok(false);
    }
    let Some(callee) = node.head.ast_node(sources)? else {
        return Ok(false);
    };
    if callee.head.atom_name()? != "." {
        return Ok(false);
    }
    let target = callee.tail.list_items()?;
    let [module_cursor, function_cursor] = target.as_slice() else {
        return Ok(false);
    };
    if !alias_path(module_cursor, sources)?.is_some_and(|path| path == ["Fz".to_string(), "Compiler".to_string()])
        || function_cursor.root().tag() != ValueKind::ATOM
    {
        return Ok(false);
    }
    Ok(function_cursor.atom_name()? == "define")
}

fn is_remote_dot_callee(node: &QuotedAstNode) -> Result<bool, QuotedSourceError> {
    if node.head.root().tag() != ValueKind::ATOM {
        return Ok(false);
    }
    Ok(node.head.atom_name()? == ".")
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use fz_runtime::any_value::{AnyValueRef, ValueKind};

    use super::is_remote_dot_callee;
    use crate::compiler2::{QuotedSourceHeap, QuotedSourceMetadata};
    use crate::source::SourceMap;

    #[test]
    fn remote_callee_probe_propagates_an_invalid_atom_payload() {
        let heap = Rc::new(QuotedSourceHeap::new());
        let builder = heap.builder();
        let unknown_atom_id = u64::MAX;
        let unknown_atom = AnyValueRef::from_scalar_slot(ValueKind::ATOM, &unknown_atom_id)
            .expect("stack scalar is a valid temporary atom carrier");
        let encoded = builder
            .ast_node(unknown_atom, &QuotedSourceMetadata::default(), builder.empty_list())
            .expect("builder copies the scalar into its owned heap");
        let root = builder.root(encoded).expect("quoted source root");
        let node = root
            .cursor()
            .ast_node(&SourceMap::new())
            .expect("structural read")
            .expect("AST node");

        let error = is_remote_dot_callee(&node).expect_err("remote callee probe must propagate invalid atom");
        assert!(error.to_string().contains("unknown atom id"), "{error}");
    }
}
