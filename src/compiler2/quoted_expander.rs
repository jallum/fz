use std::collections::HashSet;

use fz_runtime::any_value::{AnyValueRef, ValueKind};

use crate::compiler::source::Span;
use crate::diag::driver::emit_through;
use crate::diag::{Diagnostic, codes};
use crate::telemetry::opaque_debug;
use crate::{measurements, metadata};

use super::code::CodeId;
use super::drive::{FactKey, Job, JobEffects};
use super::identity::{FunctionId, ModuleId};
use super::namespace::NamespaceSymbol;
use super::quoted_surface::{
    MacroCallForm, ScopeForm, ScopeSurface, SurfaceSourceContext, is_scope_definition_head,
    read_compiler_fragment_surface,
};
use super::scope::ScopeSnapshot;
use super::source::{QuotedAstNode, QuotedLexicalContextKind, QuotedSourceCursor, QuotedSourceError, QuotedSourceRoot};
use super::source_sugar::rewrite_source_sugar;
use super::world::World;

pub(crate) const MAX_MACRO_EXPANSION_DEPTH: usize = 64;

pub(crate) enum ExpandedRoot {
    Complete(QuotedSourceRoot),
    Blocked(JobEffects),
}

pub(crate) enum ExpandedValue {
    Complete(AnyValueRef),
    Blocked(JobEffects),
}

pub(crate) enum ExpandedScopeFragment {
    Complete(ScopeSurface),
    Blocked(JobEffects),
}

pub(crate) trait QuotedExpansionCtx<'tel> {
    fn world(&mut self) -> &mut World<'tel>;
    fn current_module(&self) -> ModuleId;
    fn required_remote_macros(&self) -> &HashSet<FunctionId>;
    fn note_read(&mut self, fact: FactKey);
    fn lookup_current_module_macro(&mut self, scope: ScopeSnapshot, name: &str, arity: usize) -> Option<FunctionId>;
    fn wait_for_callable_module_interface(&mut self, function: FunctionId) -> JobEffects {
        let world = self.world();
        let module = world.function_module(function);
        let follow_up = if world.module_has_source_state(module) || world.is_runtime_module(module) {
            Job::DefineModule(module)
        } else {
            Job::DefineModuleInterface(module)
        };
        JobEffects::wait_on_current(FactKey::ModuleInterface(module), [follow_up])
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
                self.world(),
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    format!("compiler2 macro expansion exceeded depth budget {MAX_MACRO_EXPANSION_DEPTH}"),
                    Span::DUMMY,
                ),
            ));
        }

        if let Some(node) = cursor.ast_node().map_err(|error| {
            emit_internal_surface_error(self.world(), format!("quoted expansion read failed: {error}"))
        })? {
            if let Some(rewritten) = rewrite_source_sugar(owner, &node).map_err(|error| {
                emit_internal_surface_error(self.world(), format!("source sugar rewrite failed: {error}"))
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
                emit_internal_surface_error(self.world(), format!("quoted AST rebuild failed: {error}"))
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
            emit_internal_surface_error(self.world(), format!("quoted call arg read failed: {error}"))
        })?;
        if is_compiler_define_call(node, &args).map_err(|error| {
            emit_internal_surface_error(
                self.world(),
                format!("quoted compiler-service detection failed: {error}"),
            )
        })? {
            return Ok(Some(ExpandedValue::Complete(cursor.root())));
        }

        if let Some(result) = self.expand_remote_ast_call(owner, node, scope, depth, cursor.root(), &args)? {
            return Ok(Some(result));
        }

        let Ok(head) = node.head.atom_name() else {
            return Ok(None);
        };
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
                return Ok(Some(ExpandedValue::Blocked(
                    self.wait_for_callable_module_interface(function),
                )));
            }
            NamespaceSymbol::Function(_) | NamespaceSymbol::Module(_) | NamespaceSymbol::Type(_) => return Ok(None),
        };
        self.expand_macro_invocation(owner, cursor.root(), function, scope, depth, &args)
            .map(Some)
    }

    fn expand_remote_ast_call(
        &mut self,
        owner: &QuotedSourceRoot,
        node: &QuotedAstNode,
        scope: ScopeSnapshot,
        depth: usize,
        input_root: AnyValueRef,
        args: &[QuotedSourceCursor],
    ) -> Result<Option<ExpandedValue>, super::scheduler::FatalError> {
        let Some(head_node) = node.head.ast_node().map_err(|error| {
            emit_internal_surface_error(self.world(), format!("quoted remote call read failed: {error}"))
        })?
        else {
            return Ok(None);
        };
        if head_node.head.atom_name().as_deref() != Ok(".") {
            return Ok(None);
        }
        let target = head_node.tail.list_items().map_err(|error| {
            emit_internal_surface_error(self.world(), format!("quoted remote target read failed: {error}"))
        })?;
        let [module_cursor, function_cursor] = target.as_slice() else {
            return Ok(None);
        };
        let module_path = match alias_path(module_cursor) {
            Ok(path) => path,
            Err(_) => return Ok(None),
        };
        let function_name = function_cursor.atom_name().map_err(|error| {
            emit_internal_surface_error(
                self.world(),
                format!("quoted remote function name read failed: {error}"),
            )
        })?;
        let module = {
            let world = self.world();
            world.lookup_module_path(scope.namespace(), &module_path.join("."))
        };
        let Some(module) = module else {
            return Ok(None);
        };
        if module == self.current_module() {
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
        let module_defined = self.world().module_defined_revision(module);
        if module_defined.is_none() {
            if self.world().is_runtime_module(module) {
                return Ok(None);
            }
            let follow_up = if module.is_global() {
                Vec::new()
            } else {
                vec![Job::DefineModule(module)]
            };
            return Ok(Some(ExpandedValue::Blocked(JobEffects::wait_on_current(
                FactKey::ModuleDefined(module),
                follow_up,
            ))));
        }
        self.note_read(FactKey::ModuleDefined(module));
        let function = {
            let world = self.world();
            match world.lookup_module_callable(module, &function_name, args.len()) {
                Some(NamespaceSymbol::Macro(function)) => Some(function),
                Some(NamespaceSymbol::Callable(function)) => {
                    return Ok(Some(ExpandedValue::Blocked(
                        self.wait_for_callable_module_interface(function),
                    )));
                }
                _ => None,
            }
        };
        let Some(function) = function else {
            return Ok(None);
        };
        if !self.required_remote_macros().contains(&function) {
            return Err(remote_macro_not_required(
                self.world(),
                &function_name,
                args.len(),
                &module_path,
            ));
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
    ) -> Result<Option<ExpandedValue>, super::scheduler::FatalError> {
        let Some(function) = self.lookup_current_module_macro(scope, function_name, args.len()) else {
            return Ok(None);
        };
        if !self.required_remote_macros().contains(&function) {
            return Err(remote_macro_not_required(
                self.world(),
                function_name,
                args.len(),
                module_path,
            ));
        }
        self.expand_macro_invocation(owner, input_root, function, scope, depth, args)
            .map(Some)
    }

    fn expand_macro_invocation(
        &mut self,
        owner: &QuotedSourceRoot,
        input_root: AnyValueRef,
        function: FunctionId,
        scope: ScopeSnapshot,
        depth: usize,
        args: &[QuotedSourceCursor],
    ) -> Result<ExpandedValue, super::scheduler::FatalError> {
        let macro_fact = FactKey::MacroExecutable(function);
        if self.world().fact_revision(macro_fact.clone()).is_none() {
            return Ok(ExpandedValue::Blocked(JobEffects::wait_on_current(
                macro_fact,
                [Job::BuildMacroExecutable(function)],
            )));
        }
        self.note_read(macro_fact);

        let builder = owner.builder();
        let caller = self
            .world()
            .project_env_value(&builder, scope, QuotedLexicalContextKind::Caller)
            .map_err(|error| {
                emit_internal_surface_error(self.world(), format!("__ENV__ projection failed: {error}"))
            })?;
        let arg_roots = args.iter().map(QuotedSourceCursor::root).collect::<Vec<_>>();
        let expanded = self
            .world()
            .run_macro_on_source(function, owner, caller, &arg_roots)
            .map_err(|error| {
                emit_job_diagnostic(
                    self.world(),
                    Diagnostic::error(codes::LOWER_UNSUPPORTED, error, Span::DUMMY),
                )
            })?;
        emit_macro_expanded(self.world(), function, owner, input_root, &expanded, depth, args.len());
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
            emit_internal_surface_error(self.world(), format!("quoted list expansion failed: {error}"))
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
            emit_internal_surface_error(self.world(), format!("quoted list rebuild failed: {error}"))
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
            emit_internal_surface_error(self.world(), format!("quoted tuple expansion failed: {error}"))
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
            emit_internal_surface_error(self.world(), format!("quoted tuple rebuild failed: {error}"))
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
            emit_internal_surface_error(self.world(), format!("quoted map expansion failed: {error}"))
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
            emit_internal_surface_error(self.world(), format!("quoted map rebuild failed: {error}"))
        })?;
        Ok(ExpandedValue::Complete(root))
    }
}

pub(crate) fn alias_path(cursor: &QuotedSourceCursor) -> Result<Vec<String>, QuotedSourceError> {
    let Some(node) = cursor.ast_node()? else {
        return Err(QuotedSourceError::new("expected quoted module alias"));
    };
    if node.head.atom_name()? != "__aliases__" {
        return Err(QuotedSourceError::new("expected quoted module alias"));
    }
    node.tail.list_atom_names()
}

pub(crate) fn is_list_like(cursor: &QuotedSourceCursor) -> bool {
    cursor.root().is_empty_list() || cursor.root().tag() == ValueKind::LIST
}

pub(crate) fn expand_item_macro_fragment<'tel, C: QuotedExpansionCtx<'tel>>(
    ctx: &mut C,
    code_id: CodeId,
    macro_call: &MacroCallForm,
    scope: ScopeSnapshot,
) -> Result<ExpandedScopeFragment, super::scheduler::FatalError> {
    let owner = &macro_call.source;
    let invocation = item_macro_invocation(ctx.world(), owner, scope, macro_call.span)?;
    let result = if let Some(node) = invocation.node.as_ref() {
        ctx.expand_ast_call(owner, &owner.cursor(), node, scope, 0)?
    } else {
        ctx.expand_macro_invocation(
            owner,
            invocation.input_root,
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
            ctx.world(),
            &invocation.display_name,
            macro_call.span,
        ));
    };
    let expanded = match result {
        ExpandedValue::Complete(root) => item_macro_fragment_root(ctx.world(), &owner.subroot(root))?,
        ExpandedValue::Blocked(effects) => return Ok(ExpandedScopeFragment::Blocked(effects)),
    };
    let surface = read_compiler_fragment_root(ctx.world(), code_id, &expanded, "item macro expanded source")?;
    if surface.forms.iter().any(|form| matches!(form, ScopeForm::MacroCall(_))) {
        return Err(emit_job_diagnostic(
            ctx.world(),
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
    world: &World<'_>,
    root: &QuotedSourceRoot,
) -> Result<QuotedSourceRoot, super::scheduler::FatalError> {
    if root.root().tag() == ValueKind::LIST {
        return Ok(root.clone());
    }
    root.interned_list_subroot(&[root.root()]).map_err(|error| {
        emit_internal_surface_error(world, format!("item macro fragment root wrapping failed: {error}"))
    })
}

struct ItemMacroInvocation {
    function: Option<FunctionId>,
    args: Vec<QuotedSourceCursor>,
    input_root: AnyValueRef,
    display_name: String,
    node: Option<QuotedAstNode>,
}

fn item_macro_invocation(
    world: &mut World<'_>,
    owner: &QuotedSourceRoot,
    scope: ScopeSnapshot,
    span: Span,
) -> Result<ItemMacroInvocation, super::scheduler::FatalError> {
    let cursor = owner.cursor();
    if let Some(node) = cursor
        .ast_node()
        .map_err(|error| emit_internal_surface_error(world, format!("item macro source read failed: {error}")))?
    {
        if let Ok(head) = node.head.atom_name()
            && is_scope_definition_head(&head)
        {
            let args = node
                .tail
                .list_items()
                .map_err(|error| emit_internal_surface_error(world, format!("item macro arg read failed: {error}")))?;
            let Some(symbol) = world.lookup_callable_namespace(scope.namespace(), &head, args.len()) else {
                return Err(item_macro_not_defmacro(world, &head, span));
            };
            if let NamespaceSymbol::Callable(_function) = symbol {
                return Ok(ItemMacroInvocation {
                    function: None,
                    args: Vec::new(),
                    input_root: cursor.root(),
                    display_name: head,
                    node: Some(node),
                });
            }
            let NamespaceSymbol::Macro(function) = symbol else {
                return Err(item_macro_not_defmacro(world, &head, span));
            };
            return Ok(ItemMacroInvocation {
                function: Some(function),
                args,
                input_root: cursor.root(),
                display_name: head,
                node: None,
            });
        }
        return Ok(ItemMacroInvocation {
            function: None,
            args: Vec::new(),
            input_root: cursor.root(),
            display_name: item_macro_display_name(&node),
            node: Some(node),
        });
    }

    let items = cursor
        .list_items()
        .map_err(|error| emit_internal_surface_error(world, format!("grouped item macro read failed: {error}")))?;
    let mut display_name = "item".to_string();
    for item in items {
        let Some(node) = item.ast_node().map_err(|error| {
            emit_internal_surface_error(world, format!("grouped item macro item read failed: {error}"))
        })?
        else {
            return Err(item_macro_not_defmacro(world, "item", span));
        };
        let Ok(head) = node.head.atom_name() else {
            return Err(item_macro_not_defmacro(world, "item", span));
        };
        if head.starts_with('@') {
            continue;
        }
        display_name = head.clone();
        let Some(symbol) = world.lookup_callable_namespace(scope.namespace(), &head, 1) else {
            return Err(item_macro_not_defmacro(world, &display_name, span));
        };
        if let NamespaceSymbol::Callable(_function) = symbol {
            return Ok(ItemMacroInvocation {
                function: None,
                args: Vec::new(),
                input_root: owner.root(),
                display_name,
                node: Some(node),
            });
        }
        let NamespaceSymbol::Macro(function) = symbol else {
            return Err(item_macro_not_defmacro(world, &display_name, span));
        };
        return Ok(ItemMacroInvocation {
            function: Some(function),
            args: vec![owner.cursor()],
            input_root: owner.root(),
            display_name,
            node: None,
        });
    }

    Err(item_macro_not_defmacro(world, &display_name, span))
}

pub(crate) fn read_compiler_fragment_root(
    world: &World<'_>,
    code_id: CodeId,
    root: &QuotedSourceRoot,
    context: &str,
) -> Result<ScopeSurface, super::scheduler::FatalError> {
    read_surface_root_with(world, code_id, root, context, read_compiler_fragment_surface)
}

fn read_surface_root_with(
    world: &World<'_>,
    code_id: CodeId,
    root: &QuotedSourceRoot,
    context: &str,
    read: fn(&QuotedSourceRoot, &SurfaceSourceContext<'_>) -> Result<ScopeSurface, QuotedSourceError>,
) -> Result<ScopeSurface, super::scheduler::FatalError> {
    let code_text = world.code_text(code_id).to_owned();
    let ctx = SurfaceSourceContext::new(code_id, &code_text);
    let source = if root.root().is_empty_list() || root.root().tag() == ValueKind::LIST {
        root.clone()
    } else {
        root.interned_list_subroot(&[root.root()])
            .map_err(|error| emit_internal_surface_error(world, format!("{context} wrapper failed: {error}")))?
    };
    read(&source, &ctx).map_err(|error| emit_internal_surface_error(world, format!("{context} read failed: {error}")))
}

pub(crate) fn emit_macro_expanded(
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

pub(crate) fn emit_job_diagnostic(world: &World<'_>, diagnostic: Diagnostic) -> super::scheduler::FatalError {
    emit_through(world.tel(), None, std::slice::from_ref(&diagnostic));
    super::scheduler::FatalError
}

pub(crate) fn emit_internal_surface_error(world: &World<'_>, message: String) -> super::scheduler::FatalError {
    emit_job_diagnostic(
        world,
        Diagnostic::error(codes::INTERNAL_POST_RESOLUTION_LEFTOVER, message, Span::DUMMY),
    )
}

fn remote_macro_not_required(
    world: &World<'_>,
    function_name: &str,
    arity: usize,
    module_path: &[String],
) -> super::scheduler::FatalError {
    let module_name = module_path.join(".");
    emit_job_diagnostic(
        world,
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

fn item_macro_not_defmacro(world: &World<'_>, name: &str, span: Span) -> super::scheduler::FatalError {
    emit_job_diagnostic(
        world,
        Diagnostic::error(
            codes::MACRO_NOT_A_DEFMACRO,
            format!("item-level call `{name}(...)` is not a defmacro"),
            span,
        ),
    )
}

fn item_macro_display_name(node: &QuotedAstNode) -> String {
    if let Ok(function) = node.head.atom_name() {
        return function;
    }
    let Ok(Some(head_node)) = node.head.ast_node() else {
        return "item".to_string();
    };
    let Ok(parts) = head_node.tail.list_items() else {
        return "item".to_string();
    };
    let [module, function] = parts.as_slice() else {
        return "item".to_string();
    };
    if head_node.head.atom_name().as_deref() == Ok(".")
        && let Ok(path) = alias_path(module)
        && let Ok(function) = function.atom_name()
    {
        return format!("{}.{}", path.join("."), function);
    }
    "item".to_string()
}

fn is_compiler_define_call(node: &QuotedAstNode, args: &[QuotedSourceCursor]) -> Result<bool, QuotedSourceError> {
    if args.len() != 2 {
        return Ok(false);
    }
    let Some(callee) = node.head.ast_node()? else {
        return Ok(false);
    };
    if callee.head.atom_name()? != "." {
        return Ok(false);
    }
    let target = callee.tail.list_items()?;
    let [module_cursor, function_cursor] = target.as_slice() else {
        return Ok(false);
    };
    Ok(alias_path(module_cursor)
        .map(|path| path == ["Fz".to_string(), "Compiler".to_string()])
        .unwrap_or(false)
        && function_cursor.atom_name().as_deref() == Ok("define"))
}
