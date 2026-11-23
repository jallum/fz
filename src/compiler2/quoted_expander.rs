use fz_runtime::any_value::{AnyValueRef, ValueKind};

use crate::diag::{Diagnostic, codes};
use crate::modules::identity::ModuleName;
use crate::source::{SourceMap, Span};
use crate::telemetry::TelemetryExt as _;

use super::drive::{FactKey, JobEffects, ProductAddress, emit_job_diagnostic};
use super::env_projection::CallSite;
use super::identity::{FunctionId, ModuleId};
use super::jobs::is_guard_expr;
use super::module_interface::{InterfaceRequester, ReferencingCall};
use super::namespace::NamespaceSymbol;
use super::pull::{ProductKey, ProductSessions, ProductValue};
use super::quoted_function::decode_standalone_expr;
use super::quoted_surface::{MacroCallForm, ScopeSurface, is_scope_definition_head, read_compiler_fragment_surface};
use super::scope::ScopeSnapshot;
use super::source::{ListItems, QuotedAstNode, QuotedSourceCursor, QuotedSourceError, QuotedSourceRoot};
use super::source_sugar::{rewrite_guard_membership, rewrite_source_sugar};
use super::world::World;

pub(crate) const MAX_MACRO_EXPANSION_DEPTH: usize = 64;

/// Where the expansion in progress stands, as Elixir's `__CALLER__.context`
/// reports it: inside a pattern, inside a guard, or in an ordinary
/// expression. A macro may expand differently in each, as a record's
/// `rec()` builds its defaults in an expression and matches any field in a
/// pattern.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub(crate) enum ExpansionContext {
    #[default]
    Expression,
    Match,
    Guard,
}

impl ExpansionContext {
    /// The atom `__CALLER__.context` holds, `nil` for an expression.
    pub(crate) fn atom_name(self) -> Option<&'static str> {
        match self {
            ExpansionContext::Expression => None,
            ExpansionContext::Match => Some("match"),
            ExpansionContext::Guard => Some("guard"),
        }
    }
}

/// The operators whose left side is a pattern: a match, a generator, and a
/// clause.
fn binds_its_left_side(head: &str) -> bool {
    matches!(head, "=" | "<-" | "->")
}

/// The special forms one of whose sections holds `test -> body` clauses
/// rather than `pattern -> body` ones, and that section's keyword.
fn expression_clause_section(head: &str) -> Option<&'static str> {
    match head {
        "cond" => Some("do"),
        "receive" => Some("after"),
        _ => None,
    }
}

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
    /// The item's head is bound to no macro, so there is nothing to expand:
    /// the scope decides whether the item is an expression or an error.
    NotAMacro {
        display_name: String,
    },
    Blocked(Box<JobEffects>),
}

pub(crate) trait QuotedExpansionCtx {
    type Telemetry: crate::telemetry::Telemetry;
    fn world(&mut self) -> &mut World;
    fn telemetry(&self) -> &Self::Telemetry;
    fn split(&mut self) -> (&mut World, &Self::Telemetry);
    fn current_module(&self) -> ModuleId;
    /// The function whose body is being expanded, when it is one function's.
    fn expanding_function(&self) -> Option<FunctionId>;
    fn note_read(&mut self, fact: FactKey);
    fn products(&self) -> Option<&ProductSessions>;
    fn note_product_read(&mut self, product: ProductAddress);

    /// One ordinal per macro invocation this job attempt visits and commits
    /// to (never one retried because it was blocked on a fact or product —
    /// see `expand_macro_invocation`), advancing whether the expansion hits
    /// the memoization cache or runs fresh. Local to the job attempt and
    /// reset with it: the sequence this hands out is a pure function of how
    /// many invocations were visited, never of scheduling or caching.
    ///
    /// A function body holds variables from the expansions of the scope that
    /// defined it as well as from its own, so the two never share a number:
    /// a scope's expansions count up from 0 and a body's count down from -1.
    fn next_expansion_number(&mut self) -> i64;

    /// Where the expansion in progress stands. A guard expands macros but
    /// applies no source sugar: dispatch evaluates its operators itself, so
    /// `-x` stays a negation rather than becoming a `Kernel` call.
    fn expansion_context(&mut self) -> &mut ExpansionContext;

    /// Expands `cursor` standing in `context`, and returns to the enclosing
    /// context after it.
    fn expand_in(
        &mut self,
        context: ExpansionContext,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        let enclosing = std::mem::replace(self.expansion_context(), context);
        let expanded = self.expand_cursor(owner, cursor, scope, depth);
        *self.expansion_context() = enclosing;
        expanded
    }

    /// Expands a guard. A guard holds only what dispatch can evaluate, so a
    /// macro that expands there must expand to such code; `expand_macro_invocation`
    /// refuses the ones that do not.
    fn expand_guard(
        &mut self,
        owner: &QuotedSourceRoot,
        guard: &QuotedSourceCursor,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        self.expand_in(ExpansionContext::Guard, owner, guard, scope, depth)
    }

    /// Expands a pattern: a function head's parameter, or the left side of
    /// `=`, `<-` or a clause's `->`.
    fn expand_pattern(
        &mut self,
        owner: &QuotedSourceRoot,
        pattern: &QuotedSourceCursor,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        self.expand_in(ExpansionContext::Match, owner, pattern, scope, depth)
    }

    /// The source-visible caller scope for macro execution and memoization.
    /// Expansion may layer transient compiler bindings onto `scope`; those
    /// bindings must not change `__CALLER__` or the identity of a call site.
    fn macro_caller_scope(&self, scope: ScopeSnapshot) -> ScopeSnapshot {
        scope
    }
    fn lookup_current_module_macro(&mut self, scope: ScopeSnapshot, name: &str, arity: usize) -> Option<FunctionId>;
    /// A remote call that waits on `module` remembers who made it, so a stall
    /// on that module can name the call.
    fn note_call_into(&mut self, module: ModuleId, name: &str, arity: usize, span: Span) {
        let Some(caller) = self.expanding_function() else {
            return;
        };
        let requester_module = self.current_module();
        let world = self.world();
        let requester = InterfaceRequester {
            owner: world
                .function_source(caller)
                .expect("a function being expanded has its source")
                .owner,
            module: requester_module,
            span,
        };
        let call = ReferencingCall {
            caller,
            name: name.to_string(),
            arity,
        };
        world.note_module_call_expectation(module, requester, call);
    }

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
    ) -> Result<ExpandedRoot, fz_engine::FatalError> {
        match self.expand_cursor(&root, &root.cursor(), scope, depth)? {
            ExpandedValue::Complete(value) => Ok(ExpandedRoot::Complete(root.subroot(value))),
            ExpandedValue::Blocked(effects) => Ok(ExpandedRoot::Blocked(effects)),
        }
    }

    /// `@name` in a definition reads the value the module last set for it
    /// above the definition. An attribute never set reads as `nil`, and
    /// Elixir's warning says so.
    fn expand_attribute_read(
        &mut self,
        owner: &QuotedSourceRoot,
        name: &str,
        span: Option<Span>,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        let symbol = super::quoted_surface::attribute_symbol(name);
        let Some(NamespaceSymbol::Splice(value)) = self.world().lookup_namespace(scope.namespace(), &symbol) else {
            let warning = super::source_diagnostics::undefined_attribute_diagnostic(span.unwrap_or(Span::DUMMY), name);
            let (world, telemetry) = self.split();
            super::drive::ExecutionContext::new(world, telemetry).emit_warning_once(warning);
            return Ok(ExpandedValue::Complete(owner.builder().nil()));
        };
        match self.expand_root(value, scope, depth)? {
            ExpandedRoot::Complete(root) => Ok(ExpandedValue::Complete(root.root())),
            ExpandedRoot::Blocked(effects) => Ok(ExpandedValue::Blocked(effects)),
        }
    }

    fn expand_cursor(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        self.expand_cursor_with_root_sugar(owner, cursor, scope, depth, true)
    }

    fn expand_cursor_with_root_sugar(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        scope: ScopeSnapshot,
        depth: usize,
        allow_root_sugar: bool,
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
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
            if let Some(name) = attribute_read_name(&node, &source_map.borrow()).map_err(|error| {
                emit_internal_surface_error(self.telemetry(), format!("module attribute read failed: {error}"))
            })? {
                return self.expand_attribute_read(owner, &name, node.span, scope, depth);
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
            if allow_root_sugar
                && *self.expansion_context() != ExpansionContext::Guard
                && let Some(rewritten) = rewrite_source_sugar(owner, cursor.root(), &node, &source_map.borrow())
                    .map_err(|error| emit_surface_read_error(self.telemetry(), "source sugar rewrite failed", &error))?
            {
                return match self.expand_root(owner.subroot(rewritten), scope, depth)? {
                    ExpandedRoot::Complete(root) => Ok(ExpandedValue::Complete(root.root())),
                    ExpandedRoot::Blocked(effects) => Ok(ExpandedValue::Blocked(effects)),
                };
            }
            if *self.expansion_context() == ExpansionContext::Guard
                && let Some(result) = self.expand_guard_membership(owner, &node, scope, depth)?
            {
                return Ok(result);
            }
            if let Some(result) = self.expand_ast_call(owner, cursor, &node, scope, depth)? {
                return Ok(result);
            }
            return self.expand_syntax_form(owner, cursor, &node, scope, depth);
        }

        match cursor.root().tag() {
            ValueKind::LIST => self.expand_list(owner, cursor, scope, depth),
            ValueKind::STRUCT => self.expand_tuple(owner, cursor, scope, depth),
            ValueKind::MAP => self.expand_map(owner, cursor, scope, depth),
            _ => Ok(ExpandedValue::Complete(cursor.root())),
        }
    }

    /// A call that no macro answers: a form whose left side or clause section
    /// reads differently from an ordinary call's arguments, or else a plain
    /// node whose parts expand in turn. Being no macro, it is never an item
    /// macro (`x = 1` at the top of a file is a statement).
    fn expand_syntax_form(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        node: &QuotedAstNode,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        let head = (node.head.root().tag() == ValueKind::ATOM)
            .then(|| node.head.atom_name())
            .transpose()
            .map_err(|error| {
                emit_internal_surface_error(self.telemetry(), format!("quoted call head read failed: {error}"))
            })?;
        let arity = match is_list_like(&node.tail) {
            true => node.tail.list_len().map_err(|error| {
                emit_internal_surface_error(self.telemetry(), format!("quoted call arg read failed: {error}"))
            })?,
            false => return self.expand_ast_node(owner, cursor, node, scope, depth),
        };
        match head {
            Some(head) if binds_its_left_side(&head) && arity == 2 => {
                let args = self.call_args(&node.tail)?;
                self.expand_binding_call(owner, cursor, node, &args, scope, depth)
            }
            Some(head) if arity == 1 && expression_clause_section(&head).is_some() => {
                let args = self.call_args(&node.tail)?;
                let section = expression_clause_section(&head).expect("guarded by the match arm");
                self.expand_with_expression_clauses(owner, cursor, node, &args[0], section, scope, depth)
            }
            _ => self.expand_ast_node(owner, cursor, node, scope, depth),
        }
    }

    fn expand_ast_node(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        node: &QuotedAstNode,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
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

    /// `in` and `not in` in a guard, as Elixir's `in` macro expands them
    /// there. `None` when the node is no membership test or its right side is
    /// no literal list or integer range, and the guard then reads it as
    /// written.
    fn expand_guard_membership(
        &mut self,
        owner: &QuotedSourceRoot,
        node: &QuotedAstNode,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<Option<ExpandedValue>, fz_engine::FatalError> {
        if node.head.root().tag() != ValueKind::ATOM || !is_list_like(&node.tail) {
            return Ok(None);
        }
        let op = node.head.atom_name().map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted call head read failed: {error}"))
        })?;
        if !matches!(op.as_str(), "in" | "not in") {
            return Ok(None);
        }
        let args = self.call_args(&node.tail)?;
        let [left, right] = args.as_slice() else {
            return Ok(None);
        };
        let mut expanded = Vec::with_capacity(2);
        for operand in [left, right] {
            match self.expand_cursor(owner, operand, scope, depth)? {
                ExpandedValue::Complete(value) => expanded.push(owner.subroot(value)),
                ExpandedValue::Blocked(effects) => return Ok(Some(ExpandedValue::Blocked(effects))),
            }
        }
        let source_map = self.world().source_map();
        let rewritten = rewrite_guard_membership(
            owner,
            node,
            &op,
            &expanded[0].cursor(),
            &expanded[1].cursor(),
            &source_map.borrow(),
        )
        .map_err(|error| emit_surface_read_error(self.telemetry(), "guard membership rewrite failed", &error))?;
        Ok(rewritten.map(ExpandedValue::Complete))
    }

    fn expand_ast_call(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        node: &QuotedAstNode,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<Option<ExpandedValue>, fz_engine::FatalError> {
        if !is_list_like(&node.tail) {
            return Ok(None);
        }
        let arity = node.tail.list_len().map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted call arg read failed: {error}"))
        })?;
        let source_map = self.world().source_map();
        if is_compiler_define_call(node, arity, &source_map.borrow()).map_err(|error| {
            emit_internal_surface_error(
                self.telemetry(),
                format!("quoted compiler-service detection failed: {error}"),
            )
        })? {
            return Ok(Some(ExpandedValue::Complete(cursor.root())));
        }

        let invocation = owner.subroot(cursor.root());
        if let Some(result) = self.expand_remote_ast_call(owner, &invocation, node, scope, depth, arity)? {
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
        if head == "when" && arity >= 2 {
            let args = self.call_args(&node.tail)?;
            return self
                .expand_when_call(owner, cursor, node, &args, scope, depth)
                .map(Some);
        }
        if is_scope_definition_head(&head) {
            let args = self.call_args(&node.tail)?;
            let mut expanded = Vec::with_capacity(args.len());
            for (index, arg) in args.iter().enumerate() {
                let value = self.expand_cursor_with_root_sugar(owner, arg, scope, depth, index != 0)?;
                match value {
                    ExpandedValue::Complete(value) => expanded.push(value),
                    ExpandedValue::Blocked(effects) => return Ok(Some(ExpandedValue::Blocked(effects))),
                }
            }
            if expanded.iter().copied().eq(args.iter().map(QuotedSourceCursor::root)) {
                return Ok(Some(ExpandedValue::Complete(cursor.root())));
            }
            let builder = owner.builder();
            let tail = builder.list(&expanded).map_err(|error| {
                emit_internal_surface_error(self.telemetry(), format!("quoted definition rebuild failed: {error}"))
            })?;
            let rebuilt = builder
                .tuple(&[node.head.root(), node.meta.root(), tail])
                .map_err(|error| {
                    emit_internal_surface_error(self.telemetry(), format!("quoted definition rebuild failed: {error}"))
                })?;
            return Ok(Some(ExpandedValue::Complete(rebuilt)));
        }
        let bound = read_bound_callable(node).map_err(|error| {
            emit_internal_surface_error(
                self.telemetry(),
                format!("quoted call classification read failed: {error}"),
            )
        })?;
        let symbol = {
            let world = self.world();
            call_node_symbol(world, bound, scope, &head, arity)
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
        self.expand_macro_invocation(owner, invocation, function, scope, depth, &self.call_args(&node.tail)?)
            .map(Some)
    }

    fn call_args(&self, tail: &QuotedSourceCursor) -> Result<Vec<QuotedSourceCursor>, fz_engine::FatalError> {
        tail.list_items().map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted call arg read failed: {error}"))
        })
    }

    /// `pattern = value`, `pattern <- value` and `patterns -> body`: the left
    /// side binds, so it expands as a pattern; the right side stands where
    /// the call does.
    fn expand_binding_call(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        node: &QuotedAstNode,
        args: &[QuotedSourceCursor],
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        let left = match self.expand_pattern(owner, &args[0], scope, depth)? {
            ExpandedValue::Complete(value) => value,
            blocked @ ExpandedValue::Blocked(_) => return Ok(blocked),
        };
        let right = match self.expand_cursor(owner, &args[1], scope, depth)? {
            ExpandedValue::Complete(value) => value,
            blocked @ ExpandedValue::Blocked(_) => return Ok(blocked),
        };
        self.rebuild_call(owner, cursor, node, args, &[left, right])
    }

    /// `cond`'s clauses, and `receive`'s `after` clause, test an expression
    /// on the left of `->` rather than match a pattern. `section` names the
    /// keyword whose clauses those are; every other keyword expands as usual.
    #[allow(clippy::too_many_arguments)]
    fn expand_with_expression_clauses(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        node: &QuotedAstNode,
        keywords: &QuotedSourceCursor,
        section: &str,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        if !keywords.is_list_like() {
            return self.expand_ast_node(owner, cursor, node, scope, depth);
        }
        let read_failed = |tel: &Self::Telemetry, error: QuotedSourceError| {
            emit_internal_surface_error(tel, format!("quoted clause section read failed: {error}"))
        };
        let entries = keywords
            .list_items()
            .map_err(|error| read_failed(self.telemetry(), error))?;
        let builder = owner.builder();
        let mut expanded = Vec::with_capacity(entries.len());
        for entry in &entries {
            // A tuple is a schema'd struct in quoted source.
            let pair = match entry.root().tag() == ValueKind::STRUCT {
                true => entry
                    .tuple_items()
                    .map_err(|error| read_failed(self.telemetry(), error))?,
                false => Vec::new(),
            };
            let is_section = match pair.as_slice() {
                [key, _] if key.root().tag() == ValueKind::ATOM => {
                    key.atom_name().map_err(|error| read_failed(self.telemetry(), error))? == section
                }
                _ => false,
            };
            let value = if is_section {
                let clauses = match self.expand_expression_clauses(owner, &pair[1], scope, depth)? {
                    ExpandedValue::Complete(value) => value,
                    blocked @ ExpandedValue::Blocked(_) => return Ok(blocked),
                };
                builder.tuple(&[pair[0].root(), clauses]).map_err(|error| {
                    emit_internal_surface_error(
                        self.telemetry(),
                        format!("quoted clause section rebuild failed: {error}"),
                    )
                })?
            } else {
                match self.expand_cursor(owner, entry, scope, depth)? {
                    ExpandedValue::Complete(value) => value,
                    blocked @ ExpandedValue::Blocked(_) => return Ok(blocked),
                }
            };
            expanded.push(value);
        }
        if expanded
            .iter()
            .copied()
            .eq(entries.iter().map(QuotedSourceCursor::root))
        {
            return Ok(ExpandedValue::Complete(cursor.root()));
        }
        let keywords_root = builder.list(&expanded).map_err(|error| {
            emit_internal_surface_error(
                self.telemetry(),
                format!("quoted clause section rebuild failed: {error}"),
            )
        })?;
        self.rebuild_call(owner, cursor, node, std::slice::from_ref(keywords), &[keywords_root])
    }

    /// Each `test -> body` clause of `clauses`, with `test` an expression.
    fn expand_expression_clauses(
        &mut self,
        owner: &QuotedSourceRoot,
        clauses: &QuotedSourceCursor,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        if !clauses.is_list_like() {
            return self.expand_cursor(owner, clauses, scope, depth);
        }
        let read_failed = |tel: &Self::Telemetry, error: QuotedSourceError| {
            emit_internal_surface_error(tel, format!("quoted clause read failed: {error}"))
        };
        let items = clauses
            .list_items()
            .map_err(|error| read_failed(self.telemetry(), error))?;
        let source_map = self.world().source_map();
        let mut expanded = Vec::with_capacity(items.len());
        for item in &items {
            let node = item
                .ast_node(&source_map.borrow())
                .map_err(|error| read_failed(self.telemetry(), error))?;
            let arrow = match node {
                Some(node) if node.head.root().tag() == ValueKind::ATOM && node.tail.is_list_like() => {
                    let is_arrow = node
                        .head
                        .atom_name()
                        .map_err(|error| read_failed(self.telemetry(), error))?
                        == "->";
                    is_arrow.then_some(node)
                }
                _ => None,
            };
            let Some(arrow) = arrow else {
                match self.expand_cursor(owner, item, scope, depth)? {
                    ExpandedValue::Complete(value) => expanded.push(value),
                    blocked @ ExpandedValue::Blocked(_) => return Ok(blocked),
                }
                continue;
            };
            let sides = arrow
                .tail
                .list_items()
                .map_err(|error| read_failed(self.telemetry(), error))?;
            let mut expanded_sides = Vec::with_capacity(sides.len());
            for side in &sides {
                match self.expand_in(ExpansionContext::Expression, owner, side, scope, depth)? {
                    ExpandedValue::Complete(value) => expanded_sides.push(value),
                    blocked @ ExpandedValue::Blocked(_) => return Ok(blocked),
                }
            }
            match self.rebuild_call(owner, item, &arrow, &sides, &expanded_sides)? {
                ExpandedValue::Complete(value) => expanded.push(value),
                blocked @ ExpandedValue::Blocked(_) => return Ok(blocked),
            }
        }
        if expanded.iter().copied().eq(items.iter().map(QuotedSourceCursor::root)) {
            return Ok(ExpandedValue::Complete(clauses.root()));
        }
        owner
            .builder()
            .list(&expanded)
            .map(ExpandedValue::Complete)
            .map_err(|error| {
                emit_internal_surface_error(self.telemetry(), format!("quoted clause rebuild failed: {error}"))
            })
    }

    /// `node` with its arguments replaced by `expanded`, or `cursor` itself
    /// when no argument changed.
    fn rebuild_call(
        &self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        node: &QuotedAstNode,
        args: &[QuotedSourceCursor],
        expanded: &[AnyValueRef],
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        if expanded.iter().copied().eq(args.iter().map(QuotedSourceCursor::root)) {
            return Ok(ExpandedValue::Complete(cursor.root()));
        }
        let builder = owner.builder();
        builder
            .list(expanded)
            .and_then(|tail| builder.tuple(&[node.head.root(), node.meta.root(), tail]))
            .map(ExpandedValue::Complete)
            .map_err(|error| {
                emit_internal_surface_error(self.telemetry(), format!("quoted call rebuild failed: {error}"))
            })
    }

    /// `left when guard`: everything before the last argument is a pattern or
    /// head, the last is the guard.
    fn expand_when_call(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        node: &QuotedAstNode,
        args: &[QuotedSourceCursor],
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        let (guard, patterns) = args.split_last().expect("a `when` call has a guard");
        let mut expanded = Vec::with_capacity(args.len());
        for pattern in patterns {
            match self.expand_cursor(owner, pattern, scope, depth)? {
                ExpandedValue::Complete(value) => expanded.push(value),
                ExpandedValue::Blocked(effects) => return Ok(ExpandedValue::Blocked(effects)),
            }
        }
        match self.expand_guard(owner, guard, scope, depth)? {
            ExpandedValue::Complete(value) => expanded.push(value),
            ExpandedValue::Blocked(effects) => return Ok(ExpandedValue::Blocked(effects)),
        }
        self.rebuild_call(owner, cursor, node, args, &expanded)
    }

    fn expand_remote_ast_call(
        &mut self,
        owner: &QuotedSourceRoot,
        invocation: &QuotedSourceRoot,
        node: &QuotedAstNode,
        scope: ScopeSnapshot,
        depth: usize,
        arity: usize,
    ) -> Result<Option<ExpandedValue>, fz_engine::FatalError> {
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
        // `lhs[key]` is an index the decoder reads off its callee's stamp; it
        // calls into no module, whatever name the callee spells.
        if super::quoted_function::is_bracket_access_callee(&head_node).map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted bracket access read failed: {error}"))
        })? {
            return Ok(None);
        }
        let Some((module_cursor, function_cursor)) = head_node.tail.list_pair().map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted remote target read failed: {error}"))
        })?
        else {
            return Ok(None);
        };
        let (module_cursor, function_cursor) = (&module_cursor, &function_cursor);
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
                Some(module) => world.reference_module_denotation(module),
                None => world.resolve_module_name(scope.namespace(), &ModuleName::from_segments(module_path.clone())),
            }
        };
        if module == self.current_module() {
            return self.expand_current_module_remote_ast_call(
                owner,
                invocation,
                scope,
                depth,
                &node.tail,
                arity,
                &function_name,
                &module_path,
                call_span,
            );
        }
        if let Some(symbol) = self.imported_symbol_of(module, &function_name, arity, &scope) {
            return match symbol {
                NamespaceSymbol::Macro(function) => self
                    .expand_macro_invocation(
                        owner,
                        invocation.clone(),
                        function,
                        scope,
                        depth,
                        &self.call_args(&node.tail)?,
                    )
                    .map(Some),
                NamespaceSymbol::Callable(function) => {
                    self.note_call_into(module, &function_name, arity, call_span);
                    Ok(Some(ExpandedValue::Blocked(Box::new(
                        self.wait_for_callable_module_interface(function),
                    ))))
                }
                _ => Ok(None),
            };
        }
        let module_defined = self.world().module_defined_revision(module);
        if module_defined.is_none() {
            if self.world().is_runtime_module(module) {
                return Ok(None);
            }
            self.note_call_into(module, &function_name, arity, call_span);
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
            match world.lookup_module_callable(module, &function_name, arity) {
                Some(NamespaceSymbol::Macro(function)) => Some(function),
                Some(NamespaceSymbol::Callable(function)) => {
                    self.note_call_into(module, &function_name, arity, call_span);
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
        if !self.world().macro_callable_remotely(scope.namespace(), function) {
            return Err(remote_macro_not_required(
                self.telemetry(),
                &function_name,
                arity,
                &module_path,
                call_span,
            ));
        }
        self.expand_macro_invocation(
            owner,
            invocation.clone(),
            function,
            scope,
            depth,
            &self.call_args(&node.tail)?,
        )
        .map(Some)
    }

    /// What the scope's namespace binds `name/arity` to when that binding is
    /// the callable of `module`: the answer an unqualified call of the same
    /// name would get, so the qualified call follows the same route.
    fn imported_symbol_of(
        &mut self,
        module: ModuleId,
        name: &str,
        arity: usize,
        scope: &ScopeSnapshot,
    ) -> Option<NamespaceSymbol> {
        let world = self.world();
        let symbol = world.lookup_callable_namespace(scope.namespace(), name, arity)?;
        match symbol {
            NamespaceSymbol::Macro(function)
            | NamespaceSymbol::Callable(function)
            | NamespaceSymbol::Function(function)
                if world.function_module(function) == module =>
            {
                Some(symbol)
            }
            _ => None,
        }
    }

    fn expand_current_module_remote_ast_call(
        &mut self,
        owner: &QuotedSourceRoot,
        invocation: &QuotedSourceRoot,
        scope: ScopeSnapshot,
        depth: usize,
        tail: &QuotedSourceCursor,
        arity: usize,
        function_name: &str,
        module_path: &[String],
        call_span: Span,
    ) -> Result<Option<ExpandedValue>, fz_engine::FatalError> {
        let Some(function) = self.lookup_current_module_macro(scope, function_name, arity) else {
            return Ok(None);
        };
        if !self.world().macro_callable_remotely(scope.namespace(), function) {
            return Err(remote_macro_not_required(
                self.telemetry(),
                function_name,
                arity,
                module_path,
                call_span,
            ));
        }
        self.expand_macro_invocation(
            owner,
            invocation.clone(),
            function,
            scope,
            depth,
            &self.call_args(tail)?,
        )
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
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        let call_span = self.invocation_span(&invocation)?;
        let expanded = self.run_macro_invocation(owner, invocation, function, scope, depth, args)?;
        if *self.expansion_context() == ExpansionContext::Guard
            && let ExpandedValue::Complete(root) = &expanded
        {
            self.refuse_unguardable_expansion(owner.subroot(*root), function, call_span)?;
        }
        Ok(expanded)
    }

    /// The span of the call a macro was invoked by: the user's own source, or
    /// an earlier expansion's already-stamped result.
    fn invocation_span(&mut self, invocation: &QuotedSourceRoot) -> Result<Option<Span>, fz_engine::FatalError> {
        let source_map = self.world().source_map();
        let node = invocation.cursor().ast_node(&source_map.borrow()).map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("macro call span read failed: {error}"))
        })?;
        Ok(node.and_then(|node| node.span))
    }

    /// A macro expanded inside a guard answers for what it became: dispatch
    /// evaluates operators, literals, variables and function calls, so any
    /// other expansion is refused at the call, naming the macro.
    fn refuse_unguardable_expansion(
        &mut self,
        expansion: QuotedSourceRoot,
        function: FunctionId,
        call_span: Option<Span>,
    ) -> Result<(), fz_engine::FatalError> {
        let source_map = self.world().source_map();
        let guardable = decode_standalone_expr(&expansion.cursor(), call_span, &source_map.borrow())
            .map(|expr| is_guard_expr(&expr))
            .unwrap_or(false);
        if guardable {
            return Ok(());
        }
        let name = self.world().try_function_ref(function).map_or_else(
            || "<unknown macro>".to_string(),
            |reference| reference.name().to_string(),
        );
        Err(emit_job_diagnostic(
            self.telemetry(),
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("invalid expression in guard, `{name}` is not allowed in guards"),
                call_span.unwrap_or(Span::DUMMY),
            ),
        ))
    }

    fn run_macro_invocation(
        &mut self,
        owner: &QuotedSourceRoot,
        invocation: QuotedSourceRoot,
        function: FunctionId,
        scope: ScopeSnapshot,
        depth: usize,
        args: &[QuotedSourceCursor],
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        let definition = FactKey::FunctionDefined(function);
        if self.world().fact_revision(&definition).is_none() {
            return Ok(ExpandedValue::Blocked(Box::new(JobEffects::wait_on_current(
                definition,
            ))));
        }
        self.note_read(definition);
        let root = self.world().macro_root(function);
        let address = ProductAddress::of(ProductKey::RootBackendProduct(root), root);
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
        // The call site every unlocated node in this macro's result falls
        // back to (`stamp_span_fallback`) -- read from `invocation` itself,
        // which is always either the user's own source (real span from the
        // parser) or an earlier macro's already-stamped result (real span
        // from that expansion, by the same rule, one level up).
        let macro_call_span = self.invocation_span(&invocation)?;
        // Drawn once this invocation is committed to (past both blocking
        // checks above), whether it turns out to hit the memoization cache
        // or not -- see `next_expansion_number`.
        let expansion_number = self.next_expansion_number();
        let context = *self.expansion_context();
        let call_site = CallSite::locate(macro_call_span, &self.world().source_map().borrow());
        if let Some(expanded) =
            self.world()
                .memoized_macro_expansion(function, &invocation, caller_scope, context, &call_site, &program)
        {
            return match self.expand_root(expanded, scope, depth + 1)? {
                ExpandedRoot::Complete(root) => Ok(ExpandedValue::Complete(root.root())),
                ExpandedRoot::Blocked(effects) => Ok(ExpandedValue::Blocked(effects)),
            };
        }

        let builder = owner.builder();
        let caller = self
            .world()
            .project_env_value(&builder, caller_scope, context, &call_site)
            .map_err(|error| {
                emit_internal_surface_error(self.telemetry(), format!("__ENV__ projection failed: {error}"))
            })?;
        let arg_roots = args.iter().map(QuotedSourceCursor::root).collect::<Vec<_>>();
        let (world, tel) = self.split();
        let expanded = super::drive::ExecutionContext::new(world, tel)
            .run_macro_on_source(&program, owner, caller, &arg_roots)
            .map_err(|error| {
                let span = macro_call_span.unwrap_or(Span::DUMMY);
                emit_job_diagnostic(tel, Diagnostic::error(codes::LOWER_UNSUPPORTED, error, span))
            })?;
        let source_map = world.source_map();
        let expanded = if let Some(macro_call_span) = macro_call_span {
            let filled = stamp_span_fallback(&expanded, &expanded.cursor(), macro_call_span, &source_map.borrow())
                .map_err(|error| emit_internal_surface_error(tel, format!("span fallback stamping failed: {error}")))?;
            expanded.subroot(filled)
        } else {
            expanded
        };
        let claim = ExpansionClaim {
            receiver: world.quote_context(world.function_ref(function).module),
            counter: crate::ast::VarCounter::Module {
                module: world.quote_context(caller_scope.module_id()),
                n: expansion_number,
            },
        };
        let stamped = stamp_expansion_counter(&expanded, &expanded.cursor(), &claim, &source_map.borrow())
            .map_err(|error| emit_internal_surface_error(tel, format!("hygiene stamping failed: {error}")))?;
        let expanded = expanded.subroot(stamped);
        emit_macro_expanded(world, tel, &function, &expanded);
        world.memoize_macro_expansion(
            function,
            invocation,
            caller_scope,
            context,
            call_site,
            &program,
            expanded.clone(),
        );
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
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        let mut expanded = Vec::with_capacity(cursor.list_len().map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted list expansion failed: {error}"))
        })?);
        let mut changed = false;
        for item in cursor.list_iter() {
            let item = item.map_err(|error| {
                emit_internal_surface_error(self.telemetry(), format!("quoted list expansion failed: {error}"))
            })?;
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
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        let arity = cursor.tuple_arity().map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted tuple expansion failed: {error}"))
        })?;
        let mut expanded = Vec::with_capacity(arity);
        let mut changed = false;
        for index in 0..arity {
            let item = cursor.tuple_item(index).map_err(|error| {
                emit_internal_surface_error(self.telemetry(), format!("quoted tuple expansion failed: {error}"))
            })?;
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
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
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

/// What one expansion claims: the variables a `quote` of the macro's module
/// wrote (context `receiver`) that have no counter yet get `counter`.
struct ExpansionClaim {
    pub(super) receiver: crate::ast::AtomName,
    pub(super) counter: crate::ast::VarCounter,
}

/// Elixir's `linify_with_context_counter`, run on a macro's result once it
/// has run and before it is memoized. Every variable whose context is the
/// macro's module and that has no counter gets this expansion's counter, so
/// the variables it introduced bind to each other and never to a
/// same-spelled variable of the caller's or of another expansion. This holds
/// for a quote in a helper function of the macro's module as much as for one
/// in the macro itself. A variable with another context, one that already
/// has a counter, and `_` are left as they are.
fn stamp_expansion_counter(
    owner: &QuotedSourceRoot,
    cursor: &QuotedSourceCursor,
    claim: &ExpansionClaim,
    sources: &SourceMap,
) -> Result<AnyValueRef, QuotedSourceError> {
    if let Some(node) = cursor.ast_node(sources)? {
        if is_claimed_variable(&node, claim)? {
            let builder = owner.builder();
            let meta = builder.meta_put(
                &node.meta,
                super::source::META_COUNTER_KEY,
                builder.var_counter(&claim.counter)?,
            )?;
            return builder.tuple(&[node.head.root(), meta, node.tail.root()]);
        }
        let head = stamp_expansion_counter(owner, &node.head, claim, sources)?;
        let tail = stamp_expansion_counter(owner, &node.tail, claim, sources)?;
        if head == node.head.root() && tail == node.tail.root() {
            return Ok(cursor.root());
        }
        return owner.builder().tuple(&[head, node.meta.root(), tail]);
    }
    match cursor.root().tag() {
        ValueKind::LIST => match changed_elements(
            || Ok(cursor.list_iter()),
            |item| stamp_expansion_counter(owner, item, claim, sources),
        )? {
            Some(out) => owner.builder().list(&out),
            None => Ok(cursor.root()),
        },
        ValueKind::STRUCT => match changed_elements(
            || cursor.tuple_iter(),
            |item| stamp_expansion_counter(owner, item, claim, sources),
        )? {
            Some(out) => owner.builder().tuple(&out),
            None => Ok(cursor.root()),
        },
        ValueKind::MAP => {
            let entries = cursor.map_entries()?;
            let mut changed = false;
            let mut out = Vec::with_capacity(entries.len());
            for (key, value) in &entries {
                let key_root = stamp_expansion_counter(owner, key, claim, sources)?;
                let value_root = stamp_expansion_counter(owner, value, claim, sources)?;
                changed |= key_root != key.root() || value_root != value.root();
                out.push((key_root, value_root));
            }
            if changed {
                owner.builder().map(&out)
            } else {
                Ok(cursor.root())
            }
        }
        _ => Ok(cursor.root()),
    }
}

fn is_claimed_variable(node: &QuotedAstNode, claim: &ExpansionClaim) -> Result<bool, QuotedSourceError> {
    Ok(node.head.root().tag() == ValueKind::ATOM
        && node.tail.root().tag() == ValueKind::ATOM
        && node.tail.atom_name()? == claim.receiver
        && node.head.atom_name()?.as_str() != "_"
        && node.meta.var_counter()?.is_none())
}

/// The elements of a list or tuple after `visit` has rewritten each one, or
/// `None` when no element changed. `walk` starts a fresh read of the
/// elements; a second read supplies the unchanged prefix when the first
/// change is found, so an unchanged value is walked without collecting it.
fn changed_elements<I>(
    walk: impl Fn() -> Result<I, QuotedSourceError>,
    mut visit: impl FnMut(&QuotedSourceCursor) -> Result<AnyValueRef, QuotedSourceError>,
) -> Result<Option<Vec<AnyValueRef>>, QuotedSourceError>
where
    I: Iterator<Item = Result<QuotedSourceCursor, QuotedSourceError>>,
{
    let mut out: Option<Vec<AnyValueRef>> = None;
    for (index, item) in walk()?.enumerate() {
        let item = item?;
        let stamped = visit(&item)?;
        match &mut out {
            Some(out) => out.push(stamped),
            None if stamped != item.root() => {
                let mut seeded = walk()?
                    .take(index)
                    .map(|passed| passed.map(|passed| passed.root()))
                    .collect::<Result<Vec<_>, _>>()?;
                seeded.push(stamped);
                out = Some(seeded);
            }
            None => {}
        }
    }
    Ok(out)
}

/// As in Elixir: a node a macro's result carries with no location of its own
/// takes the macro call's location. A node that already has one -- unquoted
/// user code the macro merely relayed, or something an earlier expansion
/// already stamped -- keeps it. Every node a `quote` builds is one with no
/// location, and so is a node a macro builds by hand: `defmodule`,
/// `defprotocol` and `defimpl` each rebuild their `Fz.Compiler.define(...)`
/// argument from destructured parameters.
///
/// A `quote` call's own arguments are left untouched: `expand_ast_call`
/// already treats a `quote` node as its own boundary, complete without
/// looking inside (the "head == \"quote\"" case above), because what it
/// quotes is data the macro is carrying, not syntax this expansion owns.
/// Reaching past that same boundary here to stamp a location into it would
/// fabricate one on a value the macro built and meant to hand back exactly
/// as constructed.
fn stamp_span_fallback(
    owner: &QuotedSourceRoot,
    cursor: &QuotedSourceCursor,
    macro_call_span: Span,
    sources: &SourceMap,
) -> Result<AnyValueRef, QuotedSourceError> {
    if let Some(node) = cursor.ast_node(sources)? {
        if is_quote_call(&node)? {
            if node.span.is_none() {
                let builder = owner.builder();
                let meta = builder.meta_put(
                    &node.meta,
                    super::source::META_SPAN_KEY,
                    builder.span(&macro_call_span)?,
                )?;
                return builder.tuple(&[node.head.root(), meta, node.tail.root()]);
            }
            return Ok(cursor.root());
        }
        let head = stamp_span_fallback(owner, &node.head, macro_call_span, sources)?;
        let tail = stamp_span_fallback(owner, &node.tail, macro_call_span, sources)?;
        if node.span.is_none() {
            let builder = owner.builder();
            let meta = builder.meta_put(
                &node.meta,
                super::source::META_SPAN_KEY,
                builder.span(&macro_call_span)?,
            )?;
            return builder.tuple(&[head, meta, tail]);
        }
        if head == node.head.root() && tail == node.tail.root() {
            return Ok(cursor.root());
        }
        return owner.builder().tuple(&[head, node.meta.root(), tail]);
    }
    match cursor.root().tag() {
        ValueKind::LIST => match changed_elements(
            || Ok(cursor.list_iter()),
            |item| stamp_span_fallback(owner, item, macro_call_span, sources),
        )? {
            Some(out) => owner.builder().list(&out),
            None => Ok(cursor.root()),
        },
        ValueKind::STRUCT => match changed_elements(
            || cursor.tuple_iter(),
            |item| stamp_span_fallback(owner, item, macro_call_span, sources),
        )? {
            Some(out) => owner.builder().tuple(&out),
            None => Ok(cursor.root()),
        },
        ValueKind::MAP => {
            let entries = cursor.map_entries()?;
            let mut changed = false;
            let mut out = Vec::with_capacity(entries.len());
            for (key, value) in &entries {
                let key_root = stamp_span_fallback(owner, key, macro_call_span, sources)?;
                let value_root = stamp_span_fallback(owner, value, macro_call_span, sources)?;
                changed |= key_root != key.root() || value_root != value.root();
                out.push((key_root, value_root));
            }
            if changed {
                owner.builder().map(&out)
            } else {
                Ok(cursor.root())
            }
        }
        _ => Ok(cursor.root()),
    }
}

/// Whether `node` is a `quote(...)` call, the same shape `expand_ast_call`
/// recognizes as its own boundary: a call node (its tail is an argument
/// list, not a variable context) whose head atom is literally `quote`.
fn is_quote_call(node: &QuotedAstNode) -> Result<bool, QuotedSourceError> {
    if node.head.root().tag() != ValueKind::ATOM {
        return Ok(false);
    }
    Ok(node.head.atom_name()? == "quote" && is_list_like(&node.tail))
}

/// The name `@name` reads, when `node` is that read.
fn attribute_read_name(node: &QuotedAstNode, sources: &SourceMap) -> Result<Option<String>, QuotedSourceError> {
    if node.head.root().tag() != ValueKind::ATOM || node.head.atom_name()? != "@" || !is_list_like(&node.tail) {
        return Ok(None);
    }
    let mut args = node.tail.list_iter();
    let (Some(arg), None) = (args.next().transpose()?, args.next()) else {
        return Ok(None);
    };
    let Some(name_node) = arg.ast_node(sources)? else {
        return Ok(None);
    };
    if name_node.head.root().tag() != ValueKind::ATOM || is_list_like(&name_node.tail) {
        return Ok(None);
    }
    Ok(Some(name_node.head.atom_name()?.to_string()))
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
    Ok((name.starts_with("__") && !is_list_like(&node.tail)).then(|| name.to_string()))
}

pub(crate) fn expand_item_macro_fragment<C: QuotedExpansionCtx>(
    ctx: &mut C,
    macro_call: &MacroCallForm,
    scope: ScopeSnapshot,
) -> Result<ExpandedScopeFragment, fz_engine::FatalError> {
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
        return Ok(ExpandedScopeFragment::NotAMacro {
            display_name: invocation.display_name,
        });
    };
    let expanded = match result {
        ExpandedValue::Complete(root) => root,
        ExpandedValue::Blocked(effects) => return Ok(ExpandedScopeFragment::Blocked(effects)),
    };
    let source_map = ctx.world().source_map();
    let expanded = item_macro_fragment_root(ctx.telemetry(), &owner.subroot(expanded), &source_map.borrow())?;
    let surface = read_compiler_fragment_root(
        ctx.telemetry(),
        &expanded,
        "item macro expanded source",
        &source_map.borrow(),
    )?;
    Ok(ExpandedScopeFragment::Complete(surface))
}

/// The items an item macro's expansion defines: a list is its elements, a
/// block is its statements, and anything else is the one item.
fn item_macro_fragment_root(
    tel: &impl crate::telemetry::Telemetry,
    root: &QuotedSourceRoot,
    sources: &SourceMap,
) -> Result<QuotedSourceRoot, fz_engine::FatalError> {
    expanded_items(root.cursor(), sources)
        .and_then(|items| root.interned_list_subroot(&items))
        .map_err(|error| emit_internal_surface_error(tel, format!("item macro fragment root read failed: {error}")))
}

fn expanded_items(expansion: QuotedSourceCursor, sources: &SourceMap) -> Result<Vec<AnyValueRef>, QuotedSourceError> {
    let mut items = Vec::new();
    if expansion.root().tag() == ValueKind::LIST {
        for element in expansion.list_iter() {
            collect_statements(element?, sources, &mut items)?;
        }
    } else {
        collect_statements(expansion, sources, &mut items)?;
    }
    Ok(items)
}

fn collect_statements(
    quoted: QuotedSourceCursor,
    sources: &SourceMap,
    items: &mut Vec<AnyValueRef>,
) -> Result<(), QuotedSourceError> {
    match block_statements(&quoted, sources)? {
        Some(statements) => statements
            .into_iter()
            .try_for_each(|statement| collect_statements(statement?, sources, items)),
        None => {
            items.push(quoted.root());
            Ok(())
        }
    }
}

fn block_statements(quoted: &QuotedSourceCursor, sources: &SourceMap) -> Result<Option<ListItems>, QuotedSourceError> {
    match quoted.ast_node(sources)? {
        Some(node) if node.head.root().tag() == ValueKind::ATOM && node.head.atom_name()? == "__block__" => {
            Ok(Some(node.tail.list_iter()))
        }
        _ => Ok(None),
    }
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
) -> Result<ItemMacroInvocation, fz_engine::FatalError> {
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
                // Everything but a definition head expands through the ordinary
                // call path. The one thing decided here is whose macro it is:
                // at item position the module is still being defined, so its
                // own macros are not callable yet.
                let arity = node.tail.list_len().unwrap_or(0);
                let bound = read_bound_callable(&node).map_err(|error| {
                    emit_internal_surface_error(tel, format!("item macro classification read failed: {error}"))
                })?;
                if let Some(NamespaceSymbol::Macro(function)) = call_node_symbol(world, bound, scope, &head, arity)
                    && own_module_item_call(world, function, scope)
                {
                    return Err(item_macro_of_the_module_being_defined(tel, &head, arity, span));
                }
                return Ok(ItemMacroInvocation {
                    function: None,
                    args: Vec::new(),
                    display_name: head.to_string(),
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
                    display_name: head.to_string(),
                    node: Some(node),
                });
            }
            let NamespaceSymbol::Macro(function) = symbol else {
                return Err(item_macro_not_defmacro(tel, &head, span));
            };
            if own_module_item_call(world, function, scope) {
                return Err(item_macro_of_the_module_being_defined(tel, &head, args.len(), span));
            }
            return Ok(ItemMacroInvocation {
                function: Some(function),
                args,
                display_name: head.to_string(),
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

    let mut display_name = "item".to_string();
    for item in cursor.list_iter() {
        let item =
            item.map_err(|error| emit_internal_surface_error(tel, format!("grouped item macro read failed: {error}")))?;
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
        display_name = head.to_string();
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
) -> Result<ScopeSurface, fz_engine::FatalError> {
    read_surface_root_with(tel, root, context, sources, read_compiler_fragment_surface)
}

fn read_surface_root_with(
    tel: &impl crate::telemetry::Telemetry,
    root: &QuotedSourceRoot,
    context: &str,
    sources: &crate::source::SourceMap,
    read: fn(&QuotedSourceRoot, &crate::source::SourceMap) -> Result<ScopeSurface, QuotedSourceError>,
) -> Result<ScopeSurface, fz_engine::FatalError> {
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

/// Route a failed surface read to the right diagnostic: a user-coded error
/// (malformed source surface) carries its own code; everything else is an
/// internal invariant failure.
pub(crate) fn emit_surface_read_error(
    tel: &impl crate::telemetry::Telemetry,
    context: &str,
    error: &super::source::QuotedSourceError,
) -> fz_engine::FatalError {
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
) -> fz_engine::FatalError {
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
) -> fz_engine::FatalError {
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

/// The callable a call node retained, if it retained one.
fn read_bound_callable(node: &QuotedAstNode) -> Result<Option<FunctionId>, QuotedSourceError> {
    node.meta.bound_callable()
}

/// The symbol a call node names.
///
/// A retained callable settles which function the call names, and its kind is
/// then asked of that exact function; the head spelling is only consulted when
/// nothing was retained. Every reader that classifies a call asks here, so the
/// expander and the item-macro boundary cannot disagree about whose macro a
/// head is.
fn call_node_symbol(
    world: &mut World,
    bound: Option<FunctionId>,
    scope: ScopeSnapshot,
    head: &str,
    arity: usize,
) -> Option<NamespaceSymbol> {
    match bound {
        Some(function) => world.retained_callable_symbol(function),
        None => world.lookup_callable_namespace(scope.namespace(), head, arity),
    }
}

/// Whether this item-position macro belongs to the module being defined.
///
/// Top-level source is not a module: it is compiled in order, so a macro
/// defined above an invocation is callable there.
fn own_module_item_call(world: &World, function: FunctionId, scope: ScopeSnapshot) -> bool {
    let owner = world.function_module(function);
    !owner.is_global() && owner == scope.module_id()
}

/// A module body cannot invoke a macro the same module defines.
///
/// The module is still being defined when its body runs, so its own macros do
/// not exist to call yet. Elixir draws the same line and reports the call as an
/// undefined function; the macro has to live in another module the body
/// imports. A function body of that module may call it — by then the module is
/// compiled.
fn item_macro_of_the_module_being_defined(
    tel: &impl crate::telemetry::Telemetry,
    name: &str,
    arity: usize,
    span: Span,
) -> fz_engine::FatalError {
    emit_job_diagnostic(
        tel,
        Diagnostic::error(
            codes::MACRO_OWN_MODULE_ITEM_CALL,
            format!(
                "`{name}/{arity}` is a macro of the module being defined, so it cannot be invoked in that module's body; define it in another module and import it"
            ),
            span,
        ),
    )
}

/// An item macro expanded into something that is not a definition, in a scope
/// that has no program to run it.
pub(crate) fn item_macro_expanded_to_a_non_definition(
    tel: &impl crate::telemetry::Telemetry,
    span: Span,
) -> fz_engine::FatalError {
    emit_job_diagnostic(
        tel,
        Diagnostic::error(
            codes::MACRO_NOT_A_DEFMACRO,
            "item macro expansion returned a non-definition call",
            span,
        ),
    )
}

pub(crate) fn item_macro_not_defmacro(
    tel: &impl crate::telemetry::Telemetry,
    name: &str,
    span: Span,
) -> fz_engine::FatalError {
    let message = format!("item-level call `{name}(...)` is not a defmacro");
    emit_job_diagnostic(tel, Diagnostic::error(codes::MACRO_NOT_A_DEFMACRO, message, span))
}

fn item_macro_display_name(node: &QuotedAstNode, sources: &SourceMap) -> Result<String, QuotedSourceError> {
    if node.head.root().tag() == ValueKind::ATOM {
        return node.head.atom_name().map(|name| name.to_string());
    }
    let Some(head_node) = node.head.ast_node(sources)? else {
        return Ok("item".to_string());
    };
    let Some((module, function)) = head_node.tail.list_pair()? else {
        return Ok("item".to_string());
    };
    if head_node.head.root().tag() == ValueKind::ATOM
        && head_node.head.atom_name()? == "."
        && let Some(path) = alias_path(&module, sources)?
        && function.root().tag() == ValueKind::ATOM
    {
        return Ok(format!("{}.{}", path.join("."), function.atom_name()?));
    }
    Ok("item".to_string())
}

fn is_compiler_define_call(node: &QuotedAstNode, arity: usize, sources: &SourceMap) -> Result<bool, QuotedSourceError> {
    if arity != 2 {
        return Ok(false);
    }
    let Some(callee) = node.head.ast_node(sources)? else {
        return Ok(false);
    };
    if callee.head.atom_name()? != "." {
        return Ok(false);
    }
    let Some((module_cursor, function_cursor)) = callee.tail.list_pair()? else {
        return Ok(false);
    };
    if !alias_path(&module_cursor, sources)?.is_some_and(|path| path == ["Fz".to_string(), "Compiler".to_string()])
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
#[path = "quoted_expander_test.rs"]
mod quoted_expander_test;
