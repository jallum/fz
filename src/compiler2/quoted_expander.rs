use fz_runtime::any_value::{AnyValueRef, ValueKind};

use crate::diag::{Diagnostic, codes};
use crate::modules::identity::ModuleName;
use crate::source::{SourceMap, Span};
use crate::telemetry::TelemetryExt as _;

use super::canon::function_label;
use super::definition_time::is_evaluator_name;
use super::drive::{FactKey, JobEffects, ProductAddress, emit_job_diagnostic};
use super::env_projection::CallSite;
use super::identity::{FunctionId, ModuleId};
use super::jobs::is_guard_expr;
use super::macro_run::{ExpansionAnswer, ExpansionRequest, MacroExpansion, MacroRun, MacroWarning};
use super::module_interface::{InterfaceRequester, ReferencingCall};
use super::namespace::NamespaceSymbol;
use super::pull::{ProductKey, ProductSessions, ProductValue};
use super::quoted_function::decode_standalone_expr;
use super::quoted_surface::{
    MacroCallForm, ScopeForm, ScopeSurface, is_function_definition_head, is_scope_definition_head,
    read_compiler_fragment_surface, read_scope_directive,
};
use super::scope::ScopeSnapshot;
use super::source::{
    ListItems, META_BOUND_CALLABLE_KEY, QuotedAstNode, QuotedSourceCursor, QuotedSourceError, QuotedSourceMetadata,
    QuotedSourceRoot,
};
use super::source_sugar::{rewrite_guard_membership, rewrite_source_sugar};
use super::token_payload::decode_token;
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

    /// The context a macro body names when it asks the compiler to expand a
    /// call: 0 an expression, 1 a pattern, 2 a guard.
    pub(crate) fn from_code(code: i64) -> Self {
        match code {
            0 => ExpansionContext::Expression,
            1 => ExpansionContext::Match,
            2 => ExpansionContext::Guard,
            other => panic!("`Macro.expand` names context {other}, and `lib/macro.fz` names only 0, 1 and 2"),
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

/// A body's scope after one of its `alias`, `import` or `require` forms.
/// What walking a body block's statements came to.
pub(crate) enum BodyWalk {
    Blocked(Box<JobEffects>),
    Done {
        expanded: Vec<AnyValueRef>,
        scope: ScopeSnapshot,
    },
}

pub(crate) enum DirectedScope {
    Moved(ScopeSnapshot),
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

/// The scope a macro call's expansion ends in, handed to the body block that
/// holds the call as a statement: an `import` or `alias` the macro quotes
/// covers the statements after the call, as it does in Elixir. Only a call
/// that is itself a statement of a body block is handed back; a macro nested
/// in an argument or a branch keeps its scope to itself.
#[derive(Debug, Default)]
pub(crate) struct ScopeHandoff {
    statement: Option<AnyValueRef>,
    scope: Option<ScopeSnapshot>,
}

/// What a call names, as far as macros go.
pub(crate) enum MacroCall {
    Macro(FunctionId),
    /// The answer waits on a fact.
    Blocked(Box<JobEffects>),
    /// A qualified call of a module's macro that the scope does not `require`.
    NotRequired(NotRequired),
    NotAMacro,
}

/// The macro `name/arity` of `module_path`, called by a scope that does not
/// `require` the module.
pub(crate) struct NotRequired {
    name: String,
    arity: usize,
    module_path: Vec<String>,
    span: Span,
}

impl NotRequired {
    /// Written code that calls it is refused.
    fn error(&self, telemetry: &impl crate::telemetry::Telemetry) -> fz_engine::FatalError {
        remote_macro_not_required(telemetry, &self.name, self.arity, &self.module_path, self.span)
    }
}

/// What a macro body's question came to.
pub(crate) enum Answered {
    Ready(ExpansionAnswer),
    Blocked(Box<JobEffects>),
}

/// What one step of a macro call came to.
pub(crate) enum MacroStep {
    NotAMacro,
    Expanded(AnyValueRef),
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

    /// How many expansion numbers `next_expansion_number` has handed out.
    fn expansions_visited(&self) -> i64;

    /// Where the expansion in progress stands. A guard expands macros but
    /// applies no source sugar: dispatch evaluates its operators itself, so
    /// `-x` stays a negation rather than becoming a `Kernel` call.
    fn expansion_context(&mut self) -> &mut ExpansionContext;

    /// Where a macro call standing as a body statement hands the scope its
    /// expansion ended in; see `ScopeHandoff`.
    fn scope_handoff(&mut self) -> &mut ScopeHandoff;

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

    /// What a name that stands for a value of the scope itself, as `__ENV__`
    /// does, expands to where `scope` stands, or `None` when this expansion
    /// binds no such name.
    fn environment_splice(
        &mut self,
        _name: &str,
        _scope: ScopeSnapshot,
    ) -> Result<Option<QuotedSourceRoot>, fz_engine::FatalError> {
        Ok(None)
    }

    /// Moves `scope` forward by an `alias`, `import` or `require` written in a
    /// body. A module whose interface is not yet published blocks it.
    fn apply_scope_directive(
        &mut self,
        scope: ScopeSnapshot,
        directive: &ScopeForm,
    ) -> Result<DirectedScope, fz_engine::FatalError>;

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
            })? {
                if let Some(NamespaceSymbol::Splice(snippet)) = self.world().lookup_namespace(scope.namespace(), &name)
                {
                    return Ok(ExpandedValue::Complete(snippet.root()));
                }
                if let Some(snippet) = self.environment_splice(&name, scope)? {
                    return Ok(ExpandedValue::Complete(snippet.root()));
                }
            }
            if scope.is_rebound()
                && let Some(module_atom) = self.rebound_alias(owner, cursor, &node, scope)?
            {
                return Ok(ExpandedValue::Complete(module_atom));
            }
            let context = *self.expansion_context();
            if allow_root_sugar
                && let Some(rewritten) =
                    rewrite_source_sugar(owner, cursor.root(), &node, &source_map.borrow(), context).map_err(
                        |error| emit_surface_read_error(self.telemetry(), "source sugar rewrite failed", &error),
                    )?
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
            Some(head) if head == "__aliases__" && self.starts_with_a_node(&node.tail)? => {
                self.expand_alias_of_a_node(owner, cursor, node, scope, depth)
            }
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

    fn is_alias_of_a_node(&mut self, cursor: &QuotedSourceCursor) -> Result<bool, fz_engine::FatalError> {
        let source_map = self.world().source_map();
        let node = cursor.ast_node(&source_map.borrow()).map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted alias read failed: {error}"))
        })?;
        match node {
            Some(node) if node.head.root().tag() == ValueKind::ATOM && is_list_like(&node.tail) => {
                let is_alias = node.head.atom_name().is_ok_and(|name| &*name == "__aliases__");
                Ok(is_alias && self.starts_with_a_node(&node.tail)?)
            }
            _ => Ok(false),
        }
    }

    /// Whether the first segment of an alias is itself code, as the
    /// `__MODULE__` of `__MODULE__.Inner` is.
    fn starts_with_a_node(&mut self, segments: &QuotedSourceCursor) -> Result<bool, fz_engine::FatalError> {
        let source_map = self.world().source_map();
        let read_error = |error: QuotedSourceError| {
            emit_internal_surface_error(self.telemetry(), format!("quoted alias segment read failed: {error}"))
        };
        match segments.list_iter().next().transpose().map_err(read_error)? {
            Some(first) => Ok(first.ast_node(&source_map.borrow()).map_err(read_error)?.is_some()),
            None => Ok(false),
        }
    }

    /// `__MODULE__.Inner` expands as Elixir expands an alias whose first
    /// segment is a module's atom: to the atom of the module it names.
    fn expand_alias_of_a_node(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        node: &QuotedAstNode,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        let expanded = match self.expand_ast_node(owner, cursor, node, scope, depth)? {
            ExpandedValue::Complete(root) => root,
            blocked @ ExpandedValue::Blocked(_) => return Ok(blocked),
        };
        let source_map = self.world().source_map();
        let folded = fold_module_atom_alias(owner, &owner.subroot(expanded).cursor(), &source_map.borrow())
            .map_err(|error| emit_surface_read_error(self.telemetry(), "alias expansion failed", &error))?;
        Ok(ExpandedValue::Complete(folded.unwrap_or(expanded)))
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

        if scope.is_rebound()
            && let Some(result) = self.expand_rebound_capture(owner, node, arity, scope)?
        {
            return Ok(Some(result));
        }

        if is_remote_function_capture(node, &source_map.borrow()).map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted capture detection failed: {error}"))
        })? {
            return Ok(Some(ExpandedValue::Complete(cursor.root())));
        }

        let invocation = owner.subroot(cursor.root());
        match self.resolve_remote_macro_call(owner, node, scope, depth, arity)? {
            MacroCall::Macro(function) => {
                return self
                    .expand_macro_invocation(owner, invocation, function, scope, depth, &self.call_args(&node.tail)?)
                    .map(Some);
            }
            MacroCall::Blocked(effects) => return Ok(Some(ExpandedValue::Blocked(effects))),
            MacroCall::NotRequired(refusal) => return Err(refusal.error(self.telemetry())),
            MacroCall::NotAMacro => {}
        }

        if node.head.root().tag() != ValueKind::ATOM {
            return Ok(None);
        }
        let head = node.head.atom_name().map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted call head read failed: {error}"))
        })?;
        if head == "quote" {
            return self.expand_quoted_call(owner, cursor, node, scope, depth).map(Some);
        }
        if head == "when" && arity >= 2 {
            let args = self.call_args(&node.tail)?;
            return self
                .expand_when_call(owner, cursor, node, &args, scope, depth)
                .map(Some);
        }
        if scope.is_body() && head == "__block__" {
            return self.expand_body_block(owner, cursor, node, scope, depth).map(Some);
        }
        if scope.is_body() && is_scope_directive_head(&head) {
            return self.expand_lone_directive(owner, cursor, scope).map(Some);
        }
        if is_scope_definition_head(&head) {
            let args = self.call_args(&node.tail)?;
            let mut expanded = Vec::with_capacity(args.len());
            // A function's head names what it defines, so it is no call to
            // expand: the function's own expansion reads its parameters.
            let head_is_signature = is_function_definition_head(&head);
            for (index, arg) in args.iter().enumerate() {
                if index == 0 && head_is_signature {
                    expanded.push(arg.root());
                    continue;
                }
                let arg_scope = if head_is_signature { scope.in_body() } else { scope };
                let value = self.expand_cursor_with_root_sugar(owner, arg, arg_scope, depth, index != 0)?;
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
        let (bound, symbol) = self.local_call_symbol(node, scope, &head, arity)?;
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
            NamespaceSymbol::Function(function) => {
                if bound.is_none() && self.imported_by_the_body(scope, &head, arity, function) {
                    return self.expand_stamped_call(owner, node, function, scope, depth).map(Some);
                }
                return Ok(None);
            }
            NamespaceSymbol::Module(_) | NamespaceSymbol::Type(_) | NamespaceSymbol::Splice(_) => return Ok(None),
        };
        self.expand_macro_invocation(owner, invocation, function, scope, depth, &self.call_args(&node.tail)?)
            .map(Some)
    }

    /// What the scope binds the unqualified call `head/arity` to: the function
    /// the call was already stamped with, and its symbol.
    fn local_call_symbol(
        &mut self,
        node: &QuotedAstNode,
        scope: ScopeSnapshot,
        head: &str,
        arity: usize,
    ) -> Result<(Option<FunctionId>, Option<NamespaceSymbol>), fz_engine::FatalError> {
        let bound = read_bound_callable(node).map_err(|error| {
            emit_internal_surface_error(
                self.telemetry(),
                format!("quoted call classification read failed: {error}"),
            )
        })?;
        let symbol = call_node_symbol(self.world(), bound, scope, head, arity);
        Ok((bound, symbol))
    }

    /// The macro an unqualified call names, when it names one.
    fn resolve_local_macro_call(
        &mut self,
        node: &QuotedAstNode,
        scope: ScopeSnapshot,
        arity: usize,
    ) -> Result<MacroCall, fz_engine::FatalError> {
        if node.head.root().tag() != ValueKind::ATOM {
            return Ok(MacroCall::NotAMacro);
        }
        let head = node.head.atom_name().map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted call head read failed: {error}"))
        })?;
        Ok(match self.local_call_symbol(node, scope, &head, arity)?.1 {
            Some(NamespaceSymbol::Macro(function)) => MacroCall::Macro(function),
            Some(NamespaceSymbol::Callable(function)) => {
                MacroCall::Blocked(Box::new(self.wait_for_callable_module_interface(function)))
            }
            _ => MacroCall::NotAMacro,
        })
    }

    /// What `call` becomes after one step in `context`: the macro's result
    /// as the macro wrote it, nothing in it expanded. A call that is no macro
    /// stays as written, as does a qualified call of a module the scope does
    /// not `require`.
    fn expand_macro_call_once(
        &mut self,
        owner: &QuotedSourceRoot,
        call: &QuotedSourceCursor,
        context: ExpansionContext,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<MacroStep, fz_engine::FatalError> {
        let source_map = self.world().source_map();
        let node = call.ast_node(&source_map.borrow()).map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted expansion read failed: {error}"))
        })?;
        let Some(node) = node.filter(|node| is_list_like(&node.tail)) else {
            return Ok(MacroStep::NotAMacro);
        };
        let arity = node.tail.list_len().map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted call arg read failed: {error}"))
        })?;
        let enclosing = std::mem::replace(self.expansion_context(), context);
        let stepped = self.step_resolved_macro_call(owner, call, &node, scope, depth, arity);
        *self.expansion_context() = enclosing;
        stepped
    }

    fn step_resolved_macro_call(
        &mut self,
        owner: &QuotedSourceRoot,
        call: &QuotedSourceCursor,
        node: &QuotedAstNode,
        scope: ScopeSnapshot,
        depth: usize,
        arity: usize,
    ) -> Result<MacroStep, fz_engine::FatalError> {
        let resolved = match self.resolve_remote_macro_call(owner, node, scope, depth, arity)? {
            MacroCall::NotAMacro => self.resolve_local_macro_call(node, scope, arity)?,
            resolved => resolved,
        };
        match resolved {
            MacroCall::Macro(function) => {
                let invocation = owner.subroot(call.root());
                let args = self.call_args(&node.tail)?;
                Ok(
                    match self.macro_step(owner, &invocation, function, scope, depth, &args)? {
                        ExpandedValue::Complete(root) => MacroStep::Expanded(root),
                        ExpandedValue::Blocked(effects) => MacroStep::Blocked(effects),
                    },
                )
            }
            MacroCall::Blocked(effects) => Ok(MacroStep::Blocked(effects)),
            MacroCall::NotRequired(_) | MacroCall::NotAMacro => Ok(MacroStep::NotAMacro),
        }
    }

    /// Whether the call `name/arity` reaches `function` only through what the
    /// body itself imported: the definition's own scope names no such
    /// function, so lowering, which reads that scope, could not find it.
    fn imported_by_the_body(&mut self, scope: ScopeSnapshot, name: &str, arity: usize, function: FunctionId) -> bool {
        if !scope.is_rebound() {
            return false;
        }
        let origin = scope.body_origin().expect("a rebound scope is a body's");
        let resolved_there = self.world().lookup_callable_namespace(origin, name, arity);
        !matches!(
            resolved_there,
            Some(NamespaceSymbol::Function(there) | NamespaceSymbol::Callable(there)) if there == function
        )
    }

    /// A call the body's imports resolved, carrying the function it reached
    /// as the compiler's own stamp, with its arguments expanded.
    fn expand_stamped_call(
        &mut self,
        owner: &QuotedSourceRoot,
        node: &QuotedAstNode,
        function: FunctionId,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        let stamped = stamp_bound_callable(owner, node, function).map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("bound callable stamping failed: {error}"))
        })?;
        let stamped = owner.subroot(stamped);
        let source_map = self.world().source_map();
        let stamped_node = stamped
            .cursor()
            .ast_node(&source_map.borrow())
            .map_err(|error| {
                emit_internal_surface_error(self.telemetry(), format!("stamped call read failed: {error}"))
            })?
            .expect("a stamped call is a node");
        self.expand_ast_node(owner, &stamped.cursor(), &stamped_node, scope, depth)
    }

    /// `&name/arity` and `&Alias.name/arity` where the body's own directives
    /// have moved the scope: a function the body imported is captured by its
    /// module, and a body alias is the module it names, as lowering reads only
    /// the definition's scope. `None` for any other capture.
    fn expand_rebound_capture(
        &mut self,
        owner: &QuotedSourceRoot,
        node: &QuotedAstNode,
        arity: usize,
        scope: ScopeSnapshot,
    ) -> Result<Option<ExpandedValue>, fz_engine::FatalError> {
        let source_map = self.world().source_map();
        let read_failed = |tel: &Self::Telemetry, error: QuotedSourceError| {
            emit_internal_surface_error(tel, format!("quoted capture read failed: {error}"))
        };
        if arity != 1 || node.head.root().tag() != ValueKind::ATOM || node.head.atom_name().is_ok_and(|n| n != "&") {
            return Ok(None);
        }
        let operand = node
            .tail
            .list_items()
            .map_err(|e| read_failed(self.telemetry(), e))?
            .remove(0);
        let Some(slash) = operand
            .ast_node(&source_map.borrow())
            .map_err(|e| read_failed(self.telemetry(), e))?
        else {
            return Ok(None);
        };
        if slash.head.root().tag() != ValueKind::ATOM
            || slash.head.atom_name().is_ok_and(|n| n != "/")
            || !is_list_like(&slash.tail)
        {
            return Ok(None);
        }
        let parts = slash.tail.list_items().map_err(|e| read_failed(self.telemetry(), e))?;
        let [target, capture_arity] = parts.as_slice() else {
            return Ok(None);
        };
        if capture_arity.root().tag() != ValueKind::INT {
            return Ok(None);
        }
        let Some(target_node) = target
            .ast_node(&source_map.borrow())
            .map_err(|e| read_failed(self.telemetry(), e))?
        else {
            return Ok(None);
        };
        let builder = owner.builder();
        let new_target = if super::quoted_function::is_no_parens_call(&target_node)
            .map_err(|e| read_failed(self.telemetry(), e))?
        {
            let Some(dot) = target_node
                .head
                .ast_node(&source_map.borrow())
                .map_err(|e| read_failed(self.telemetry(), e))?
            else {
                return Ok(None);
            };
            let Some((module, function)) = dot.tail.list_pair().map_err(|e| read_failed(self.telemetry(), e))? else {
                return Ok(None);
            };
            let Some(module_node) = module
                .ast_node(&source_map.borrow())
                .map_err(|e| read_failed(self.telemetry(), e))?
            else {
                return Ok(None);
            };
            let Some(module_atom) = self.rebound_alias(owner, &module, &module_node, scope)? else {
                return Ok(None);
            };
            let dot_tail = builder
                .list(&[module_atom, function.root()])
                .map_err(|e| read_failed(self.telemetry(), e))?;
            let dot_head = builder
                .tuple(&[dot.head.root(), dot.meta.root(), dot_tail])
                .map_err(|e| read_failed(self.telemetry(), e))?;
            builder
                .tuple(&[dot_head, target_node.meta.root(), target_node.tail.root()])
                .map_err(|e| read_failed(self.telemetry(), e))?
        } else {
            if target_node.head.root().tag() != ValueKind::ATOM || is_list_like(&target_node.tail) {
                return Ok(None);
            }
            let name = target_node
                .head
                .atom_name()
                .map_err(|e| read_failed(self.telemetry(), e))?;
            let wanted = usize::try_from(
                capture_arity
                    .int_value()
                    .map_err(|e| read_failed(self.telemetry(), e))?,
            )
            .unwrap_or(usize::MAX);
            let function = match self.world().lookup_callable_namespace(scope.namespace(), &name, wanted) {
                Some(NamespaceSymbol::Callable(function)) => {
                    return Ok(Some(ExpandedValue::Blocked(Box::new(
                        self.wait_for_callable_module_interface(function),
                    ))));
                }
                Some(NamespaceSymbol::Function(function))
                    if self.imported_by_the_body(scope, &name, wanted, function) =>
                {
                    function
                }
                _ => return Ok(None),
            };
            let world = self.world();
            let module = world.function_module(function);
            let module_atom = world.module_atom_value(&builder, module);
            let span = target_node.span.unwrap_or(Span::DUMMY);
            let meta = builder
                .meta(&QuotedSourceMetadata {
                    no_parens: true,
                    span: Some(span),
                    ..QuotedSourceMetadata::default()
                })
                .map_err(|e| read_failed(self.telemetry(), e))?;
            let dot_tail = builder
                .list(&[module_atom, builder.atom(&name)])
                .map_err(|e| read_failed(self.telemetry(), e))?;
            let dot_head = builder
                .tuple(&[builder.atom("."), target_node.meta.root(), dot_tail])
                .map_err(|e| read_failed(self.telemetry(), e))?;
            let empty = builder.list(&[]).map_err(|e| read_failed(self.telemetry(), e))?;
            builder
                .tuple(&[dot_head, meta, empty])
                .map_err(|e| read_failed(self.telemetry(), e))?
        };
        let slash_tail = builder
            .list(&[new_target, capture_arity.root()])
            .map_err(|e| read_failed(self.telemetry(), e))?;
        let new_slash = builder
            .tuple(&[slash.head.root(), slash.meta.root(), slash_tail])
            .map_err(|e| read_failed(self.telemetry(), e))?;
        let tail = builder
            .list(&[new_slash])
            .map_err(|e| read_failed(self.telemetry(), e))?;
        let rebuilt = builder
            .tuple(&[node.head.root(), node.meta.root(), tail])
            .map_err(|e| read_failed(self.telemetry(), e))?;
        Ok(Some(ExpandedValue::Complete(rebuilt)))
    }

    /// The module an alias names where the body's own `alias` has moved the
    /// scope, as the atom the alias stands for: a body alias is gone from the
    /// tree once expanded, and lowering reads only the definition's scope.
    fn rebound_alias(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        node: &QuotedAstNode,
        scope: ScopeSnapshot,
    ) -> Result<Option<AnyValueRef>, fz_engine::FatalError> {
        if node.head.root().tag() != ValueKind::ATOM
            || !is_list_like(&node.tail)
            || node.head.atom_name().is_ok_and(|name| name != "__aliases__")
            || self.starts_with_a_node(&node.tail)?
        {
            return Ok(None);
        }
        let source_map = self.world().source_map();
        let Some(path) = alias_path(cursor, &source_map.borrow()).map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted alias read failed: {error}"))
        })?
        else {
            return Ok(None);
        };
        let world = self.world();
        let module = world.resolve_module_name(scope.namespace(), &ModuleName::from_segments(path));
        Ok(Some(world.module_atom_value(&owner.builder(), module)))
    }

    /// The statements of a body's block, each in the scope the ones before it
    /// left. An `alias`, `import` or `require` moves the scope for the rest of
    /// the block and is gone from the tree, unless it is the last statement,
    /// whose value it is. A block nested in a statement inherits the scope and
    /// hands nothing back, so a branch's import ends with the branch.
    fn expand_body_block(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        node: &QuotedAstNode,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        let statements = self.call_args(&node.tail)?;
        match self.walk_body_statements(owner, &statements, scope, depth)? {
            BodyWalk::Blocked(effects) => Ok(ExpandedValue::Blocked(effects)),
            BodyWalk::Done { expanded, .. } => self.rebuild_call(owner, cursor, node, &statements, &expanded),
        }
    }

    /// Expands `statements` in order, each in the scope the directives before
    /// it have made, and answers the scope the last one leaves.
    fn walk_body_statements(
        &mut self,
        owner: &QuotedSourceRoot,
        statements: &[QuotedSourceCursor],
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<BodyWalk, fz_engine::FatalError> {
        let mut scope = scope;
        let mut expanded = Vec::with_capacity(statements.len());
        for (index, statement) in statements.iter().enumerate() {
            let is_last = index + 1 == statements.len();
            let Some(directive) = self.read_directive(owner, statement)? else {
                *self.scope_handoff() = ScopeHandoff {
                    statement: Some(statement.root()),
                    scope: None,
                };
                match self.expand_cursor(owner, statement, scope, depth)? {
                    ExpandedValue::Complete(value) => expanded.push(value),
                    ExpandedValue::Blocked(effects) => return Ok(BodyWalk::Blocked(effects)),
                }
                let handoff = std::mem::take(self.scope_handoff());
                if handoff.statement == Some(statement.root())
                    && let Some(handed) = handoff.scope
                {
                    scope = handed;
                }
                continue;
            };
            let module = self.directive_module(scope, &directive);
            match self.apply_scope_directive(scope, &directive)? {
                DirectedScope::Moved(next) => scope = next,
                DirectedScope::Blocked(effects) => return Ok(BodyWalk::Blocked(effects)),
            }
            if is_last {
                let world = self.world();
                expanded.push(world.module_atom_value(&owner.builder(), module));
            }
        }
        Ok(BodyWalk::Done { expanded, scope })
    }

    /// A macro's result, expanded where the call stands. A call that is a
    /// statement of a body block expands its result as statements of that
    /// block and hands the scope they end in back to it.
    fn expand_macro_result(
        &mut self,
        invocation: &QuotedSourceRoot,
        result: QuotedSourceRoot,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        let is_statement = scope.is_body() && self.scope_handoff().statement == Some(invocation.root());
        if !is_statement {
            return match self.expand_root(result, scope, depth)? {
                ExpandedRoot::Complete(root) => Ok(ExpandedValue::Complete(root.root())),
                ExpandedRoot::Blocked(effects) => Ok(ExpandedValue::Blocked(effects)),
            };
        }
        let source_map = self.world().source_map();
        let block = result
            .cursor()
            .ast_node(&source_map.borrow())
            .map_err(|error| {
                emit_internal_surface_error(self.telemetry(), format!("macro result read failed: {error}"))
            })?
            .filter(|node| node.head.atom_name().is_ok_and(|name| name == "__block__") && is_list_like(&node.tail));
        let (statements, block) = match block {
            Some(node) => (self.call_args(&node.tail)?, Some(node)),
            None => (vec![result.cursor()], None),
        };
        let (expanded, ending) = match self.walk_body_statements(&result, &statements, scope, depth)? {
            BodyWalk::Blocked(effects) => return Ok(ExpandedValue::Blocked(effects)),
            BodyWalk::Done { expanded, scope } => (expanded, scope),
        };
        let value = match block {
            Some(node) => self.rebuild_call(&result, &result.cursor(), &node, &statements, &expanded)?,
            None => ExpandedValue::Complete(expanded[0]),
        };
        *self.scope_handoff() = ScopeHandoff {
            statement: Some(invocation.root()),
            scope: Some(ending),
        };
        Ok(value)
    }

    /// An `alias`, `import` or `require` standing alone, where its scope
    /// reaches no further statement: it applies, so that it is refused when it
    /// is wrong, and its value is the module.
    fn expand_lone_directive(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        scope: ScopeSnapshot,
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        let directive = self
            .read_directive(owner, cursor)?
            .expect("the head says this is a directive");
        let module = self.directive_module(scope, &directive);
        match self.apply_scope_directive(scope, &directive)? {
            DirectedScope::Moved(_) => {}
            DirectedScope::Blocked(effects) => return Ok(ExpandedValue::Blocked(effects)),
        }
        let world = self.world();
        Ok(ExpandedValue::Complete(
            world.module_atom_value(&owner.builder(), module),
        ))
    }

    fn read_directive(
        &mut self,
        owner: &QuotedSourceRoot,
        statement: &QuotedSourceCursor,
    ) -> Result<Option<ScopeForm>, fz_engine::FatalError> {
        let source_map = self.world().source_map();
        let Some(node) = statement.ast_node(&source_map.borrow()).map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("body statement read failed: {error}"))
        })?
        else {
            return Ok(None);
        };
        let is_directive = node.head.root().tag() == ValueKind::ATOM
            && is_list_like(&node.tail)
            && node.head.atom_name().is_ok_and(|name| is_scope_directive_head(&name));
        if !is_directive {
            return Ok(None);
        }
        let root = owner.subroot(statement.root());
        read_scope_directive(&root, &source_map.borrow())
            .map_err(|error| emit_surface_read_error(self.telemetry(), "body directive read failed", &error))
    }

    /// The module the directive names, which is the value of the statement.
    fn directive_module(&mut self, scope: ScopeSnapshot, directive: &ScopeForm) -> ModuleId {
        super::scope_directives::directive_module(self.world(), scope.namespace(), directive)
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
    /// A `quote` is data except for its `unquote`s, each of which holds code
    /// the enclosing function runs. That code expands as any other does, for
    /// its `@name` reads and macro calls; the rest of the quote stays as
    /// written, a nested `quote` with it.
    fn expand_quoted_unquotes(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        let source_map = self.world().source_map();
        let node = cursor.ast_node(&source_map.borrow()).map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted code read failed: {error}"))
        })?;
        let Some(node) = node else {
            return self.expand_quoted_collection(owner, cursor, scope, depth);
        };
        let nested_quote =
            node.head.root().tag() == ValueKind::ATOM && node.head.atom_name().is_ok_and(|name| name == "quote");
        if nested_quote {
            return Ok(ExpandedValue::Complete(cursor.root()));
        }
        self.expand_quoted_call(owner, cursor, &node, scope, depth)
    }

    /// One call of quoted code: an `unquote` expands its argument, any other
    /// call keeps its name and looks in its parts for `unquote`s.
    fn expand_quoted_call(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        node: &QuotedAstNode,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        let builder = owner.builder();
        let head_is_atom = node.head.root().tag() == ValueKind::ATOM;
        let head_name = if head_is_atom {
            Some(node.head.atom_name().map_err(|error| {
                emit_internal_surface_error(self.telemetry(), format!("quoted call head read failed: {error}"))
            })?)
        } else {
            None
        };
        let args = if is_list_like(&node.tail) {
            self.call_args(&node.tail)?
        } else {
            return Ok(ExpandedValue::Complete(cursor.root()));
        };
        let unquote = matches!(head_name.as_deref(), Some("unquote" | "unquote_splicing"));
        let head = if head_is_atom {
            ExpandedValue::Complete(node.head.root())
        } else {
            self.expand_quoted_unquotes(owner, &node.head, scope, depth)?
        };
        let ExpandedValue::Complete(head) = head else {
            return Ok(head);
        };
        let mut expanded = Vec::with_capacity(args.len());
        for arg in &args {
            let value = if unquote {
                self.expand_cursor(owner, arg, scope, depth)?
            } else {
                self.expand_quoted_unquotes(owner, arg, scope, depth)?
            };
            match value {
                ExpandedValue::Complete(value) => expanded.push(value),
                blocked @ ExpandedValue::Blocked(_) => return Ok(blocked),
            }
        }
        let unchanged =
            head == node.head.root() && expanded.iter().copied().eq(args.iter().map(QuotedSourceCursor::root));
        if unchanged {
            return Ok(ExpandedValue::Complete(cursor.root()));
        }
        builder
            .list(&expanded)
            .and_then(|tail| builder.tuple(&[head, node.meta.root(), tail]))
            .map(ExpandedValue::Complete)
            .map_err(|error| {
                emit_internal_surface_error(self.telemetry(), format!("quoted call rebuild failed: {error}"))
            })
    }

    /// The quoted code that is not a call: a list of it, or a pair.
    fn expand_quoted_collection(
        &mut self,
        owner: &QuotedSourceRoot,
        cursor: &QuotedSourceCursor,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<ExpandedValue, fz_engine::FatalError> {
        let items = match cursor.root().tag() {
            ValueKind::LIST => cursor.list_items(),
            ValueKind::STRUCT if cursor.tuple_arity().is_ok_and(|arity| arity == 2) => cursor.tuple_items(),
            _ => return Ok(ExpandedValue::Complete(cursor.root())),
        }
        .map_err(|error| emit_internal_surface_error(self.telemetry(), format!("quoted code read failed: {error}")))?;
        let mut expanded = Vec::with_capacity(items.len());
        for item in &items {
            match self.expand_quoted_unquotes(owner, item, scope, depth)? {
                ExpandedValue::Complete(value) => expanded.push(value),
                blocked @ ExpandedValue::Blocked(_) => return Ok(blocked),
            }
        }
        if expanded.iter().copied().eq(items.iter().map(QuotedSourceCursor::root)) {
            return Ok(ExpandedValue::Complete(cursor.root()));
        }
        let builder = owner.builder();
        let rebuilt = if cursor.root().tag() == ValueKind::LIST {
            builder.list(&expanded)
        } else {
            builder.tuple(&expanded)
        };
        rebuilt.map(ExpandedValue::Complete).map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted code rebuild failed: {error}"))
        })
    }

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

    /// The macro a qualified call `Module.name(args)` names, when it names one:
    /// in the module being defined, one the scope imports, or one `require`d.
    fn resolve_remote_macro_call(
        &mut self,
        owner: &QuotedSourceRoot,
        node: &QuotedAstNode,
        scope: ScopeSnapshot,
        depth: usize,
        arity: usize,
    ) -> Result<MacroCall, fz_engine::FatalError> {
        let source_map = self.world().source_map();
        let Some(head_node) = node.head.ast_node(&source_map.borrow()).map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted remote call read failed: {error}"))
        })?
        else {
            return Ok(MacroCall::NotAMacro);
        };
        let call_span = node.span.unwrap_or(Span::DUMMY);
        if !is_remote_dot_callee(&head_node).map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted remote callee read failed: {error}"))
        })? {
            return Ok(MacroCall::NotAMacro);
        }
        // `lhs[key]` is an index the decoder reads off its callee's stamp; it
        // calls into no module, whatever name the callee spells.
        if super::quoted_function::is_bracket_access_callee(&head_node).map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted bracket access read failed: {error}"))
        })? {
            return Ok(MacroCall::NotAMacro);
        }
        let Some((module_cursor, function_cursor)) = head_node.tail.list_pair().map_err(|error| {
            emit_internal_surface_error(self.telemetry(), format!("quoted remote target read failed: {error}"))
        })?
        else {
            return Ok(MacroCall::NotAMacro);
        };
        let module_cursor = if self.is_alias_of_a_node(&module_cursor)? {
            match self.expand_cursor(owner, &module_cursor, scope, depth)? {
                ExpandedValue::Complete(root) => owner.subroot(root).cursor(),
                ExpandedValue::Blocked(effects) => return Ok(MacroCall::Blocked(effects)),
            }
        } else {
            module_cursor
        };
        let (module_cursor, function_cursor) = (&module_cursor, &function_cursor);
        let atom_module = super::quoted_function::module_atom(module_cursor);
        let module_path = match &atom_module {
            Some(name) => name.segments().to_vec(),
            None => match alias_path(module_cursor, &source_map.borrow()).map_err(|error| {
                emit_internal_surface_error(self.telemetry(), format!("quoted remote module read failed: {error}"))
            })? {
                Some(path) => path,
                None => return Ok(MacroCall::NotAMacro),
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
            match atom_module {
                Some(name) => world.reference_module(name),
                None => world.resolve_module_name(scope.namespace(), &ModuleName::from_segments(module_path.clone())),
            }
        };
        if module == self.current_module() {
            return self.resolve_current_module_remote_macro_call(
                scope,
                arity,
                &function_name,
                &module_path,
                call_span,
            );
        }
        if let Some(symbol) = self.imported_symbol_of(module, &function_name, arity, &scope) {
            return match symbol {
                NamespaceSymbol::Macro(function) => Ok(MacroCall::Macro(function)),
                NamespaceSymbol::Callable(function) => {
                    self.note_call_into(module, &function_name, arity, call_span);
                    Ok(MacroCall::Blocked(Box::new(
                        self.wait_for_callable_module_interface(function),
                    )))
                }
                _ => Ok(MacroCall::NotAMacro),
            };
        }
        let module_defined = self.world().module_defined_revision(module);
        if module_defined.is_none() {
            if self.world().is_runtime_module(module) {
                return Ok(MacroCall::NotAMacro);
            }
            self.note_call_into(module, &function_name, arity, call_span);
            // `FactKey::ModuleDefined`'s sole producer arm is `Job::DefineModule`
            // (`World::demand_fact_producer`); the `is_global()` split this bare
            // wait used to make (never pushing for a global module) is defensive,
            // not reachable in practice -- `ModuleId::GLOBAL` is defined before
            // any expansion runs, so `module_defined.is_none()` is never true for
            // it here.
            return Ok(MacroCall::Blocked(Box::new(JobEffects::wait_on_current(
                FactKey::ModuleDefined(module),
            ))));
        }
        self.note_read(FactKey::ModuleDefined(module));
        let function = {
            let world = self.world();
            match world.lookup_module_callable(module, &function_name, arity) {
                Some(NamespaceSymbol::Macro(function)) => Some(function),
                Some(NamespaceSymbol::Callable(function)) => {
                    self.note_call_into(module, &function_name, arity, call_span);
                    return Ok(MacroCall::Blocked(Box::new(
                        self.wait_for_callable_module_interface(function),
                    )));
                }
                _ => None,
            }
        };
        let Some(function) = function else {
            return Ok(MacroCall::NotAMacro);
        };
        if !self.world().macro_callable_remotely(scope.namespace(), function) {
            return Ok(MacroCall::NotRequired(NotRequired {
                name: function_name.to_string(),
                arity,
                module_path,
                span: call_span,
            }));
        }
        Ok(MacroCall::Macro(function))
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

    fn resolve_current_module_remote_macro_call(
        &mut self,
        scope: ScopeSnapshot,
        arity: usize,
        function_name: &str,
        module_path: &[String],
        call_span: Span,
    ) -> Result<MacroCall, fz_engine::FatalError> {
        let Some(function) = self.lookup_current_module_macro(scope, function_name, arity) else {
            return Ok(MacroCall::NotAMacro);
        };
        if !self.world().macro_callable_remotely(scope.namespace(), function) {
            return Ok(MacroCall::NotRequired(NotRequired {
                name: function_name.to_string(),
                arity,
                module_path: module_path.to_vec(),
                span: call_span,
            }));
        }
        Ok(MacroCall::Macro(function))
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
        let result = match self.macro_step(owner, &invocation, function, scope, depth, args)? {
            ExpandedValue::Complete(result) => owner.subroot(result),
            blocked @ ExpandedValue::Blocked(_) => return Ok(blocked),
        };
        let expanded = self.expand_macro_result(&invocation, result, scope, depth + 1)?;
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

    /// What the macro `function` answers for `invocation`: its result, as the
    /// macro wrote it, with the hygiene stamped and nothing in it expanded.
    /// The run is memoized by what the macro can see.
    fn macro_step(
        &mut self,
        owner: &QuotedSourceRoot,
        invocation: &QuotedSourceRoot,
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

        let caller_scope = scope;
        // The call site every unlocated node in this macro's result falls
        // back to (`stamp_span_fallback`) -- read from `invocation` itself,
        // which is always either the user's own source (real span from the
        // parser) or an earlier macro's already-stamped result (real span
        // from that expansion, by the same rule, one level up).
        let macro_call_span = self.invocation_span(invocation)?;
        // Drawn once this invocation is committed to (past both blocking
        // checks above), whether it turns out to hit the memoization cache
        // or not -- see `next_expansion_number`.
        let expansion_number = self.next_expansion_number();
        let context = *self.expansion_context();
        let call_site = CallSite::locate(macro_call_span, &self.world().source_map().borrow());
        if let Some(memoized) =
            self.world()
                .memoized_macro_expansion(function, invocation, caller_scope, context, &call_site, &program)
        {
            self.emit_macro_warnings(&memoized.warnings, macro_call_span);
            for _ in 0..memoized.answered_expansions {
                self.next_expansion_number();
            }
            return Ok(ExpandedValue::Complete(memoized.root.root()));
        }

        let builder = owner.builder();
        let caller = self
            .world()
            .project_env_value(&builder, caller_scope, context, &call_site)
            .map_err(|error| {
                emit_internal_surface_error(self.telemetry(), format!("__ENV__ projection failed: {error}"))
            })?;
        let arg_roots = args.iter().map(QuotedSourceCursor::root).collect::<Vec<_>>();
        let visited_before = self.expansions_visited();
        let mut answers = Vec::new();
        let (expanded, warnings) = loop {
            let (world, tel) = self.split();
            let run = super::drive::ExecutionContext::new(world, tel)
                .run_macro_on_source(&program, owner, caller, &arg_roots, &answers)
                .map_err(|error| {
                    let span = macro_call_span.unwrap_or(Span::DUMMY);
                    emit_job_diagnostic(tel, Diagnostic::error(codes::LOWER_UNSUPPORTED, error, span))
                })?;
            match run {
                MacroRun::Finished { root, warnings } => break (root, warnings),
                MacroRun::Asked(request) => {
                    match self.answer_expansion_request(owner, request, caller_scope, depth)? {
                        Answered::Ready(answer) => answers.push(answer),
                        Answered::Blocked(effects) => return Ok(ExpandedValue::Blocked(effects)),
                    }
                }
            }
        };
        let answered_expansions = self.expansions_visited() - visited_before;
        let (world, tel) = self.split();
        let source_map = world.source_map();
        if let Some(invalid) = first_invalid_quoted_expr(&expanded.cursor(), &source_map.borrow())
            .map_err(|error| emit_internal_surface_error(tel, format!("macro result validation failed: {error}")))?
        {
            let value = invalid.inspect().map_err(|error| {
                emit_internal_surface_error(tel, format!("macro result inspection failed: {error}"))
            })?;
            // An evaluator stands for code the source wrote, so there is no
            // macro to name.
            let macro_label =
                (!is_evaluator_name(world.function_ref(function).name())).then(|| function_label(world, function));
            return Err(invalid_quoted_expr(
                tel,
                macro_label.as_deref(),
                &value,
                macro_call_span.unwrap_or(Span::DUMMY),
            ));
        }
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
            invocation.clone(),
            caller_scope,
            context,
            call_site,
            &program,
            MacroExpansion {
                root: expanded.clone(),
                warnings: warnings.clone(),
                answered_expansions,
            },
        );
        self.emit_macro_warnings(&warnings, macro_call_span);
        Ok(ExpandedValue::Complete(expanded.root()))
    }

    /// Answers a question a macro body asked: what its call is after one step
    /// in the scope the macro was called from.
    fn answer_expansion_request(
        &mut self,
        owner: &QuotedSourceRoot,
        request: ExpansionRequest,
        scope: ScopeSnapshot,
        depth: usize,
    ) -> Result<Answered, fz_engine::FatalError> {
        let call = owner.subroot(request.call).cursor();
        Ok(
            match self.expand_macro_call_once(owner, &call, request.context, scope, depth + 1)? {
                MacroStep::NotAMacro => Answered::Ready(ExpansionAnswer::NotAMacro),
                MacroStep::Expanded(root) => Answered::Ready(ExpansionAnswer::Expanded(root)),
                MacroStep::Blocked(effects) => Answered::Blocked(effects),
            },
        )
    }

    /// Reports what a macro's run warned, as it does for a run and for a memo
    /// hit alike; a warning already reported this drive is not reported twice.
    fn emit_macro_warnings(&mut self, warnings: &[MacroWarning], macro_call_span: Option<Span>) {
        let (world, telemetry) = self.split();
        for warning in warnings {
            let diagnostic = warning.diagnostic(macro_call_span, &world.source_map().borrow());
            super::drive::ExecutionContext::new(world, telemetry).emit_warning_once(diagnostic);
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
/// The heads of the three forms that move a scope forward.
fn is_scope_directive_head(head: &str) -> bool {
    matches!(head, "alias" | "import" | "require")
}

/// `node` with its metadata retaining `function` as the callable it names.
fn stamp_bound_callable(
    owner: &QuotedSourceRoot,
    node: &QuotedAstNode,
    function: FunctionId,
) -> Result<AnyValueRef, QuotedSourceError> {
    let builder = owner.builder();
    let mut entries = Vec::new();
    for entry in node.meta.list_iter() {
        let pair = entry?.tuple_items()?;
        if pair[0].atom_name()? != META_BOUND_CALLABLE_KEY {
            entries.push((pair[0].root(), pair[1].root()));
        }
    }
    entries.push((
        builder.atom(META_BOUND_CALLABLE_KEY),
        builder.int(i64::from(function.as_u32())),
    ));
    let meta = builder.keyword_list(&entries)?;
    builder.tuple(&[node.head.root(), meta, node.tail.root()])
}

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
    let surface = read_expanded_items(ctx.telemetry(), &owner.subroot(expanded), &source_map.borrow())?;
    Ok(ExpandedScopeFragment::Complete(surface))
}

/// The definitions a macro's expansion makes, read as a surface: a list is
/// its elements, a block is its statements, and anything else is the one
/// item.
pub(crate) fn read_expanded_items(
    tel: &impl crate::telemetry::Telemetry,
    expansion: &QuotedSourceRoot,
    sources: &SourceMap,
) -> Result<ScopeSurface, fz_engine::FatalError> {
    let items = item_macro_fragment_root(tel, expansion, sources)?;
    read_compiler_fragment_root(tel, &items, "item macro expanded source", sources)
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

/// The outermost part of `cursor` that is not valid quoted syntax, by
/// Elixir's grammar: an atom, number, binary, list or two-tuple of valid
/// parts, or a call node `{head, meta, args}` (a variable node carries an atom
/// where the arguments go). Maps, functions, pids and tuples of any other size
/// are values that must be escaped to enter the syntax. The one exception is
/// the environment argument of `Fz.Compiler.define`, the details of an
/// `extern` form and the lexer tokens a type expression carries: values the
/// compiler's own forms embed.
fn first_invalid_quoted_expr(
    cursor: &QuotedSourceCursor,
    sources: &SourceMap,
) -> Result<Option<QuotedSourceCursor>, QuotedSourceError> {
    let tag = cursor.root().tag();
    if [
        ValueKind::ATOM,
        ValueKind::INT,
        ValueKind::FLOAT,
        ValueKind::BITSTRING,
        ValueKind::BINVIEW,
        ValueKind::BINREF,
    ]
    .contains(&tag)
    {
        return Ok(None);
    }
    let invalid_unless_readable = |items: Result<Vec<QuotedSourceCursor>, QuotedSourceError>| match items {
        Ok(items) => first_invalid_among(&items, sources),
        Err(_) => Ok(Some(cursor.clone())),
    };
    if tag == ValueKind::LIST {
        return invalid_unless_readable(cursor.list_iter().collect());
    }
    if tag != ValueKind::STRUCT {
        return Ok(Some(cursor.clone()));
    }
    match cursor.tuple_arity()? {
        2 => invalid_unless_readable(cursor.tuple_items()),
        3 => first_invalid_call_node(cursor, sources),
        _ if decode_token(cursor, sources).is_ok() => Ok(None),
        _ => Ok(Some(cursor.clone())),
    }
}

fn first_invalid_among(
    items: &[QuotedSourceCursor],
    sources: &SourceMap,
) -> Result<Option<QuotedSourceCursor>, QuotedSourceError> {
    for item in items {
        if let Some(invalid) = first_invalid_quoted_expr(item, sources)? {
            return Ok(Some(invalid));
        }
    }
    Ok(None)
}

fn first_invalid_call_node(
    cursor: &QuotedSourceCursor,
    sources: &SourceMap,
) -> Result<Option<QuotedSourceCursor>, QuotedSourceError> {
    let Ok(Some(node)) = cursor.ast_node(sources) else {
        return Ok(Some(cursor.clone()));
    };
    let head_tag = node.head.root().tag();
    let tail_tag = node.tail.root().tag();
    if (head_tag != ValueKind::ATOM && head_tag != ValueKind::STRUCT)
        || (tail_tag != ValueKind::ATOM && tail_tag != ValueKind::LIST)
    {
        return Ok(Some(cursor.clone()));
    }
    if let Some(invalid) = first_invalid_quoted_expr(&node.head, sources)? {
        return Ok(Some(invalid));
    }
    if tail_tag == ValueKind::ATOM {
        return Ok(None);
    }
    let args = match node.tail.list_iter().collect::<Result<Vec<_>, _>>() {
        Ok(args) => args,
        Err(_) => return Ok(Some(node.tail)),
    };
    if is_compiler_define_call(&node, args.len(), sources).unwrap_or(false) || is_extern_form(&node, args.len()) {
        return first_invalid_among(&args[..1], sources);
    }
    first_invalid_among(&args, sources)
}

/// A macro returned something that is not quoted syntax: Elixir's
/// `invalid quoted expression` error, naming the macro it came from.
fn invalid_quoted_expr(
    tel: &impl crate::telemetry::Telemetry,
    macro_label: Option<&str>,
    value: &str,
    span: Span,
) -> fz_engine::FatalError {
    let diagnostic = Diagnostic::error(
        codes::MACRO_INVALID_QUOTED_EXPR,
        format!(
            "invalid quoted expression: {value}\n\n\
                 Please make sure your quoted expressions are made of valid AST nodes. \
                 If you would like to introduce a value into the AST, such as a four-element \
                 tuple or a map, make sure to call Macro.escape/1 before"
        ),
        span,
    );
    emit_job_diagnostic(
        tel,
        match macro_label {
            Some(label) => diagnostic.with_note(format!("expanding macro: {label}")),
            None => diagnostic,
        },
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

/// The front door's `extern(abi, details)` form: its details are a map the
/// compiler reads back, not syntax.
fn is_extern_form(node: &QuotedAstNode, arity: usize) -> bool {
    arity == 2 && node.head.root().tag() == ValueKind::ATOM && node.head.atom_name().is_ok_and(|name| name == "extern")
}

/// `&Mod.fun/1`: the target names a function and calls nothing, so it is not a
/// remote call to expand.
fn is_remote_function_capture(node: &QuotedAstNode, sources: &SourceMap) -> Result<bool, QuotedSourceError> {
    if node.head.root().tag() != ValueKind::ATOM || node.head.atom_name()? != "&" {
        return Ok(false);
    }
    let operands = node.tail.list_items()?;
    let [operand] = operands.as_slice() else {
        return Ok(false);
    };
    let Some(slash) = operand.ast_node(sources)? else {
        return Ok(false);
    };
    if slash.head.root().tag() != ValueKind::ATOM || slash.head.atom_name()? != "/" {
        return Ok(false);
    }
    let parts = slash.tail.list_items()?;
    let [target, arity] = parts.as_slice() else {
        return Ok(false);
    };
    let Some(target) = target.ast_node(sources)? else {
        return Ok(false);
    };
    Ok(arity.root().tag() == ValueKind::INT && super::quoted_function::is_no_parens_call(&target)?)
}

/// An alias that starts with a module's atom (`__MODULE__` once expanded) is
/// the atom of the module it names; one that starts with `nil` (`__MODULE__`
/// outside any module) is the alias of its remaining segments, as
/// `Module.concat/1` ignores `nil`. `None` for any other alias.
fn fold_module_atom_alias(
    owner: &QuotedSourceRoot,
    alias: &QuotedSourceCursor,
    sources: &SourceMap,
) -> Result<Option<AnyValueRef>, QuotedSourceError> {
    let Some(node) = alias.ast_node(sources)? else {
        return Ok(None);
    };
    let segments = node.tail.list_items()?;
    let Some((first, rest)) = segments.split_first() else {
        return Ok(None);
    };
    if first.root().tag() != ValueKind::ATOM {
        return Ok(None);
    }
    let builder = owner.builder();
    let first_name = first.atom_name()?;
    if &*first_name == "nil" {
        let rest = rest.iter().map(QuotedSourceCursor::root).collect::<Vec<_>>();
        return Ok(Some(builder.tuple(&[
            node.head.root(),
            node.meta.root(),
            builder.list(&rest)?,
        ])?));
    }
    let Some(module) = ModuleName::from_atom_name(&first_name).filter(|_| first_name.starts_with("Elixir.")) else {
        return Ok(None);
    };
    let module = rest.iter().try_fold(module, |module, segment| {
        segment.atom_name().map(|name| module.child(name.to_string()))
    })?;
    Ok(Some(builder.atom(&module.atom_name())))
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
