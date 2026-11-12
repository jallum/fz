//! Source-only rewrites over compiler2 quoted AST.
//!
//! These rules remove syntax sugar during staged function expansion, after raw
//! `FunctionSource` publication and before `DefineFunction` decodes the body.

use fz_runtime::any_value::{AnyValueRef, ValueKind};

use super::source::{
    META_FROM_OPERATOR_KEY, QuotedAstNode, QuotedSourceBuilder, QuotedSourceCursor, QuotedSourceError,
    QuotedSourceMetadata, QuotedSourceRoot,
};
use crate::ast::{Var, VarContext};
use crate::source::{SourceMap, Span};

pub(crate) fn rewrite_source_sugar(
    owner: &QuotedSourceRoot,
    source: AnyValueRef,
    node: &QuotedAstNode,
    sources: &SourceMap,
) -> Result<Option<AnyValueRef>, QuotedSourceError> {
    if let Some(rewritten) = owner.source_sugar_rewrite(source) {
        return Ok(Some(rewritten));
    }
    if !is_list_like(&node.tail) {
        return Ok(None);
    }
    if node.head.root().tag() != ValueKind::ATOM {
        return Ok(None);
    }
    let head = node.head.atom_name()?;
    let args = node.tail.list_items()?;
    let rewritten = match head.as_str() {
        "|>" if args.len() == 2 => rewrite_pipe(owner, node, &args, sources),
        "&" if args.len() == 1 => rewrite_capture(owner, node, &args[0], sources),
        "-" if args.len() == 1 => rewrite_unary_minus(owner, node, &args[0]),
        "fn" => rewrite_lambda(owner, node, &args, sources),
        "for" => rewrite_comprehension(owner, node, &args, sources),
        "++" | "--" | "<>" | ".." | "//" | "in" | "not in" if args.len() == 2 => {
            rewrite_operator(owner, node, head.as_str(), &args, sources)
        }
        _ => Ok(None),
    }?;
    if let Some(rewritten) = rewritten {
        owner.memoize_source_sugar_rewrite(source, rewritten);
    }
    Ok(rewritten)
}

fn rewrite_pipe(
    owner: &QuotedSourceRoot,
    node: &QuotedAstNode,
    args: &[QuotedSourceCursor],
    sources: &SourceMap,
) -> Result<Option<AnyValueRef>, QuotedSourceError> {
    let lhs = args[0].root();
    let rhs = &args[1];
    let Some(rhs_node) = rhs.ast_node(sources)? else {
        return Ok(None);
    };
    if !is_list_like(&rhs_node.tail) {
        return Ok(None);
    }

    let rhs_args = roots(&rhs_node.tail.list_items()?);
    let is_case = rhs_node.head.root().tag() == ValueKind::ATOM && rhs_node.head.atom_name()? == "case";
    if is_case {
        if rhs_args.len() != 1 {
            return Ok(None);
        }
        return Ok(Some(ast_call(
            &owner.builder(),
            rhs_node.head.root(),
            node.meta.root(),
            &[lhs, rhs_args[0]],
        )?));
    }

    let mut piped_args = Vec::with_capacity(rhs_args.len() + 1);
    piped_args.push(lhs);
    piped_args.extend(rhs_args);
    Ok(Some(ast_call(
        &owner.builder(),
        rhs_node.head.root(),
        node.meta.root(),
        &piped_args,
    )?))
}

/// `-x` becomes `Kernel.negate(x)`, a typed clause family like every BINARY
/// operator.
///
/// Lowered instead to one machine instruction, unary minus read a single lane,
/// so `-x` aborted natively for an operand that might be an integer or a float
/// while `0 - x` on the same value worked (fz-5xp.38). Routing it through
/// `Kernel` makes the two agree by construction, and makes an unsupported
/// operand a missing clause rather than a wrong instruction.
///
/// A numeric LITERAL is left alone for the decoder to fold into a negative
/// literal: `-3` should not become a call.
fn rewrite_unary_minus(
    owner: &QuotedSourceRoot,
    node: &QuotedAstNode,
    operand: &QuotedSourceCursor,
) -> Result<Option<AnyValueRef>, QuotedSourceError> {
    if matches!(operand.root().tag(), ValueKind::INT | ValueKind::FLOAT) {
        return Ok(None);
    }
    let builder = owner.builder();
    Ok(Some(remote_call(
        &builder,
        "Kernel.negate",
        node.meta.root(),
        &[operand.root()],
    )?))
}

fn rewrite_operator(
    owner: &QuotedSourceRoot,
    node: &QuotedAstNode,
    op: &str,
    args: &[QuotedSourceCursor],
    sources: &SourceMap,
) -> Result<Option<AnyValueRef>, QuotedSourceError> {
    let builder = owner.builder();
    let left = args[0].root();
    let right = args[1].root();
    let meta = node.meta.root();
    let rewritten = match op {
        "++" => remote_call(
            &builder,
            "List.concat",
            operator_meta(&builder, node, op)?,
            &[left, right],
        )?,
        "--" => remote_call(&builder, "List.subtract", meta, &[left, right])?,
        "<>" => remote_call(
            &builder,
            "Kernel.<>",
            operator_meta(&builder, node, op)?,
            &[left, right],
        )?,
        ".." => remote_call(&builder, "Range.new", meta, &[left, right, builder.int(1)])?,
        "//" => {
            let Some((first, last)) = range_parts(&args[0], sources)? else {
                return Ok(None);
            };
            remote_call(&builder, "Range.new", meta, &[first, last, right])?
        }
        "in" => remote_call(
            &builder,
            "Enum.member?",
            operator_meta(&builder, node, op)?,
            &[right, left],
        )?,
        "not in" => {
            let member = remote_call(&builder, "Enum.member?", meta, &[right, left])?;
            named_call(&builder, "not", meta, &[member])?
        }
        _ => return Ok(None),
    };
    Ok(Some(rewritten))
}

/// The operator call's metadata with the operator stamped on it, so a pattern
/// can tell this call from one the user spelled out.
fn operator_meta(
    builder: &QuotedSourceBuilder,
    node: &QuotedAstNode,
    op: &str,
) -> Result<AnyValueRef, QuotedSourceError> {
    let mut entries = node
        .meta
        .map_entries()?
        .into_iter()
        .map(|(key, value)| (key.root(), value.root()))
        .collect::<Vec<_>>();
    entries.push((builder.atom(META_FROM_OPERATOR_KEY), builder.atom(op)));
    builder.map(&entries)
}

fn range_parts(
    cursor: &QuotedSourceCursor,
    sources: &SourceMap,
) -> Result<Option<(AnyValueRef, AnyValueRef)>, QuotedSourceError> {
    let Some(node) = cursor.ast_node(sources)? else {
        return Ok(None);
    };
    if node.head.root().tag() != ValueKind::ATOM {
        return Ok(None);
    }
    let head = node.head.atom_name()?;
    if head != ".." && head != "Range.new" {
        return Ok(None);
    }
    let args = node.tail.list_items()?;
    if args.len() < 2 {
        return Ok(None);
    }
    Ok(Some((args[0].root(), args[1].root())))
}

fn rewrite_capture(
    owner: &QuotedSourceRoot,
    node: &QuotedAstNode,
    body: &QuotedSourceCursor,
    sources: &SourceMap,
) -> Result<Option<AnyValueRef>, QuotedSourceError> {
    if is_function_ref_payload(body, sources)? {
        return Ok(None);
    }

    let builder = owner.builder();
    let meta = node.meta.root();
    if body.root().tag() == ValueKind::INT {
        let arity = body.int_value()?;
        if arity < 1 {
            return Ok(None);
        }
        let body = generated_variable(&builder, "__fz_capture_arg", arity as usize, node.span)?;
        return Ok(Some(capture_lambda(&builder, arity as usize, body, meta, node.span)?));
    }

    let arity = max_capture_arg(body, sources)?.unwrap_or(0);
    let body = replace_capture_args(&builder, body, node.span, sources)?.0;
    Ok(Some(capture_lambda(&builder, arity, body, meta, node.span)?))
}

fn rewrite_lambda(
    owner: &QuotedSourceRoot,
    node: &QuotedAstNode,
    clauses: &[QuotedSourceCursor],
    sources: &SourceMap,
) -> Result<Option<AnyValueRef>, QuotedSourceError> {
    if !lambda_source_sugar_shape(clauses, sources)? {
        return Ok(None);
    }
    if lambda_is_direct_clause(clauses, sources)? {
        return Ok(None);
    }

    let mut decoded = Vec::with_capacity(clauses.len());
    for clause in clauses {
        decoded.push(lambda_clause(clause, sources)?);
    }
    let Some(arity) = decoded.first().map(|clause| clause.params.len()) else {
        return Ok(None);
    };
    if decoded.iter().any(|clause| clause.params.len() != arity) {
        return Ok(None);
    }

    let builder = owner.builder();
    let meta = node.meta.root();
    let lambda_params = (0..arity)
        .map(|index| generated_variable(&builder, "__fz_lambda_arg", index, node.span))
        .collect::<Result<Vec<_>, _>>()?;
    let subject = if arity == 1 {
        lambda_params[0]
    } else {
        builder.tuple(&lambda_params)?
    };

    let mut arms = Vec::with_capacity(decoded.len());
    for clause in decoded {
        let pattern = if arity == 1 {
            clause.params[0]
        } else {
            builder.tuple(&clause.params)?
        };
        let pattern = if let Some(guard) = clause.guard {
            named_call(&builder, "when", clause.meta, &[pattern, guard])?
        } else {
            pattern
        };
        let patterns = builder.list(&[pattern])?;
        arms.push(named_call(&builder, "->", clause.meta, &[patterns, clause.body])?);
    }

    let case_body = builder.list(&arms)?;
    let case_kw = builder.list(&[builder.keyword("do", case_body)?])?;
    let case = named_call(&builder, "case", meta, &[subject, case_kw])?;
    let params = builder.list(&lambda_params)?;
    let clause = named_call(&builder, "->", meta, &[params, case])?;
    Ok(Some(named_call(&builder, "fn", meta, &[clause])?))
}

/// `for` becomes nested `Enum.reduce` calls, one per generator, threading an
/// accumulator inward:
///
/// - `p <- e` wraps the step in `Enum.reduce(e, acc, fn p, acc' -> STEP end)`.
///   A refutable `p` is matched inside a `case` whose `_` arm returns `acc'`,
///   so a non-matching element is skipped. An irrefutable `p` (a variable)
///   gets no skip arm: it would be a redundant clause.
/// - a filter `f` wraps the step in `if f, do: STEP, else: acc`.
/// - the innermost step is `[body | acc]`, `fun.(acc, {:cont, body})` for
///   `into:`, or `case acc do <clauses> end` for `reduce:`.
///
/// The outermost reduce starts from `[]` and is reversed; from the collector's
/// `init` and is finished with `fun.(result, :done)`; or from the `reduce:`
/// value and is returned as is.
fn rewrite_comprehension(
    owner: &QuotedSourceRoot,
    node: &QuotedAstNode,
    args: &[QuotedSourceCursor],
    sources: &SourceMap,
) -> Result<Option<AnyValueRef>, QuotedSourceError> {
    let span = node.span;
    let qualifier_count = args.len() - args.iter().rev().take_while(|arg| is_keyword_list(arg)).count();
    let (qualifiers, option_lists) = args.split_at(qualifier_count);
    if option_lists.is_empty() {
        return Err(comprehension_error(span, "comprehension needs a `do` body"));
    }
    let options = ComprehensionOptions::read(option_lists, span, sources)?;
    let qualifiers = qualifiers
        .iter()
        .map(|qualifier| Qualifier::read(qualifier, span, sources))
        .collect::<Result<Vec<_>, _>>()?;
    if !matches!(qualifiers.first(), Some(Qualifier::Generator { .. })) {
        return Err(comprehension_error(span, "comprehension must start with a generator"));
    }
    let builder = owner.builder();
    let build = ComprehensionBuild {
        builder: &builder,
        meta: node.meta.root(),
        span: node.span,
        options: &options,
        qualifiers: &qualifiers,
    };
    Ok(Some(build.finish()?))
}

/// A comprehension the rewrite refuses is a user error at the `for`, not an
/// internal leftover.
fn comprehension_error(span: Option<Span>, message: impl Into<String>) -> QuotedSourceError {
    QuotedSourceError::user(crate::diag::codes::PARSE_COMPREHENSION, span, message)
}

struct ComprehensionOptions {
    body: AnyValueRef,
    collector: Option<AnyValueRef>,
    reduce: Option<AnyValueRef>,
}

impl ComprehensionOptions {
    /// The trailing keyword lists, which the parser delivers separately when
    /// a `do` block follows (`reduce: 0 do ... end`), read as one.
    fn read(
        option_lists: &[QuotedSourceCursor],
        span: Option<Span>,
        sources: &SourceMap,
    ) -> Result<Self, QuotedSourceError> {
        let mut body = None;
        let mut collector = None;
        let mut reduce = None;
        for entry in option_lists
            .iter()
            .map(QuotedSourceCursor::list_items)
            .collect::<Result<Vec<_>, _>>()?
            .concat()
        {
            let items = entry.tuple_items()?;
            let [key, value] = items.as_slice() else {
                return Err(comprehension_error(
                    span,
                    "comprehension option expects a key and a value",
                ));
            };
            match key.atom_name()?.as_str() {
                "do" => body = Some(value.clone()),
                "into" => collector = Some(value.root()),
                "reduce" => reduce = Some(value.root()),
                other => {
                    return Err(comprehension_error(
                        span,
                        format!("comprehension `{other}:` is not built"),
                    ));
                }
            }
        }
        let Some(body) = body else {
            return Err(comprehension_error(span, "comprehension needs a `do` body"));
        };
        if collector.is_some() && reduce.is_some() {
            return Err(comprehension_error(
                span,
                "comprehension takes `into:` or `reduce:`, not both",
            ));
        }
        if reduce.is_some() && !lambda_source_sugar_shape(&body.list_items().unwrap_or_default(), sources)? {
            return Err(comprehension_error(
                span,
                "comprehension `reduce:` takes a `do` block of `->` clauses",
            ));
        }
        Ok(Self {
            body: body.root(),
            collector,
            reduce,
        })
    }
}

fn is_keyword_list(cursor: &QuotedSourceCursor) -> bool {
    cursor.root().tag() == ValueKind::LIST
        && cursor.list_items().is_ok_and(|entries| {
            entries.iter().all(|entry| {
                entry
                    .tuple_items()
                    .is_ok_and(|items| items.len() == 2 && items[0].root().tag() == ValueKind::ATOM)
            })
        })
}

enum Qualifier {
    Generator {
        pattern: AnyValueRef,
        source: AnyValueRef,
        refutable: bool,
    },
    Filter(AnyValueRef),
}

impl Qualifier {
    fn read(cursor: &QuotedSourceCursor, span: Option<Span>, sources: &SourceMap) -> Result<Self, QuotedSourceError> {
        let Some(node) = cursor.ast_node(sources)? else {
            return Ok(Self::Filter(cursor.root()));
        };
        if node.head.root().tag() != ValueKind::ATOM || !is_list_like(&node.tail) {
            return Ok(Self::Filter(cursor.root()));
        }
        let head = node.head.atom_name()?;
        if head == "<<>>" && Self::holds_generator(&node, sources)? {
            return Err(comprehension_error(
                span,
                "comprehension bitstring generators are not built",
            ));
        }
        if head != "<-" {
            return Ok(Self::Filter(cursor.root()));
        }
        let parts = node.tail.list_items()?;
        let [pattern, source] = parts.as_slice() else {
            return Err(comprehension_error(
                span,
                "comprehension generator takes a pattern and an enumerable",
            ));
        };
        let refutable = match pattern.ast_node(sources)? {
            None => true,
            Some(pattern_node) => is_list_like(&pattern_node.tail),
        };
        Ok(Self::Generator {
            pattern: pattern.root(),
            source: source.root(),
            refutable,
        })
    }
}

impl Qualifier {
    /// Whether a `<<...>>` qualifier is the `<<x <- bin>>` generator form.
    fn holds_generator(bitstring: &QuotedAstNode, sources: &SourceMap) -> Result<bool, QuotedSourceError> {
        for part in bitstring.tail.list_items()? {
            if let Some(node) = part.ast_node(sources)?
                && node.head.root().tag() == ValueKind::ATOM
                && node.head.atom_name()? == "<-"
            {
                return Ok(true);
            }
        }
        Ok(false)
    }
}

struct ComprehensionBuild<'a> {
    builder: &'a QuotedSourceBuilder,
    meta: AnyValueRef,
    span: Option<Span>,
    options: &'a ComprehensionOptions,
    qualifiers: &'a [Qualifier],
}

impl ComprehensionBuild<'_> {
    fn finish(&self) -> Result<AnyValueRef, QuotedSourceError> {
        let builder = self.builder;
        if let Some(initial) = self.options.reduce {
            return self.nest(0, 0, initial);
        }
        if let Some(collector) = self.options.collector {
            let init = self.generated("__fz_for_init", 0)?;
            let fun = self.generated("__fz_for_fun", 0)?;
            let collectable = remote_call(builder, "Collectable.into", self.meta, &[collector])?;
            let bind = named_call(builder, "=", self.meta, &[builder.tuple(&[init, fun])?, collectable])?;
            let reduced = self.nest(0, 0, init)?;
            let done = self.closure_call(fun, &[reduced, builder.atom("done")])?;
            return named_call(builder, "__block__", self.meta, &[bind, done]);
        }
        let reduced = self.nest(0, 0, builder.empty_list())?;
        remote_call(builder, "Enum.reverse", self.meta, &[reduced])
    }

    /// The qualifiers from `index` inward, given the expression holding the
    /// accumulator at that point and the number of generators outside it.
    fn nest(&self, index: usize, depth: usize, acc: AnyValueRef) -> Result<AnyValueRef, QuotedSourceError> {
        let builder = self.builder;
        let Some(qualifier) = self.qualifiers.get(index) else {
            return self.step(acc);
        };
        match qualifier {
            Qualifier::Filter(condition) => {
                let step = self.nest(index + 1, depth, acc)?;
                let branches = builder.list(&[builder.keyword("do", step)?, builder.keyword("else", acc)?])?;
                named_call(builder, "if", self.meta, &[*condition, branches])
            }
            Qualifier::Generator {
                pattern,
                source,
                refutable,
            } => {
                let inner_acc = self.generated("__fz_for_acc", depth)?;
                let step = self.nest(index + 1, depth + 1, inner_acc)?;
                let (param, body) = if *refutable {
                    let elem = self.generated("__fz_for_elem", depth)?;
                    (elem, self.skipping_case(elem, *pattern, step, inner_acc)?)
                } else {
                    (*pattern, step)
                };
                let params = builder.list(&[param, inner_acc])?;
                let clause = named_call(builder, "->", self.meta, &[params, body])?;
                let reducer = named_call(builder, "fn", self.meta, &[clause])?;
                remote_call(builder, "Enum.reduce", self.meta, &[*source, acc, reducer])
            }
        }
    }

    fn step(&self, acc: AnyValueRef) -> Result<AnyValueRef, QuotedSourceError> {
        let builder = self.builder;
        let options = self.options;
        if options.reduce.is_some() {
            let kw = builder.list(&[builder.keyword("do", options.body)?])?;
            return named_call(builder, "case", self.meta, &[acc, kw]);
        }
        if options.collector.is_some() {
            let fun = self.generated("__fz_for_fun", 0)?;
            let cont = builder.tuple(&[builder.atom("cont"), options.body])?;
            return self.closure_call(fun, &[acc, cont]);
        }
        builder.list(&[named_call(builder, "|", self.meta, &[options.body, acc])?])
    }

    fn skipping_case(
        &self,
        elem: AnyValueRef,
        pattern: AnyValueRef,
        step: AnyValueRef,
        acc: AnyValueRef,
    ) -> Result<AnyValueRef, QuotedSourceError> {
        let builder = self.builder;
        let matched = named_call(builder, "->", self.meta, &[builder.list(&[pattern])?, step])?;
        let wildcard = builder.variable(
            &Var {
                name: "_".to_string(),
                context: VarContext::User,
            },
            &QuotedSourceMetadata::default(),
        )?;
        let skip = named_call(builder, "->", self.meta, &[builder.list(&[wildcard])?, acc])?;
        let kw = builder.list(&[builder.keyword("do", builder.list(&[matched, skip])?)?])?;
        named_call(builder, "case", self.meta, &[elem, kw])
    }

    /// `fun.(args)`: a call whose head is the dot applied to the callee alone.
    fn closure_call(&self, fun: AnyValueRef, args: &[AnyValueRef]) -> Result<AnyValueRef, QuotedSourceError> {
        let callee = named_call(self.builder, ".", self.meta, &[fun])?;
        ast_call(self.builder, callee, self.meta, args)
    }

    fn generated(&self, name: &str, ordinal: usize) -> Result<AnyValueRef, QuotedSourceError> {
        generated_variable(self.builder, name, ordinal, self.span)
    }
}

fn lambda_source_sugar_shape(clauses: &[QuotedSourceCursor], sources: &SourceMap) -> Result<bool, QuotedSourceError> {
    for clause in clauses {
        let Some(node) = clause.ast_node(sources)? else {
            return Ok(false);
        };
        if node.head.root().tag() != ValueKind::ATOM || node.head.atom_name()? != "->" {
            return Ok(false);
        }
    }
    Ok(!clauses.is_empty())
}

struct LambdaClauseSource {
    params: Vec<AnyValueRef>,
    guard: Option<AnyValueRef>,
    body: AnyValueRef,
    meta: AnyValueRef,
}

fn lambda_is_direct_clause(clauses: &[QuotedSourceCursor], sources: &SourceMap) -> Result<bool, QuotedSourceError> {
    let [clause] = clauses else {
        return Ok(false);
    };
    Ok(lambda_clause(clause, sources)?.guard.is_none())
}

fn lambda_clause(cursor: &QuotedSourceCursor, sources: &SourceMap) -> Result<LambdaClauseSource, QuotedSourceError> {
    let Some(node) = cursor.ast_node(sources)? else {
        return Err(QuotedSourceError::new("lambda clause expected quoted AST"));
    };
    if node.head.atom_name()? != "->" {
        return Err(QuotedSourceError::new("lambda clause expected `->`"));
    }
    let parts = node.tail.list_items()?;
    let [params, body] = parts.as_slice() else {
        return Err(QuotedSourceError::new("lambda clause expected params and body"));
    };
    let params = params.list_items()?;
    if params.len() == 1
        && let Some(when) = params[0].ast_node(sources)?
        && when.head.atom_name()? == "when"
    {
        let args = when.tail.list_items()?;
        let Some((guard, params)) = args.split_last() else {
            return Err(QuotedSourceError::new("guarded lambda clause is empty"));
        };
        return Ok(LambdaClauseSource {
            params: roots(params),
            guard: Some(guard.root()),
            body: body.root(),
            meta: node.meta.root(),
        });
    }
    Ok(LambdaClauseSource {
        params: roots(&params),
        guard: None,
        body: body.root(),
        meta: node.meta.root(),
    })
}

fn is_function_ref_payload(cursor: &QuotedSourceCursor, sources: &SourceMap) -> Result<bool, QuotedSourceError> {
    let Some(node) = cursor.ast_node(sources)? else {
        return Ok(false);
    };
    if node.head.root().tag() != ValueKind::ATOM {
        return Ok(false);
    }
    Ok(node.head.atom_name()? == "/" && is_list_like(&node.tail))
}

fn max_capture_arg(cursor: &QuotedSourceCursor, sources: &SourceMap) -> Result<Option<usize>, QuotedSourceError> {
    if let Some(index) = capture_arg_index(cursor, sources)? {
        return Ok(Some(index));
    }
    let mut max = None;
    for child in child_cursors(cursor)? {
        if let Some(index) = max_capture_arg(&child, sources)? {
            max = Some(max.map_or(index, |current: usize| current.max(index)));
        }
    }
    Ok(max)
}

fn replace_capture_args(
    builder: &QuotedSourceBuilder,
    cursor: &QuotedSourceCursor,
    span: Option<Span>,
    sources: &SourceMap,
) -> Result<(AnyValueRef, bool), QuotedSourceError> {
    if let Some(index) = capture_arg_index(cursor, sources)? {
        return Ok((generated_variable(builder, "__fz_capture_arg", index, span)?, true));
    }

    match cursor.root().tag() {
        ValueKind::LIST => {
            let items = cursor.list_items()?;
            let mut changed = false;
            let mut out = Vec::with_capacity(items.len());
            for item in items {
                let (root, item_changed) = replace_capture_args(builder, &item, span, sources)?;
                changed |= item_changed;
                out.push(root);
            }
            if changed {
                Ok((builder.list(&out)?, true))
            } else {
                Ok((cursor.root(), false))
            }
        }
        ValueKind::STRUCT => {
            let items = cursor.tuple_items()?;
            let mut changed = false;
            let mut out = Vec::with_capacity(items.len());
            for item in items {
                let (root, item_changed) = replace_capture_args(builder, &item, span, sources)?;
                changed |= item_changed;
                out.push(root);
            }
            if changed {
                Ok((builder.tuple(&out)?, true))
            } else {
                Ok((cursor.root(), false))
            }
        }
        ValueKind::MAP => {
            let entries = cursor.map_entries()?;
            let mut changed = false;
            let mut out = Vec::with_capacity(entries.len());
            for (key, value) in entries {
                let (key, key_changed) = replace_capture_args(builder, &key, span, sources)?;
                let (value, value_changed) = replace_capture_args(builder, &value, span, sources)?;
                changed |= key_changed || value_changed;
                out.push((key, value));
            }
            if changed {
                Ok((builder.map(&out)?, true))
            } else {
                Ok((cursor.root(), false))
            }
        }
        _ => Ok((cursor.root(), false)),
    }
}

fn capture_arg_index(cursor: &QuotedSourceCursor, sources: &SourceMap) -> Result<Option<usize>, QuotedSourceError> {
    let Some(node) = cursor.ast_node(sources)? else {
        return Ok(None);
    };
    if node.head.root().tag() != ValueKind::ATOM || node.head.atom_name()? != "&" || !is_list_like(&node.tail) {
        return Ok(None);
    }
    let args = node.tail.list_items()?;
    let [arg] = args.as_slice() else {
        return Ok(None);
    };
    if arg.root().tag() != ValueKind::INT {
        return Ok(None);
    }
    let index = arg.int_value()?;
    if index < 1 {
        return Ok(None);
    }
    Ok(Some(index as usize))
}

fn child_cursors(cursor: &QuotedSourceCursor) -> Result<Vec<QuotedSourceCursor>, QuotedSourceError> {
    match cursor.root().tag() {
        ValueKind::LIST => cursor.list_items(),
        ValueKind::STRUCT => cursor.tuple_items(),
        ValueKind::MAP => Ok(cursor
            .map_entries()?
            .into_iter()
            .flat_map(|(key, value)| [key, value])
            .collect()),
        _ => Ok(Vec::new()),
    }
}

fn capture_lambda(
    builder: &QuotedSourceBuilder,
    arity: usize,
    body: AnyValueRef,
    meta: AnyValueRef,
    span: Option<Span>,
) -> Result<AnyValueRef, QuotedSourceError> {
    let params = (1..=arity)
        .map(|index| generated_variable(builder, "__fz_capture_arg", index, span))
        .collect::<Result<Vec<_>, _>>()?;
    let params = builder.list(&params)?;
    let clause = named_call(builder, "->", meta, &[params, body])?;
    named_call(builder, "fn", meta, &[clause])
}

/// The one shape a sugar-synthesised parameter or reference takes: a `Var`
/// with `Generated(ordinal)` context, so it can never collide with a
/// same-spelled variable the user wrote, no matter how it reads on the page.
fn generated_variable(
    builder: &QuotedSourceBuilder,
    name: &str,
    ordinal: usize,
    span: Option<Span>,
) -> Result<AnyValueRef, QuotedSourceError> {
    let var = Var {
        name: name.to_string(),
        context: VarContext::Generated(ordinal as u32),
    };
    let meta = QuotedSourceMetadata {
        module: None,
        bound_callable: None,
        from_brackets: false,
        span,
        hygiene_ordinal: None,
    };
    builder.variable(&var, &meta)
}

fn named_call(
    builder: &QuotedSourceBuilder,
    name: &str,
    meta: AnyValueRef,
    args: &[AnyValueRef],
) -> Result<AnyValueRef, QuotedSourceError> {
    ast_call(builder, builder.atom(name), meta, args)
}

fn remote_call(
    builder: &QuotedSourceBuilder,
    name: &str,
    meta: AnyValueRef,
    args: &[AnyValueRef],
) -> Result<AnyValueRef, QuotedSourceError> {
    let Some((module, function)) = name.rsplit_once('.') else {
        return named_call(builder, name, meta, args);
    };
    let segments = module
        .split('.')
        .map(|segment| builder.atom(segment))
        .collect::<Vec<_>>();
    let alias = ast_call(builder, builder.atom("__aliases__"), meta, &segments)?;
    let callee = ast_call(builder, builder.atom("."), meta, &[alias, builder.atom(function)])?;
    ast_call(builder, callee, meta, args)
}

fn ast_call(
    builder: &QuotedSourceBuilder,
    head: AnyValueRef,
    meta: AnyValueRef,
    args: &[AnyValueRef],
) -> Result<AnyValueRef, QuotedSourceError> {
    builder.tuple(&[head, meta, builder.list(args)?])
}

fn roots(cursors: &[QuotedSourceCursor]) -> Vec<AnyValueRef> {
    cursors.iter().map(QuotedSourceCursor::root).collect()
}

fn is_list_like(cursor: &QuotedSourceCursor) -> bool {
    cursor.root().is_empty_list() || cursor.root().tag() == ValueKind::LIST
}

#[cfg(test)]
#[path = "source_sugar_test.rs"]
mod source_sugar_test;
