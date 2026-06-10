//! Source-only rewrites over compiler2 quoted AST.
//!
//! These rules remove syntax sugar before `FunctionSource` is published, so
//! body lowering sees ordinary calls, lambdas, and case forms.

use fz_runtime::any_value::{AnyValueRef, ValueKind};

use super::source::{QuotedAstNode, QuotedSourceBuilder, QuotedSourceCursor, QuotedSourceError, QuotedSourceRoot};

pub(crate) fn rewrite_source_sugar(
    owner: &QuotedSourceRoot,
    node: &QuotedAstNode,
) -> Result<Option<AnyValueRef>, QuotedSourceError> {
    if !is_list_like(&node.tail) {
        return Ok(None);
    }
    let Ok(head) = node.head.atom_name() else {
        return Ok(None);
    };
    let args = node.tail.list_items()?;
    match head.as_str() {
        "|>" if args.len() == 2 => rewrite_pipe(owner, node, &args),
        "&" if args.len() == 1 => rewrite_capture(owner, node, &args[0]),
        "fn" => rewrite_lambda(owner, node, &args),
        "++" | "--" | "<>" | ".." | "//" | "in" | "not in" if args.len() == 2 => {
            rewrite_operator(owner, node, head.as_str(), &args)
        }
        _ => Ok(None),
    }
}

fn rewrite_pipe(
    owner: &QuotedSourceRoot,
    node: &QuotedAstNode,
    args: &[QuotedSourceCursor],
) -> Result<Option<AnyValueRef>, QuotedSourceError> {
    let lhs = args[0].root();
    let rhs = &args[1];
    let Some(rhs_node) = rhs.ast_node()? else {
        return Ok(None);
    };
    if !is_list_like(&rhs_node.tail) {
        return Ok(None);
    }

    let rhs_args = roots(&rhs_node.tail.list_items()?);
    if rhs_node.head.atom_name().as_deref() == Ok("case") {
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

fn rewrite_operator(
    owner: &QuotedSourceRoot,
    node: &QuotedAstNode,
    op: &str,
    args: &[QuotedSourceCursor],
) -> Result<Option<AnyValueRef>, QuotedSourceError> {
    let builder = owner.builder();
    let left = args[0].root();
    let right = args[1].root();
    let meta = node.meta.root();
    let rewritten = match op {
        "++" => remote_call(&builder, "List.concat", meta, &[left, right])?,
        "--" => remote_call(&builder, "List.subtract", meta, &[left, right])?,
        "<>" => remote_call(&builder, "Kernel.fz_binary_concat", meta, &[left, right])?,
        ".." => remote_call(&builder, "Range.new", meta, &[left, right, builder.int(1)])?,
        "//" => {
            let Some((first, last)) = range_parts(&args[0])? else {
                return Ok(None);
            };
            remote_call(&builder, "Range.new", meta, &[first, last, right])?
        }
        "in" => remote_call(&builder, "Enum.member?", meta, &[right, left])?,
        "not in" => {
            let member = remote_call(&builder, "Enum.member?", meta, &[right, left])?;
            named_call(&builder, "not", meta, &[member])?
        }
        _ => return Ok(None),
    };
    Ok(Some(rewritten))
}

fn range_parts(cursor: &QuotedSourceCursor) -> Result<Option<(AnyValueRef, AnyValueRef)>, QuotedSourceError> {
    let Some(node) = cursor.ast_node()? else {
        return Ok(None);
    };
    if node.head.atom_name().as_deref() != Ok("..") && node.head.atom_name().as_deref() != Ok("Range.new") {
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
) -> Result<Option<AnyValueRef>, QuotedSourceError> {
    if is_function_ref_payload(body)? {
        return Ok(None);
    }

    let builder = owner.builder();
    let meta = node.meta.root();
    if body.root().tag() == ValueKind::INT {
        let arity = body.int_value()?;
        if arity < 1 {
            return Ok(None);
        }
        let body = variable(&builder, capture_arg_name(arity as usize), meta)?;
        return Ok(Some(capture_lambda(&builder, arity as usize, body, meta)?));
    }

    let arity = max_capture_arg(body)?.unwrap_or(0);
    let body = replace_capture_args(&builder, body, meta)?.0;
    Ok(Some(capture_lambda(&builder, arity, body, meta)?))
}

fn rewrite_lambda(
    owner: &QuotedSourceRoot,
    node: &QuotedAstNode,
    clauses: &[QuotedSourceCursor],
) -> Result<Option<AnyValueRef>, QuotedSourceError> {
    if !lambda_source_sugar_shape(clauses)? {
        return Ok(None);
    }
    if lambda_is_direct_clause(clauses)? {
        return Ok(None);
    }

    let mut decoded = Vec::with_capacity(clauses.len());
    for clause in clauses {
        decoded.push(lambda_clause(clause)?);
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
        .map(|index| variable(&builder, lambda_arg_name(index), meta))
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

fn lambda_source_sugar_shape(clauses: &[QuotedSourceCursor]) -> Result<bool, QuotedSourceError> {
    for clause in clauses {
        let Some(node) = clause.ast_node()? else {
            return Ok(false);
        };
        if node.head.atom_name().as_deref() != Ok("->") {
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

fn lambda_is_direct_clause(clauses: &[QuotedSourceCursor]) -> Result<bool, QuotedSourceError> {
    let [clause] = clauses else {
        return Ok(false);
    };
    Ok(lambda_clause(clause)?.guard.is_none())
}

fn lambda_clause(cursor: &QuotedSourceCursor) -> Result<LambdaClauseSource, QuotedSourceError> {
    let Some(node) = cursor.ast_node()? else {
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
        && let Some(when) = params[0].ast_node()?
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

fn is_function_ref_payload(cursor: &QuotedSourceCursor) -> Result<bool, QuotedSourceError> {
    let Some(node) = cursor.ast_node()? else {
        return Ok(false);
    };
    Ok(node.head.atom_name().as_deref() == Ok("/") && is_list_like(&node.tail))
}

fn max_capture_arg(cursor: &QuotedSourceCursor) -> Result<Option<usize>, QuotedSourceError> {
    if let Some(index) = capture_arg_index(cursor)? {
        return Ok(Some(index));
    }
    let mut max = None;
    for child in child_cursors(cursor)? {
        if let Some(index) = max_capture_arg(&child)? {
            max = Some(max.map_or(index, |current: usize| current.max(index)));
        }
    }
    Ok(max)
}

fn replace_capture_args(
    builder: &QuotedSourceBuilder,
    cursor: &QuotedSourceCursor,
    meta: AnyValueRef,
) -> Result<(AnyValueRef, bool), QuotedSourceError> {
    if let Some(index) = capture_arg_index(cursor)? {
        return Ok((variable(builder, capture_arg_name(index), meta)?, true));
    }

    match cursor.root().tag() {
        ValueKind::LIST => {
            let items = cursor.list_items()?;
            let mut changed = false;
            let mut out = Vec::with_capacity(items.len());
            for item in items {
                let (root, item_changed) = replace_capture_args(builder, &item, meta)?;
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
                let (root, item_changed) = replace_capture_args(builder, &item, meta)?;
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
                let (key, key_changed) = replace_capture_args(builder, &key, meta)?;
                let (value, value_changed) = replace_capture_args(builder, &value, meta)?;
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

fn capture_arg_index(cursor: &QuotedSourceCursor) -> Result<Option<usize>, QuotedSourceError> {
    let Some(node) = cursor.ast_node()? else {
        return Ok(None);
    };
    if node.head.atom_name().as_deref() != Ok("&") || !is_list_like(&node.tail) {
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
) -> Result<AnyValueRef, QuotedSourceError> {
    let params = (1..=arity)
        .map(|index| variable(builder, capture_arg_name(index), meta))
        .collect::<Result<Vec<_>, _>>()?;
    let params = builder.list(&params)?;
    let clause = named_call(builder, "->", meta, &[params, body])?;
    named_call(builder, "fn", meta, &[clause])
}

fn variable(builder: &QuotedSourceBuilder, name: String, meta: AnyValueRef) -> Result<AnyValueRef, QuotedSourceError> {
    builder.tuple(&[builder.atom(&name), meta, builder.nil()])
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

fn capture_arg_name(index: usize) -> String {
    format!("__fz_capture_arg_{index}")
}

fn lambda_arg_name(index: usize) -> String {
    format!("__fz_lambda_arg_{index}")
}
