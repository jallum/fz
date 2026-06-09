use crate::ast::{
    AfterClause, Attribute, BinOp, BitField, BitFieldSpec, BitSize, BitType, Endian, Expr, FnClause, LambdaClause,
    MatchClause, Pattern, Spanned, SpecDecl, TypeExprBody, UnOp,
};
use crate::compiler::source::{Id as SourceId, Span};
use crate::function_surface::FunctionSurface;
use crate::modules::identity::ModuleName;
use crate::parser::lexer::{Lexer, Tok, Token};
use crate::telemetry::Telemetry;

use super::code::CodeId;
use super::source::{QuotedAstNode, QuotedSourceCursor, QuotedSourceError, QuotedSourceRoot};

const META_SPAN_KEY: &str = "__fz_span__";

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct QuotedFunctionError {
    message: String,
}

impl QuotedFunctionError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl std::fmt::Display for QuotedFunctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

impl From<QuotedSourceError> for QuotedFunctionError {
    fn from(value: QuotedSourceError) -> Self {
        Self::new(value.to_string())
    }
}

struct DecodeCtx<'a> {
    code_id: CodeId,
    code_name: &'a str,
    code_text: &'a str,
    tel: &'a dyn Telemetry,
}

type DecodedFnHead = (
    String,
    Vec<Spanned<Pattern>>,
    Vec<Option<TypeExprBody>>,
    Span,
    Option<Spanned<Expr>>,
);

type ExprPair = (Spanned<Expr>, Spanned<Expr>);

pub(crate) fn derive_function_surface(
    root: &QuotedSourceRoot,
    code_id: CodeId,
    code_name: Option<&str>,
    code_text: &str,
    tel: &dyn Telemetry,
) -> Result<FunctionSurface, QuotedFunctionError> {
    let code_name = code_name.unwrap_or("<quoted-function>");
    let ctx = DecodeCtx {
        code_id,
        code_name,
        code_text,
        tel,
    };
    let mut attrs = Vec::new();
    let mut forms = Vec::new();
    for item in root.cursor().list_items()? {
        let node = expect_ast_node(&item, "grouped function item")?;
        let head = atom_name(&node.head)?;
        if head.starts_with('@') {
            attrs.push(decode_attribute(&item, &ctx)?);
        } else {
            forms.push(item);
        }
    }

    if forms.is_empty() {
        return Err(QuotedFunctionError::new("grouped quoted function source is empty"));
    }

    let first = expect_ast_node(&forms[0], "function form")?;
    let form_head = atom_name(&first.head)?;
    if form_head == "extern" {
        if forms.len() != 1 {
            return Err(QuotedFunctionError::new(
                "grouped quoted extern source cannot contain multiple non-attribute forms",
            ));
        }
        return decode_extern_fn(&first, attrs, &ctx);
    }

    let is_macro = form_head == "defmacro";
    let mut clauses = Vec::new();
    let mut group_name: Option<String> = None;
    let mut name_span = Span::DUMMY;
    let mut group_span = Span::DUMMY;

    for form in forms {
        let node = expect_ast_node(&form, "function clause")?;
        let head_name = atom_name(&node.head)?;
        if head_name != form_head {
            return Err(QuotedFunctionError::new(format!(
                "grouped quoted function mixes `{form_head}` and `{head_name}`"
            )));
        }
        let (name, clause, clause_name_span) = decode_function_clause(&node, &ctx)?;
        match &group_name {
            None => {
                group_name = Some(name);
                name_span = clause_name_span;
            }
            Some(current) if current == &name => {}
            Some(current) => {
                return Err(QuotedFunctionError::new(format!(
                    "grouped quoted function mixes `{current}` and `{name}` clauses"
                )));
            }
        }
        group_span = group_span.merge(clause.span);
        clauses.push(clause);
    }

    for attr in &attrs {
        if let Attribute::Spec(spec) = attr {
            let expected_name = group_name.as_deref().unwrap_or_default();
            let expected_arity = clauses.first().map(|clause| clause.params.len()).unwrap_or_default();
            if spec.name != expected_name {
                return Err(QuotedFunctionError::new(format!(
                    "@spec name `{}` doesn't match function `{expected_name}`",
                    spec.name
                )));
            }
            if spec.param_body_tokens.len() != expected_arity {
                return Err(QuotedFunctionError::new(format!(
                    "@spec arity {} doesn't match function `{expected_name}/{expected_arity}`",
                    spec.param_body_tokens.len()
                )));
            }
        }
    }

    let name = group_name.expect("non-empty grouped function should establish a name");
    Ok(FunctionSurface {
        name,
        name_span,
        clauses,
        is_macro,
        extern_abi: None,
        extern_param_tokens: Vec::new(),
        extern_ret_tokens: TypeExprBody(Vec::new()),
        extern_constraints: Vec::new(),
        variadic: false,
        attrs,
        span: group_span,
    })
}

fn decode_attribute(cursor: &QuotedSourceCursor, ctx: &DecodeCtx<'_>) -> Result<Attribute, QuotedFunctionError> {
    let node = expect_ast_node(cursor, "function attribute")?;
    let head = atom_name(&node.head)?;
    let args = node.tail.list_items()?;
    let Some(value) = args.first() else {
        return Err(QuotedFunctionError::new(format!(
            "quoted function attribute `{head}` is missing its payload"
        )));
    };
    match head.as_str() {
        "@doc" => Ok(Attribute::Doc(value.utf8_binary_text()?)),
        "@spec" => decode_spec_attribute(&value.utf8_binary_text()?, ctx),
        other => Err(QuotedFunctionError::new(format!(
            "unsupported quoted function attribute `{other}`"
        ))),
    }
}

fn decode_extern_fn(
    node: &QuotedAstNode,
    attrs: Vec<Attribute>,
    ctx: &DecodeCtx<'_>,
) -> Result<FunctionSurface, QuotedFunctionError> {
    let args = node.tail.list_items()?;
    if args.len() != 2 {
        return Err(QuotedFunctionError::new("quoted extern expects ABI and detail map"));
    }
    let abi = args[0].utf8_binary_text()?;
    let details = &args[1];
    let name = required_map_utf8(details, "name")?;
    let params = required_map_list_utf8(details, "params")?;
    let ret = required_map_utf8(details, "return")?;
    let variadic = required_map_bool(details, "variadic")?;
    let constraints = optional_map_keyword_utf8(details, "when")?;
    let span = span_from_meta(&node.meta, ctx).unwrap_or(Span::DUMMY);

    let extern_param_tokens = params
        .into_iter()
        .map(|text| lex_fragment_tokens(ctx, &text).and_then(strip_extern_param_name))
        .map(|result| result.map(TypeExprBody))
        .collect::<Result<Vec<_>, _>>()?;
    let extern_ret_tokens = TypeExprBody(lex_fragment_tokens(ctx, &ret)?);
    let extern_constraints = constraints
        .into_iter()
        .map(|(name, body)| Ok((name, TypeExprBody(lex_fragment_tokens(ctx, &body)?))))
        .collect::<Result<Vec<_>, QuotedFunctionError>>()?;

    Ok(FunctionSurface {
        name,
        name_span: span,
        clauses: Vec::new(),
        is_macro: false,
        extern_abi: Some(abi),
        extern_param_tokens,
        extern_ret_tokens,
        extern_constraints,
        variadic,
        attrs,
        span,
    })
}

fn decode_function_clause(
    node: &QuotedAstNode,
    ctx: &DecodeCtx<'_>,
) -> Result<(String, FnClause, Span), QuotedFunctionError> {
    let span = span_from_meta(&node.meta, ctx).unwrap_or(Span::DUMMY);
    let args = node.tail.list_items()?;
    if args.len() != 2 {
        return Err(QuotedFunctionError::new(
            "quoted function clause expects head and do-body",
        ));
    }
    let (name, params, param_annotations, name_span, guard) = decode_function_head(&args[0], ctx, Some(span))?;
    let body = decode_do_body(&args[1], ctx, Some(span))?;
    Ok((
        name,
        FnClause {
            params,
            param_annotations,
            guard,
            body,
            span,
        },
        name_span,
    ))
}

fn decode_function_head(
    cursor: &QuotedSourceCursor,
    ctx: &DecodeCtx<'_>,
    fallback_span: Option<Span>,
) -> Result<DecodedFnHead, QuotedFunctionError> {
    let node = expect_ast_node(cursor, "function head")?;
    let span = span_from_meta(&node.meta, ctx).unwrap_or(fallback_span.unwrap_or(Span::DUMMY));
    if atom_name(&node.head)? == "when" {
        let parts = node.tail.list_items()?;
        if parts.len() != 2 {
            return Err(QuotedFunctionError::new(
                "quoted `when` function head expects head and guard",
            ));
        }
        let (name, params, annotations, name_span, _) = decode_function_head(&parts[0], ctx, Some(span))?;
        let guard = decode_expr(&parts[1], ctx, Some(span))?;
        return Ok((name, params, annotations, name_span, Some(guard)));
    }

    let name = atom_name(&node.head)?;
    let mut params = Vec::new();
    let mut annotations = Vec::new();
    for arg in node.tail.list_items()? {
        if let Some(ascribe) = arg.ast_node()?
            && atom_name(&ascribe.head)? == "::"
        {
            let parts = ascribe.tail.list_items()?;
            if parts.len() != 2 {
                return Err(QuotedFunctionError::new("quoted `::` parameter expects lhs and rhs"));
            }
            params.push(decode_pattern(&parts[0], ctx, Some(span))?);
            annotations.push(Some(rendered_type_expr_body(&parts[1], ctx)?));
            continue;
        }
        params.push(decode_pattern(&arg, ctx, Some(span))?);
        annotations.push(None);
    }
    Ok((name, params, annotations, span, None))
}

fn decode_do_body(
    cursor: &QuotedSourceCursor,
    ctx: &DecodeCtx<'_>,
    fallback_span: Option<Span>,
) -> Result<Spanned<Expr>, QuotedFunctionError> {
    let entries = decode_keyword_entries(cursor)?;
    let Some((_, body)) = entries.into_iter().find(|(key, _)| key == "do") else {
        return Err(QuotedFunctionError::new(
            "quoted function clause is missing its `do` body",
        ));
    };
    decode_expr(&body, ctx, fallback_span)
}

fn decode_expr(
    cursor: &QuotedSourceCursor,
    ctx: &DecodeCtx<'_>,
    fallback_span: Option<Span>,
) -> Result<Spanned<Expr>, QuotedFunctionError> {
    if let Some(node) = cursor.ast_node()? {
        let span = span_from_meta(&node.meta, ctx).unwrap_or(fallback_span.unwrap_or(Span::DUMMY));
        if !is_list_like(&node.tail) {
            return Ok(Spanned::new(Expr::Var(atom_name(&node.head)?), span));
        }

        let args = node.tail.list_items()?;
        if node.head.root().tag() != fz_runtime::any_value::ValueKind::ATOM {
            if let Some(head_node) = node.head.ast_node()?
                && atom_name(&head_node.head)? == "."
            {
                let callee_parts = head_node.tail.list_items()?;
                if callee_parts.len() == 1 {
                    let callee = decode_expr(&callee_parts[0], ctx, Some(span))?;
                    let call_args = decode_exprs(&args, ctx, Some(span))?;
                    return Ok(Spanned::new(Expr::ClosureCall(Box::new(callee), call_args), span));
                }
                if callee_parts.len() == 2 && is_access_get(&callee_parts[0], &callee_parts[1]) && args.len() == 2 {
                    let base = decode_expr(&args[0], ctx, Some(span))?;
                    let key = decode_expr(&args[1], ctx, Some(span))?;
                    return Ok(Spanned::new(Expr::Index(Box::new(base), Box::new(key)), span));
                }
            }
            let callee = decode_expr(&node.head, ctx, Some(span))?;
            let call_args = decode_exprs(&args, ctx, Some(span))?;
            return Ok(Spanned::new(Expr::Call(Box::new(callee), call_args), span));
        }

        return decode_named_expr(atom_name(&node.head)?, &args, ctx, span);
    }

    let span = fallback_span.unwrap_or(Span::DUMMY);
    match cursor.root().tag() {
        fz_runtime::any_value::ValueKind::INT => Ok(Spanned::new(Expr::Int(cursor.int_value()?), span)),
        fz_runtime::any_value::ValueKind::FLOAT => Ok(Spanned::new(
            Expr::Float(cursor.root().load_float().map_err(QuotedSourceError::from)?),
            span,
        )),
        fz_runtime::any_value::ValueKind::ATOM => {
            let atom = cursor.atom_name()?;
            Ok(Spanned::new(
                match atom.as_str() {
                    "true" => Expr::Bool(true),
                    "false" => Expr::Bool(false),
                    "nil" => Expr::Nil,
                    _ => Expr::Atom(atom),
                },
                span,
            ))
        }
        fz_runtime::any_value::ValueKind::BITSTRING | fz_runtime::any_value::ValueKind::PROCBIN => {
            Ok(Spanned::new(Expr::Binary(cursor.raw_bytes()?), span))
        }
        fz_runtime::any_value::ValueKind::LIST => decode_list_expr(cursor, ctx, span),
        fz_runtime::any_value::ValueKind::STRUCT => {
            let items = cursor.tuple_items()?;
            let elems = decode_exprs(&items, ctx, Some(span))?;
            Ok(Spanned::new(Expr::Tuple(elems), span))
        }
        other => Err(QuotedFunctionError::new(format!(
            "unsupported quoted expression runtime kind {:?}",
            other
        ))),
    }
}

fn decode_named_expr(
    name: String,
    args: &[QuotedSourceCursor],
    ctx: &DecodeCtx<'_>,
    span: Span,
) -> Result<Spanned<Expr>, QuotedFunctionError> {
    if let Some(op) = binop_from_name(&name)
        && args.len() == 2
    {
        let left = decode_expr(&args[0], ctx, Some(span))?;
        let right = decode_expr(&args[1], ctx, Some(span))?;
        return Ok(Spanned::new(Expr::BinOp(op, Box::new(left), Box::new(right)), span));
    }
    match (name.as_str(), args.len()) {
        ("-", 1) => {
            let inner = decode_expr(&args[0], ctx, Some(span))?;
            Ok(Spanned::new(Expr::UnOp(UnOp::Neg, Box::new(inner)), span))
        }
        ("not", 1) => {
            let inner = decode_expr(&args[0], ctx, Some(span))?;
            Ok(Spanned::new(Expr::UnOp(UnOp::Not, Box::new(inner)), span))
        }
        ("=", 2) => {
            let lhs = decode_pattern(&args[0], ctx, Some(span))?;
            let rhs = decode_expr(&args[1], ctx, Some(span))?;
            Ok(Spanned::new(Expr::Match(lhs, Box::new(rhs)), span))
        }
        ("::", 2) => {
            let value = decode_expr(&args[0], ctx, Some(span))?;
            let ty = rendered_type_expr_body(&args[1], ctx)?;
            Ok(Spanned::new(Expr::Ascribe(Box::new(value), ty), span))
        }
        ("__aliases__", _) => Ok(Spanned::new(Expr::Var(alias_name_from_args(args)?), span)),
        (".", 2) => {
            let base = decode_expr(&args[0], ctx, Some(span))?;
            let field = Spanned::new(Expr::Atom(args[1].atom_name()?), span);
            Ok(Spanned::new(Expr::Index(Box::new(base), Box::new(field)), span))
        }
        ("__block__", _) => Ok(Spanned::new(Expr::Block(decode_exprs(args, ctx, Some(span))?), span)),
        ("if", 2) => decode_if(args, ctx, span),
        ("case", 1 | 2) => decode_case(args, ctx, span),
        ("cond", 1) => decode_cond(args, ctx, span),
        ("receive", 1) => decode_receive(args, ctx, span),
        ("fn", _) => decode_lambda(args, ctx, span),
        ("quote", 1) => decode_quote(args, ctx, span),
        ("unquote", 1) => {
            let inner = decode_expr(&args[0], ctx, Some(span))?;
            Ok(Spanned::new(Expr::Unquote(Box::new(inner)), span))
        }
        ("{}", _) => Ok(Spanned::new(Expr::Tuple(decode_exprs(args, ctx, Some(span))?), span)),
        ("%{}", _) => decode_map_expr(args, ctx, span),
        ("%", 2) if is_alias(&args[0]) => decode_struct_expr(args, ctx, span),
        ("<<>>", _) => decode_bitstring_expr(args, ctx, span),
        ("&", 1) => decode_fn_ref_expr(&args[0], ctx, span),
        _ => {
            let callee = Spanned::new(Expr::Var(name), span);
            let call_args = decode_exprs(args, ctx, Some(span))?;
            Ok(Spanned::new(Expr::Call(Box::new(callee), call_args), span))
        }
    }
}

fn decode_pattern(
    cursor: &QuotedSourceCursor,
    ctx: &DecodeCtx<'_>,
    fallback_span: Option<Span>,
) -> Result<Spanned<Pattern>, QuotedFunctionError> {
    if let Some(node) = cursor.ast_node()? {
        let span = span_from_meta(&node.meta, ctx).unwrap_or(fallback_span.unwrap_or(Span::DUMMY));
        if !is_list_like(&node.tail) {
            let name = atom_name(&node.head)?;
            return Ok(Spanned::new(
                if name == "_" {
                    Pattern::Wildcard
                } else {
                    Pattern::Var(name)
                },
                span,
            ));
        }
        let args = node.tail.list_items()?;
        return match atom_name(&node.head)?.as_str() {
            "=" => {
                let Some(name) = pattern_var_name(&args[0], ctx, Some(span))? else {
                    return Err(QuotedFunctionError::new("pattern as-bind lhs must be a variable"));
                };
                let inner = decode_pattern(&args[1], ctx, Some(span))?;
                Ok(Spanned::new(Pattern::As(name, Box::new(inner)), span))
            }
            "^" => {
                let Some(name) = pattern_var_name(&args[0], ctx, Some(span))? else {
                    return Err(QuotedFunctionError::new("pinned pattern expects a variable"));
                };
                Ok(Spanned::new(Pattern::Pinned(name), span))
            }
            "%{}" => decode_map_pattern(&args, ctx, span),
            "%" if is_alias(&args[0]) => decode_struct_pattern(&args, ctx, span),
            "{}" => Ok(Spanned::new(
                Pattern::Tuple(
                    args.iter()
                        .map(|arg| decode_pattern(arg, ctx, Some(span)))
                        .collect::<Result<Vec<_>, _>>()?,
                ),
                span,
            )),
            "<<>>" => decode_bitstring_pattern(&args, ctx, span),
            "-" if args.len() == 1 => decode_negative_pattern(&args[0], ctx, span),
            "__aliases__" => Err(QuotedFunctionError::new("module aliases are not valid patterns")),
            other => Err(QuotedFunctionError::new(format!(
                "unsupported quoted pattern head `{other}`"
            ))),
        };
    }

    let span = fallback_span.unwrap_or(Span::DUMMY);
    match cursor.root().tag() {
        fz_runtime::any_value::ValueKind::INT => Ok(Spanned::new(Pattern::Int(cursor.int_value()?), span)),
        fz_runtime::any_value::ValueKind::FLOAT => Ok(Spanned::new(
            Pattern::Float(cursor.root().load_float().map_err(QuotedSourceError::from)?),
            span,
        )),
        fz_runtime::any_value::ValueKind::ATOM => {
            let atom = cursor.atom_name()?;
            Ok(Spanned::new(
                match atom.as_str() {
                    "true" => Pattern::Bool(true),
                    "false" => Pattern::Bool(false),
                    "nil" => Pattern::Nil,
                    _ => Pattern::Atom(atom),
                },
                span,
            ))
        }
        fz_runtime::any_value::ValueKind::BITSTRING | fz_runtime::any_value::ValueKind::PROCBIN => {
            Ok(Spanned::new(Pattern::Binary(cursor.raw_bytes()?), span))
        }
        fz_runtime::any_value::ValueKind::LIST => decode_list_pattern(cursor, ctx, span),
        fz_runtime::any_value::ValueKind::STRUCT => {
            let items = cursor.tuple_items()?;
            let elems = items
                .into_iter()
                .map(|item| decode_pattern(&item, ctx, Some(span)))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Spanned::new(Pattern::Tuple(elems), span))
        }
        other => Err(QuotedFunctionError::new(format!(
            "unsupported quoted pattern runtime kind {:?}",
            other
        ))),
    }
}

fn decode_if(
    args: &[QuotedSourceCursor],
    ctx: &DecodeCtx<'_>,
    span: Span,
) -> Result<Spanned<Expr>, QuotedFunctionError> {
    let cond = decode_expr(&args[0], ctx, Some(span))?;
    let entries = decode_keyword_entries(&args[1])?;
    let mut then_branch = None;
    let mut else_branch = None;
    for (key, value) in entries {
        match key.as_str() {
            "do" => then_branch = Some(decode_expr(&value, ctx, Some(span))?),
            "else" => else_branch = Some(decode_expr(&value, ctx, Some(span))?),
            other => {
                return Err(QuotedFunctionError::new(format!(
                    "unsupported quoted `if` keyword `{other}`"
                )));
            }
        }
    }
    Ok(Spanned::new(
        Expr::If(
            Box::new(cond),
            Box::new(then_branch.ok_or_else(|| QuotedFunctionError::new("quoted `if` is missing `do`"))?),
            else_branch.map(Box::new),
        ),
        span,
    ))
}

fn decode_case(
    args: &[QuotedSourceCursor],
    ctx: &DecodeCtx<'_>,
    span: Span,
) -> Result<Spanned<Expr>, QuotedFunctionError> {
    let (subject, kw_cursor) = match args {
        [kw] => (None, kw),
        [subject, kw] => (Some(decode_expr(subject, ctx, Some(span))?), kw),
        _ => {
            return Err(QuotedFunctionError::new(
                "quoted `case` expects a subject and `do` body",
            ));
        }
    };
    let entries = decode_keyword_entries(kw_cursor)?;
    let Some((_, body)) = entries.into_iter().find(|(key, _)| key == "do") else {
        return Err(QuotedFunctionError::new("quoted `case` is missing `do` clauses"));
    };
    let clauses = body
        .list_items()?
        .into_iter()
        .map(|clause| decode_match_clause(&clause, ctx, Some(span)))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Spanned::new(Expr::Case(subject.map(Box::new), clauses), span))
}

fn decode_cond(
    args: &[QuotedSourceCursor],
    ctx: &DecodeCtx<'_>,
    span: Span,
) -> Result<Spanned<Expr>, QuotedFunctionError> {
    let entries = decode_keyword_entries(&args[0])?;
    let Some((_, body)) = entries.into_iter().find(|(key, _)| key == "do") else {
        return Err(QuotedFunctionError::new("quoted `cond` is missing `do` clauses"));
    };
    let mut clauses = Vec::new();
    for clause in body.list_items()? {
        let node = expect_ast_node(&clause, "cond clause")?;
        if atom_name(&node.head)? != "->" {
            return Err(QuotedFunctionError::new("quoted `cond` body expects `->` clauses"));
        }
        let parts = node.tail.list_items()?;
        if parts.len() != 2 {
            return Err(QuotedFunctionError::new(
                "quoted `cond` clause expects test list and body",
            ));
        }
        let tests = parts[0].list_items()?;
        if tests.len() != 1 {
            return Err(QuotedFunctionError::new("quoted `cond` clause expects one test"));
        }
        clauses.push((
            decode_expr(&tests[0], ctx, Some(span))?,
            decode_expr(&parts[1], ctx, Some(span))?,
        ));
    }
    Ok(Spanned::new(Expr::Cond(clauses), span))
}

fn decode_receive(
    args: &[QuotedSourceCursor],
    ctx: &DecodeCtx<'_>,
    span: Span,
) -> Result<Spanned<Expr>, QuotedFunctionError> {
    let entries = decode_keyword_entries(&args[0])?;
    let mut clauses = Vec::new();
    let mut after = None;
    for (key, value) in entries {
        match key.as_str() {
            "do" => {
                clauses = value
                    .list_items()?
                    .into_iter()
                    .map(|clause| decode_match_clause(&clause, ctx, Some(span)))
                    .collect::<Result<Vec<_>, _>>()?;
            }
            "after" => {
                let after_items = value.list_items()?;
                let Some(clause) = after_items.first() else {
                    return Err(QuotedFunctionError::new("quoted `receive after` is empty"));
                };
                after = Some(Box::new(decode_after_clause(clause, ctx, Some(span))?));
            }
            other => {
                return Err(QuotedFunctionError::new(format!(
                    "unsupported quoted `receive` keyword `{other}`"
                )));
            }
        }
    }
    Ok(Spanned::new(Expr::Receive { clauses, after }, span))
}

fn decode_lambda(
    args: &[QuotedSourceCursor],
    ctx: &DecodeCtx<'_>,
    span: Span,
) -> Result<Spanned<Expr>, QuotedFunctionError> {
    let clauses = args
        .iter()
        .map(|clause| decode_lambda_clause(clause, ctx, Some(span)))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Spanned::new(Expr::Lambda(clauses), span))
}

fn decode_quote(
    args: &[QuotedSourceCursor],
    ctx: &DecodeCtx<'_>,
    span: Span,
) -> Result<Spanned<Expr>, QuotedFunctionError> {
    let entries = decode_keyword_entries(&args[0])?;
    let Some((_, body)) = entries.into_iter().find(|(key, _)| key == "do") else {
        return Err(QuotedFunctionError::new("quoted `quote` is missing `do` body"));
    };
    Ok(Spanned::new(
        Expr::Quote(Box::new(decode_expr(&body, ctx, Some(span))?)),
        span,
    ))
}

fn decode_map_expr(
    args: &[QuotedSourceCursor],
    ctx: &DecodeCtx<'_>,
    span: Span,
) -> Result<Spanned<Expr>, QuotedFunctionError> {
    if args.len() == 1
        && let Some(node) = args[0].ast_node()?
        && atom_name(&node.head)? == "|"
    {
        let parts = node.tail.list_items()?;
        if parts.len() != 2 {
            return Err(QuotedFunctionError::new(
                "quoted map update expects base and keyword list",
            ));
        }
        let base = decode_expr(&parts[0], ctx, Some(span))?;
        let entries = decode_expr_keyword_pairs(&parts[1], ctx, Some(span))?;
        return Ok(Spanned::new(Expr::MapUpdate(Box::new(base), entries), span));
    }

    let entries = args
        .iter()
        .map(|entry| decode_expr_pair(entry, ctx, Some(span)))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Spanned::new(Expr::Map(entries), span))
}

fn decode_struct_expr(
    args: &[QuotedSourceCursor],
    ctx: &DecodeCtx<'_>,
    span: Span,
) -> Result<Spanned<Expr>, QuotedFunctionError> {
    let module = decode_module_name(&args[0])?;
    let map = expect_ast_node(&args[1], "struct map payload")?;
    if atom_name(&map.head)? != "%{}" {
        return Err(QuotedFunctionError::new("quoted struct payload must be a `%{}` node"));
    }
    let mut fields = Vec::new();
    for entry in map.tail.list_items()? {
        let (key, value) = decode_expr_pair(&entry, ctx, Some(span))?;
        let Expr::Atom(field) = key.node else {
            return Err(QuotedFunctionError::new("quoted struct keys must be atoms"));
        };
        fields.push((field, value));
    }
    Ok(Spanned::new(Expr::Struct { module, fields }, span))
}

fn decode_bitstring_expr(
    args: &[QuotedSourceCursor],
    ctx: &DecodeCtx<'_>,
    span: Span,
) -> Result<Spanned<Expr>, QuotedFunctionError> {
    let mut fields = Vec::new();
    for field in args {
        if let Some(node) = field.ast_node()?
            && atom_name(&node.head)? == "::"
        {
            let parts = node.tail.list_items()?;
            if parts.len() != 2 {
                return Err(QuotedFunctionError::new(
                    "quoted bitstring field expects value and spec",
                ));
            }
            fields.push(BitField {
                value: decode_expr(&parts[0], ctx, Some(span))?,
                spec: decode_bit_spec(&parts[1])?,
            });
            continue;
        }
        fields.push(BitField {
            value: decode_expr(field, ctx, Some(span))?,
            spec: BitFieldSpec::default(),
        });
    }
    Ok(Spanned::new(Expr::Bitstring(fields), span))
}

fn decode_fn_ref_expr(
    cursor: &QuotedSourceCursor,
    ctx: &DecodeCtx<'_>,
    span: Span,
) -> Result<Spanned<Expr>, QuotedFunctionError> {
    let node = expect_ast_node(cursor, "function reference payload")?;
    if atom_name(&node.head)? != "/" {
        return Err(QuotedFunctionError::new("quoted `&` expects a `/` target"));
    }
    let parts = node.tail.list_items()?;
    if parts.len() != 2 {
        return Err(QuotedFunctionError::new(
            "quoted function reference expects target and arity",
        ));
    }
    let name = decode_fn_ref_name(&parts[0], ctx, Some(span))?;
    let arity = parts[1].int_value()? as usize;
    Ok(Spanned::new(Expr::FnRef { name, arity }, span))
}

fn decode_match_clause(
    cursor: &QuotedSourceCursor,
    ctx: &DecodeCtx<'_>,
    fallback_span: Option<Span>,
) -> Result<MatchClause, QuotedFunctionError> {
    let node = expect_ast_node(cursor, "match clause")?;
    let span = span_from_meta(&node.meta, ctx).unwrap_or(fallback_span.unwrap_or(Span::DUMMY));
    if atom_name(&node.head)? != "->" {
        return Err(QuotedFunctionError::new("quoted clause expects a `->` head"));
    }
    let parts = node.tail.list_items()?;
    if parts.len() != 2 {
        return Err(QuotedFunctionError::new("quoted clause expects pattern list and body"));
    }
    let patterns = parts[0].list_items()?;
    if patterns.len() != 1 {
        return Err(QuotedFunctionError::new("quoted match clause expects one pattern"));
    }
    let (pattern, guard) = if let Some(when) = patterns[0].ast_node()?
        && atom_name(&when.head)? == "when"
    {
        let args = when.tail.list_items()?;
        if args.len() != 2 {
            return Err(QuotedFunctionError::new(
                "quoted guarded clause expects pattern and guard",
            ));
        }
        (
            decode_pattern(&args[0], ctx, Some(span))?,
            Some(decode_expr(&args[1], ctx, Some(span))?),
        )
    } else {
        (decode_pattern(&patterns[0], ctx, Some(span))?, None)
    };
    Ok(MatchClause {
        pattern,
        guard,
        body: decode_expr(&parts[1], ctx, Some(span))?,
        span,
    })
}

fn decode_after_clause(
    cursor: &QuotedSourceCursor,
    ctx: &DecodeCtx<'_>,
    fallback_span: Option<Span>,
) -> Result<AfterClause, QuotedFunctionError> {
    let node = expect_ast_node(cursor, "after clause")?;
    let span = span_from_meta(&node.meta, ctx).unwrap_or(fallback_span.unwrap_or(Span::DUMMY));
    if atom_name(&node.head)? != "->" {
        return Err(QuotedFunctionError::new("quoted `after` clause expects `->`"));
    }
    let parts = node.tail.list_items()?;
    if parts.len() != 2 {
        return Err(QuotedFunctionError::new(
            "quoted `after` clause expects timeout and body",
        ));
    }
    let patterns = parts[0].list_items()?;
    if patterns.len() != 1 {
        return Err(QuotedFunctionError::new(
            "quoted `after` clause expects one timeout expression",
        ));
    }
    Ok(AfterClause {
        timeout: decode_expr(&patterns[0], ctx, Some(span))?,
        body: decode_expr(&parts[1], ctx, Some(span))?,
        span,
    })
}

fn decode_lambda_clause(
    cursor: &QuotedSourceCursor,
    ctx: &DecodeCtx<'_>,
    fallback_span: Option<Span>,
) -> Result<LambdaClause, QuotedFunctionError> {
    let node = expect_ast_node(cursor, "lambda clause")?;
    let span = span_from_meta(&node.meta, ctx).unwrap_or(fallback_span.unwrap_or(Span::DUMMY));
    if atom_name(&node.head)? != "->" {
        return Err(QuotedFunctionError::new("quoted lambda clause expects `->`"));
    }
    let parts = node.tail.list_items()?;
    if parts.len() != 2 {
        return Err(QuotedFunctionError::new("quoted lambda clause expects params and body"));
    }
    let params_root = parts[0].list_items()?;
    let (params, guard) = if params_root.len() == 1 {
        if let Some(when) = params_root[0].ast_node()?
            && atom_name(&when.head)? == "when"
        {
            let args = when.tail.list_items()?;
            let Some((guard_cursor, param_cursors)) = args.split_last() else {
                return Err(QuotedFunctionError::new("quoted guarded lambda clause is empty"));
            };
            let params = param_cursors
                .iter()
                .map(|param| decode_pattern(param, ctx, Some(span)))
                .collect::<Result<Vec<_>, _>>()?;
            let guard = decode_expr(guard_cursor, ctx, Some(span))?;
            (params, Some(guard))
        } else {
            (
                params_root
                    .iter()
                    .map(|param| decode_pattern(param, ctx, Some(span)))
                    .collect::<Result<Vec<_>, _>>()?,
                None,
            )
        }
    } else {
        (
            params_root
                .iter()
                .map(|param| decode_pattern(param, ctx, Some(span)))
                .collect::<Result<Vec<_>, _>>()?,
            None,
        )
    };
    Ok(LambdaClause {
        params,
        guard,
        body: decode_expr(&parts[1], ctx, Some(span))?,
        span,
    })
}

fn decode_map_pattern(
    args: &[QuotedSourceCursor],
    ctx: &DecodeCtx<'_>,
    span: Span,
) -> Result<Spanned<Pattern>, QuotedFunctionError> {
    let entries = args
        .iter()
        .map(|entry| decode_pattern_pair(entry, ctx, Some(span)))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Spanned::new(Pattern::Map(entries), span))
}

fn decode_struct_pattern(
    args: &[QuotedSourceCursor],
    ctx: &DecodeCtx<'_>,
    span: Span,
) -> Result<Spanned<Pattern>, QuotedFunctionError> {
    let module = decode_module_name(&args[0])?;
    let map = expect_ast_node(&args[1], "struct pattern payload")?;
    if atom_name(&map.head)? != "%{}" {
        return Err(QuotedFunctionError::new("quoted struct pattern payload must be `%{}`"));
    }
    let mut fields = Vec::new();
    for entry in map.tail.list_items()? {
        let (key, value) = decode_pattern_pair(&entry, ctx, Some(span))?;
        let Pattern::Atom(field) = key.node else {
            return Err(QuotedFunctionError::new("quoted struct pattern keys must be atoms"));
        };
        fields.push((field, value));
    }
    Ok(Spanned::new(Pattern::Struct { module, fields }, span))
}

fn decode_bitstring_pattern(
    args: &[QuotedSourceCursor],
    ctx: &DecodeCtx<'_>,
    span: Span,
) -> Result<Spanned<Pattern>, QuotedFunctionError> {
    let mut fields = Vec::new();
    for field in args {
        if let Some(node) = field.ast_node()?
            && atom_name(&node.head)? == "::"
        {
            let parts = node.tail.list_items()?;
            if parts.len() != 2 {
                return Err(QuotedFunctionError::new(
                    "quoted bitstring pattern field expects value and spec",
                ));
            }
            fields.push(BitField {
                value: decode_pattern(&parts[0], ctx, Some(span))?,
                spec: decode_bit_spec(&parts[1])?,
            });
            continue;
        }
        fields.push(BitField {
            value: decode_pattern(field, ctx, Some(span))?,
            spec: BitFieldSpec::default(),
        });
    }
    Ok(Spanned::new(Pattern::Bitstring(fields), span))
}

fn decode_negative_pattern(
    cursor: &QuotedSourceCursor,
    ctx: &DecodeCtx<'_>,
    span: Span,
) -> Result<Spanned<Pattern>, QuotedFunctionError> {
    let decoded = decode_pattern(cursor, ctx, Some(span))?;
    match decoded.node {
        Pattern::Int(value) => Ok(Spanned::new(Pattern::Int(-value), span)),
        Pattern::Float(value) => Ok(Spanned::new(Pattern::Float(-value), span)),
        other => Err(QuotedFunctionError::new(format!(
            "quoted negative pattern expects a number, got {:?}",
            other
        ))),
    }
}

fn decode_list_expr(
    cursor: &QuotedSourceCursor,
    ctx: &DecodeCtx<'_>,
    span: Span,
) -> Result<Spanned<Expr>, QuotedFunctionError> {
    let items = cursor.list_items()?;
    let (items, tail) = split_improper_list(items, ctx, span)?;
    Ok(Spanned::new(
        Expr::List(decode_exprs(&items, ctx, Some(span))?, tail.map(Box::new)),
        span,
    ))
}

fn decode_list_pattern(
    cursor: &QuotedSourceCursor,
    ctx: &DecodeCtx<'_>,
    span: Span,
) -> Result<Spanned<Pattern>, QuotedFunctionError> {
    let items = cursor.list_items()?;
    let (items, tail) = split_improper_pattern_list(items, ctx, span)?;
    Ok(Spanned::new(
        Pattern::List(
            items
                .iter()
                .map(|item| decode_pattern(item, ctx, Some(span)))
                .collect::<Result<Vec<_>, _>>()?,
            tail.map(Box::new),
        ),
        span,
    ))
}

fn split_improper_list(
    items: Vec<QuotedSourceCursor>,
    ctx: &DecodeCtx<'_>,
    span: Span,
) -> Result<(Vec<QuotedSourceCursor>, Option<Spanned<Expr>>), QuotedFunctionError> {
    let Some((last, prefix)) = items.split_last() else {
        return Ok((Vec::new(), None));
    };
    if let Some(node) = last.ast_node()?
        && atom_name(&node.head)? == "|"
    {
        let parts = node.tail.list_items()?;
        if parts.len() != 2 {
            return Err(QuotedFunctionError::new(
                "quoted improper list marker expects head and tail",
            ));
        }
        let mut heads = prefix.to_vec();
        heads.push(parts[0].clone());
        return Ok((heads, Some(decode_expr(&parts[1], ctx, Some(span))?)));
    }
    Ok((items, None))
}

fn split_improper_pattern_list(
    items: Vec<QuotedSourceCursor>,
    ctx: &DecodeCtx<'_>,
    span: Span,
) -> Result<(Vec<QuotedSourceCursor>, Option<Spanned<Pattern>>), QuotedFunctionError> {
    let Some((last, prefix)) = items.split_last() else {
        return Ok((Vec::new(), None));
    };
    if let Some(node) = last.ast_node()?
        && atom_name(&node.head)? == "|"
    {
        let parts = node.tail.list_items()?;
        if parts.len() != 2 {
            return Err(QuotedFunctionError::new(
                "quoted improper pattern list marker expects head and tail",
            ));
        }
        let mut heads = prefix.to_vec();
        heads.push(parts[0].clone());
        return Ok((heads, Some(decode_pattern(&parts[1], ctx, Some(span))?)));
    }
    Ok((items, None))
}

fn decode_exprs(
    args: &[QuotedSourceCursor],
    ctx: &DecodeCtx<'_>,
    fallback_span: Option<Span>,
) -> Result<Vec<Spanned<Expr>>, QuotedFunctionError> {
    args.iter()
        .map(|arg| decode_expr(arg, ctx, fallback_span))
        .collect::<Result<Vec<_>, _>>()
}

fn decode_expr_pair(
    cursor: &QuotedSourceCursor,
    ctx: &DecodeCtx<'_>,
    fallback_span: Option<Span>,
) -> Result<(Spanned<Expr>, Spanned<Expr>), QuotedFunctionError> {
    let items = cursor.tuple_items()?;
    if items.len() != 2 {
        return Err(QuotedFunctionError::new("quoted pair expects a 2-tuple"));
    }
    Ok((
        decode_expr(&items[0], ctx, fallback_span)?,
        decode_expr(&items[1], ctx, fallback_span)?,
    ))
}

fn decode_pattern_pair(
    cursor: &QuotedSourceCursor,
    ctx: &DecodeCtx<'_>,
    fallback_span: Option<Span>,
) -> Result<(Spanned<Pattern>, Spanned<Pattern>), QuotedFunctionError> {
    let items = cursor.tuple_items()?;
    if items.len() != 2 {
        return Err(QuotedFunctionError::new("quoted pair expects a 2-tuple"));
    }
    Ok((
        decode_pattern(&items[0], ctx, fallback_span)?,
        decode_pattern(&items[1], ctx, fallback_span)?,
    ))
}

fn decode_expr_keyword_pairs(
    cursor: &QuotedSourceCursor,
    ctx: &DecodeCtx<'_>,
    fallback_span: Option<Span>,
) -> Result<Vec<ExprPair>, QuotedFunctionError> {
    cursor
        .list_items()?
        .into_iter()
        .map(|entry| decode_expr_pair(&entry, ctx, fallback_span))
        .collect::<Result<Vec<_>, _>>()
}

fn decode_keyword_entries(
    cursor: &QuotedSourceCursor,
) -> Result<Vec<(String, QuotedSourceCursor)>, QuotedFunctionError> {
    let mut out = Vec::new();
    for entry in cursor.list_items()? {
        let items = entry.tuple_items()?;
        if items.len() != 2 {
            return Err(QuotedFunctionError::new("quoted keyword entry expects a 2-tuple"));
        }
        out.push((items[0].atom_name()?, items[1].clone()));
    }
    Ok(out)
}

fn decode_module_name(cursor: &QuotedSourceCursor) -> Result<ModuleName, QuotedFunctionError> {
    let node = expect_ast_node(cursor, "module alias")?;
    if atom_name(&node.head)? != "__aliases__" {
        return Err(QuotedFunctionError::new(
            "quoted module path expects an __aliases__ node",
        ));
    }
    Ok(ModuleName::from_segments(
        node.tail.list_atom_names().map_err(QuotedFunctionError::from)?,
    ))
}

fn decode_fn_ref_name(
    cursor: &QuotedSourceCursor,
    ctx: &DecodeCtx<'_>,
    fallback_span: Option<Span>,
) -> Result<String, QuotedFunctionError> {
    if let Some(node) = cursor.ast_node()? {
        let span = span_from_meta(&node.meta, ctx).unwrap_or(fallback_span.unwrap_or(Span::DUMMY));
        if !is_list_like(&node.tail) {
            return atom_name(&node.head);
        }
        let args = node.tail.list_items()?;
        return match atom_name(&node.head)?.as_str() {
            "__aliases__" => alias_name_from_args(&args),
            "." if args.len() == 2 => Ok(format!(
                "{}.{}",
                decode_fn_ref_name(&args[0], ctx, Some(span))?,
                args[1].atom_name()?
            )),
            other => Err(QuotedFunctionError::new(format!(
                "unsupported quoted function-ref target head `{other}`"
            ))),
        };
    }
    Err(QuotedFunctionError::new("unsupported quoted function-ref target"))
}

fn pattern_var_name(
    cursor: &QuotedSourceCursor,
    ctx: &DecodeCtx<'_>,
    fallback_span: Option<Span>,
) -> Result<Option<String>, QuotedFunctionError> {
    let decoded = decode_pattern(cursor, ctx, fallback_span)?;
    Ok(match decoded.node {
        Pattern::Var(name) => Some(name),
        Pattern::Wildcard => Some("_".to_string()),
        _ => None,
    })
}

fn rendered_type_expr_body(
    cursor: &QuotedSourceCursor,
    ctx: &DecodeCtx<'_>,
) -> Result<TypeExprBody, QuotedFunctionError> {
    Ok(TypeExprBody(lex_fragment_tokens(ctx, &render_type_expr(cursor)?)?))
}

fn decode_spec_attribute(raw: &str, ctx: &DecodeCtx<'_>) -> Result<Attribute, QuotedFunctionError> {
    let mut parser = FragmentCursor::new(lex_fragment_stream(ctx, raw)?);
    let (name, param_body_tokens) =
        if matches!(parser.peek(), Tok::Ident(_)) && matches!(parser.peek_at(1), Some(Tok::LParen)) {
            let name = match parser.bump() {
                Some(Tok::Ident(name)) => name,
                _ => unreachable!("guarded by peek"),
            };
            parser.expect_lparen("`(` after @spec name")?;
            let mut params = Vec::new();
            if !matches!(parser.peek(), Tok::RParen) {
                loop {
                    let tokens = parser.collect_type_tokens(TypeTokenBoundary::SpecParam);
                    if tokens.is_empty() {
                        return Err(QuotedFunctionError::new("expected type expression in @spec param list"));
                    }
                    params.push(TypeExprBody(tokens));
                    if !parser.eat_comma() {
                        break;
                    }
                }
            }
            parser.expect_rparen("`)` after @spec param list")?;
            (name, params)
        } else {
            let left = parser.collect_type_tokens(TypeTokenBoundary::SpecInfixOperand);
            if left.is_empty() {
                return Err(QuotedFunctionError::new(
                    "expected type expression before operator in @spec",
                ));
            }
            let name = parser
                .bump()
                .and_then(|tok| operator_token_name(&tok).map(str::to_string))
                .ok_or_else(|| QuotedFunctionError::new("expected `@spec name(` or `@spec T1 <op> T2`"))?;
            let right = parser.collect_type_tokens(TypeTokenBoundary::SpecInfixOperand);
            if right.is_empty() {
                return Err(QuotedFunctionError::new(
                    "expected type expression after operator in @spec",
                ));
            }
            (name, vec![TypeExprBody(left), TypeExprBody(right)])
        };

    parser.expect_colon_colon("`::` in @spec")?;
    let result_body_tokens = parser.collect_type_tokens(TypeTokenBoundary::TypeBody);
    if result_body_tokens.is_empty() {
        return Err(QuotedFunctionError::new(
            "expected result type expression after `::` in @spec",
        ));
    }

    let mut constraints = Vec::new();
    if parser.eat_when() {
        loop {
            let (var, kw_colon) = match parser.bump() {
                Some(Tok::Ident(name)) => (name, false),
                Some(Tok::KwKey(name)) => (name, true),
                Some(other) => {
                    return Err(QuotedFunctionError::new(format!(
                        "expected type variable after `when`, got {:?}",
                        other
                    )));
                }
                None => return Err(QuotedFunctionError::new("expected type variable after `when`")),
            };
            if !kw_colon {
                parser.expect_colon("`:` after constrained type variable")?;
            }
            let body = parser.collect_type_tokens(TypeTokenBoundary::Constraint);
            if body.is_empty() {
                return Err(QuotedFunctionError::new(format!(
                    "expected constraint type expression after `{}:`",
                    var
                )));
            }
            constraints.push((var, TypeExprBody(body)));
            if !parser.eat_comma() {
                break;
            }
        }
    }

    parser.expect_eof("end of @spec")?;
    Ok(Attribute::Spec(SpecDecl {
        name,
        param_body_tokens,
        result_body_tokens: TypeExprBody(result_body_tokens),
        constraints,
    }))
}

fn render_type_expr(cursor: &QuotedSourceCursor) -> Result<String, QuotedFunctionError> {
    if let Some(node) = cursor.ast_node()? {
        if !is_list_like(&node.tail) {
            return atom_name(&node.head);
        }
        let args = node.tail.list_items()?;
        return match atom_name(&node.head)?.as_str() {
            "__aliases__" => alias_name_from_args(&args),
            "{}" => Ok(format!(
                "{{{}}}",
                args.iter()
                    .map(render_type_expr)
                    .collect::<Result<Vec<_>, _>>()?
                    .join(", ")
            )),
            "%" => {
                let module = render_type_expr(&args[0])?;
                let fields = render_struct_field_entries(&args[1])?;
                Ok(format!("%{module}{{{fields}}}"))
            }
            name if args.is_empty() => Ok(name.to_string()),
            name if args.len() == 2 && matches!(name, "|" | "||") => Ok(format!(
                "{} | {}",
                render_type_expr(&args[0])?,
                render_type_expr(&args[1])?
            )),
            name => Ok(format!(
                "{name}({})",
                args.iter()
                    .map(render_type_expr)
                    .collect::<Result<Vec<_>, _>>()?
                    .join(", ")
            )),
        };
    }
    match cursor.root().tag() {
        fz_runtime::any_value::ValueKind::INT => Ok(cursor.int_value()?.to_string()),
        fz_runtime::any_value::ValueKind::FLOAT => {
            Ok(cursor.root().load_float().map_err(QuotedSourceError::from)?.to_string())
        }
        fz_runtime::any_value::ValueKind::ATOM => Ok(cursor.atom_name()?),
        fz_runtime::any_value::ValueKind::BITSTRING | fz_runtime::any_value::ValueKind::PROCBIN => {
            Ok(cursor.utf8_binary_text()?)
        }
        fz_runtime::any_value::ValueKind::LIST => Ok(format!(
            "[{}]",
            cursor
                .list_items()?
                .into_iter()
                .map(|item| render_type_expr(&item))
                .collect::<Result<Vec<_>, _>>()?
                .join(", ")
        )),
        fz_runtime::any_value::ValueKind::STRUCT => Ok(format!(
            "{{{}}}",
            cursor
                .tuple_items()?
                .into_iter()
                .map(|item| render_type_expr(&item))
                .collect::<Result<Vec<_>, _>>()?
                .join(", ")
        )),
        other => Err(QuotedFunctionError::new(format!(
            "unsupported quoted type fragment kind {:?}",
            other
        ))),
    }
}

fn decode_bit_spec(cursor: &QuotedSourceCursor) -> Result<BitFieldSpec, QuotedFunctionError> {
    let mut spec = BitFieldSpec::default();
    apply_bit_spec_modifier(cursor, &mut spec)?;
    Ok(spec)
}

fn apply_bit_spec_modifier(cursor: &QuotedSourceCursor, spec: &mut BitFieldSpec) -> Result<(), QuotedFunctionError> {
    if let Some(node) = cursor.ast_node()? {
        let args = if is_list_like(&node.tail) {
            node.tail.list_items()?
        } else {
            Vec::new()
        };
        return match atom_name(&node.head)?.as_str() {
            "-" if args.len() == 2 => {
                apply_bit_spec_modifier(&args[0], spec)?;
                apply_bit_spec_modifier(&args[1], spec)
            }
            "size" if args.len() == 1 => {
                spec.size = Some(decode_bit_size(&args[0])?);
                Ok(())
            }
            "unit" if args.len() == 1 => {
                spec.unit = Some(decode_bit_unit(&args[0])?);
                Ok(())
            }
            name if args.is_empty() => apply_bit_modifier_name(spec, name),
            other => Err(QuotedFunctionError::new(format!(
                "unsupported quoted bit-spec modifier `{other}`"
            ))),
        };
    }

    match cursor.root().tag() {
        fz_runtime::any_value::ValueKind::INT => {
            let raw = cursor.int_value()?;
            let size = u32::try_from(raw)
                .map_err(|_| QuotedFunctionError::new(format!("bitstring size literal must fit in u32, got {raw}")))?;
            spec.size = Some(BitSize::Literal(size));
            Ok(())
        }
        fz_runtime::any_value::ValueKind::ATOM => apply_bit_modifier_name(spec, &cursor.atom_name()?),
        fz_runtime::any_value::ValueKind::BITSTRING | fz_runtime::any_value::ValueKind::PROCBIN => {
            apply_bit_modifier_name(spec, &cursor.utf8_binary_text()?)
        }
        other => Err(QuotedFunctionError::new(format!(
            "unsupported quoted bit-spec fragment kind {:?}",
            other
        ))),
    }
}

fn decode_bit_size(cursor: &QuotedSourceCursor) -> Result<BitSize, QuotedFunctionError> {
    if let Ok(value) = cursor.int_value() {
        return u32::try_from(value)
            .map(BitSize::Literal)
            .map_err(|_| QuotedFunctionError::new(format!("bitstring size literal must fit in u32, got {value}")));
    }
    if let Some(node) = cursor.ast_node()?
        && !is_list_like(&node.tail)
    {
        return Ok(BitSize::Var(atom_name(&node.head)?));
    }
    match cursor.root().tag() {
        fz_runtime::any_value::ValueKind::ATOM => Ok(BitSize::Var(cursor.atom_name()?)),
        other => Err(QuotedFunctionError::new(format!(
            "bitstring size expects int or variable, got {:?}",
            other
        ))),
    }
}

fn decode_bit_unit(cursor: &QuotedSourceCursor) -> Result<u32, QuotedFunctionError> {
    let raw = cursor.int_value()?;
    u32::try_from(raw).map_err(|_| QuotedFunctionError::new(format!("bitstring unit must fit in u32, got {raw}")))
}

fn apply_bit_modifier_name(spec: &mut BitFieldSpec, name: &str) -> Result<(), QuotedFunctionError> {
    match name {
        "integer" => spec.ty = BitType::Integer,
        "float" => spec.ty = BitType::Float,
        "binary" => spec.ty = BitType::Binary,
        "bits" | "bitstring" => spec.ty = BitType::Bits,
        "utf8" => spec.ty = BitType::Utf8,
        "utf16" => spec.ty = BitType::Utf16,
        "utf32" => spec.ty = BitType::Utf32,
        "big" => spec.endian = Endian::Big,
        "little" => spec.endian = Endian::Little,
        "native" => spec.endian = Endian::Native,
        "signed" => spec.signed = true,
        "unsigned" => spec.signed = false,
        other => return Err(QuotedFunctionError::new(format!("unknown bitstring modifier: {other}"))),
    }
    Ok(())
}

fn render_struct_field_entries(cursor: &QuotedSourceCursor) -> Result<String, QuotedFunctionError> {
    let node = expect_ast_node(cursor, "struct field map")?;
    if atom_name(&node.head)? != "%{}" {
        return Err(QuotedFunctionError::new(
            "quoted struct fields must be wrapped in `%{}`",
        ));
    }
    let mut fields = Vec::new();
    for entry in node.tail.list_items()? {
        let pair = entry.tuple_items()?;
        if pair.len() != 2 {
            return Err(QuotedFunctionError::new("quoted struct field expects a 2-tuple"));
        }
        fields.push(format!("{}: {}", pair[0].atom_name()?, render_type_expr(&pair[1])?));
    }
    Ok(fields.join(", "))
}

fn lex_fragment_stream(ctx: &DecodeCtx<'_>, text: &str) -> Result<Vec<Token>, QuotedFunctionError> {
    Lexer::with_source_name(text, ctx.code_name.to_string())
        .tokenize(ctx.tel)
        .map_err(|error| QuotedFunctionError::new(error.msg))
}

fn lex_fragment_tokens(ctx: &DecodeCtx<'_>, text: &str) -> Result<Vec<Token>, QuotedFunctionError> {
    Ok(lex_fragment_stream(ctx, text)?
        .into_iter()
        .filter(|token| !matches!(token.tok, Tok::Eof | Tok::Newline))
        .collect())
}

fn strip_extern_param_name(tokens: Vec<Token>) -> Result<Vec<Token>, QuotedFunctionError> {
    let mut depth = 0_i32;
    for (index, token) in tokens.iter().enumerate() {
        match token.tok {
            Tok::LParen | Tok::LBrack | Tok::LBrace => depth += 1,
            Tok::RParen | Tok::RBrack | Tok::RBrace => depth -= 1,
            Tok::ColonColon if depth == 0 => {
                let body = tokens[index + 1..].to_vec();
                if body.is_empty() {
                    return Err(QuotedFunctionError::new("expected extern parameter type after `::`"));
                }
                return Ok(body);
            }
            _ => {}
        }
    }
    Ok(tokens)
}

#[derive(Debug, Clone, Copy)]
enum TypeTokenBoundary {
    SpecParam,
    SpecInfixOperand,
    TypeBody,
    Constraint,
}

impl TypeTokenBoundary {
    fn stops_before(self, tok: &Tok, depth: i32) -> bool {
        if depth != 0 {
            return false;
        }
        match self {
            TypeTokenBoundary::SpecParam => matches!(tok, Tok::Comma | Tok::RParen | Tok::Eof),
            TypeTokenBoundary::SpecInfixOperand => {
                operator_token_name(tok).is_some() || matches!(tok, Tok::ColonColon | Tok::Eof)
            }
            TypeTokenBoundary::TypeBody => matches!(tok, Tok::When | Tok::Eof),
            TypeTokenBoundary::Constraint => matches!(tok, Tok::Comma | Tok::Eof),
        }
    }
}

struct FragmentCursor {
    toks: Vec<Token>,
    pos: usize,
}

impl FragmentCursor {
    fn new(toks: Vec<Token>) -> Self {
        Self { toks, pos: 0 }
    }

    fn peek(&self) -> Tok {
        self.peek_at(0).cloned().unwrap_or(Tok::Eof)
    }

    fn peek_at(&self, off: usize) -> Option<&Tok> {
        self.toks.get(self.pos + off).map(|token| &token.tok)
    }

    fn bump(&mut self) -> Option<Tok> {
        let tok = self.toks.get(self.pos).map(|token| token.tok.clone());
        if tok.is_some() {
            self.pos += 1;
        }
        tok
    }

    fn eat_comma(&mut self) -> bool {
        self.eat(|tok| matches!(tok, Tok::Comma))
    }

    fn eat_when(&mut self) -> bool {
        self.eat(|tok| matches!(tok, Tok::When))
    }

    fn expect_lparen(&mut self, label: &str) -> Result<(), QuotedFunctionError> {
        self.expect(|tok| matches!(tok, Tok::LParen), label)
    }

    fn expect_rparen(&mut self, label: &str) -> Result<(), QuotedFunctionError> {
        self.expect(|tok| matches!(tok, Tok::RParen), label)
    }

    fn expect_colon_colon(&mut self, label: &str) -> Result<(), QuotedFunctionError> {
        self.expect(|tok| matches!(tok, Tok::ColonColon), label)
    }

    fn expect_colon(&mut self, label: &str) -> Result<(), QuotedFunctionError> {
        self.expect(|tok| matches!(tok, Tok::Colon), label)
    }

    fn expect_eof(&mut self, label: &str) -> Result<(), QuotedFunctionError> {
        self.expect(|tok| matches!(tok, Tok::Eof), label)
    }

    fn collect_type_tokens(&mut self, boundary: TypeTokenBoundary) -> Vec<Token> {
        let mut out = Vec::new();
        let mut depth = 0_i32;
        while let Some(token) = self.toks.get(self.pos).cloned() {
            if boundary.stops_before(&token.tok, depth) {
                break;
            }
            match token.tok {
                Tok::LParen | Tok::LBrack | Tok::LBrace => depth += 1,
                Tok::RParen | Tok::RBrack | Tok::RBrace => depth -= 1,
                _ => {}
            }
            self.pos += 1;
            out.push(token);
        }
        out
    }

    fn eat(&mut self, pred: impl FnOnce(&Tok) -> bool) -> bool {
        if self.peek_at(0).is_some_and(pred) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, pred: impl FnOnce(&Tok) -> bool, label: &str) -> Result<(), QuotedFunctionError> {
        match self.bump() {
            Some(tok) if pred(&tok) => Ok(()),
            Some(other) => Err(QuotedFunctionError::new(format!("expected {label}, got {:?}", other))),
            None => Err(QuotedFunctionError::new(format!("expected {label}, got eof"))),
        }
    }
}

fn operator_token_name(tok: &Tok) -> Option<&'static str> {
    Some(match tok {
        Tok::Plus => "+",
        Tok::Minus => "-",
        Tok::Star => "*",
        Tok::Slash => "/",
        Tok::Percent => "%",
        Tok::EqEq => "==",
        Tok::NotEq => "!=",
        Tok::Lt => "<",
        Tok::LtEq => "<=",
        Tok::Gt => ">",
        Tok::GtEq => ">=",
        _ => return None,
    })
}

fn required_map_utf8(cursor: &QuotedSourceCursor, key: &str) -> Result<String, QuotedFunctionError> {
    cursor
        .map_value(key)?
        .ok_or_else(|| QuotedFunctionError::new(format!("quoted map is missing `{key}`")))?
        .utf8_binary_text()
        .map_err(QuotedFunctionError::from)
}

fn required_map_list_utf8(cursor: &QuotedSourceCursor, key: &str) -> Result<Vec<String>, QuotedFunctionError> {
    cursor
        .map_value(key)?
        .ok_or_else(|| QuotedFunctionError::new(format!("quoted map is missing `{key}`")))?
        .list_items()?
        .into_iter()
        .map(|item| item.utf8_binary_text().map_err(QuotedFunctionError::from))
        .collect::<Result<Vec<_>, _>>()
}

fn required_map_bool(cursor: &QuotedSourceCursor, key: &str) -> Result<bool, QuotedFunctionError> {
    let value = cursor
        .map_value(key)?
        .ok_or_else(|| QuotedFunctionError::new(format!("quoted map is missing `{key}`")))?;
    match value.atom_name()?.as_str() {
        "true" => Ok(true),
        "false" => Ok(false),
        other => Err(QuotedFunctionError::new(format!(
            "quoted map bool `{key}` expected true/false, got `{other}`"
        ))),
    }
}

fn optional_map_keyword_utf8(
    cursor: &QuotedSourceCursor,
    key: &str,
) -> Result<Vec<(String, String)>, QuotedFunctionError> {
    let Some(list) = cursor.map_value(key)? else {
        return Ok(Vec::new());
    };
    let mut out = Vec::new();
    for entry in list.list_items()? {
        let items = entry.tuple_items()?;
        if items.len() != 2 {
            return Err(QuotedFunctionError::new("quoted keyword entry expects a 2-tuple"));
        }
        out.push((items[0].atom_name()?, items[1].utf8_binary_text()?));
    }
    Ok(out)
}

fn expect_ast_node(cursor: &QuotedSourceCursor, context: &str) -> Result<QuotedAstNode, QuotedFunctionError> {
    cursor
        .ast_node()?
        .ok_or_else(|| QuotedFunctionError::new(format!("expected quoted AST node for {context}")))
}

fn atom_name(cursor: &QuotedSourceCursor) -> Result<String, QuotedFunctionError> {
    cursor.atom_name().map_err(QuotedFunctionError::from)
}

fn alias_name_from_args(args: &[QuotedSourceCursor]) -> Result<String, QuotedFunctionError> {
    args.iter()
        .map(|segment| segment.atom_name().map_err(QuotedFunctionError::from))
        .collect::<Result<Vec<_>, _>>()
        .map(|segments| segments.join("."))
}

fn is_alias(cursor: &QuotedSourceCursor) -> bool {
    cursor
        .ast_node()
        .ok()
        .flatten()
        .and_then(|node| atom_name(&node.head).ok().map(|name| name == "__aliases__"))
        .unwrap_or(false)
}

fn is_access_get(base: &QuotedSourceCursor, field: &QuotedSourceCursor) -> bool {
    is_alias(base) && field.atom_name().ok().as_deref() == Some("get")
}

fn is_list_like(cursor: &QuotedSourceCursor) -> bool {
    cursor.root().tag() == fz_runtime::any_value::ValueKind::LIST
}

fn span_from_meta(meta: &QuotedSourceCursor, ctx: &DecodeCtx<'_>) -> Result<Span, QuotedFunctionError> {
    let Some(span_map) = meta.map_value(META_SPAN_KEY)? else {
        return Ok(Span::DUMMY);
    };
    let line = span_map
        .map_value("line")?
        .ok_or_else(|| QuotedFunctionError::new("quoted span is missing `line`"))?
        .int_value()? as u32;
    let column = span_map
        .map_value("column")?
        .ok_or_else(|| QuotedFunctionError::new("quoted span is missing `column`"))?
        .int_value()? as u32;
    let length = span_map
        .map_value("length")?
        .ok_or_else(|| QuotedFunctionError::new("quoted span is missing `length`"))?
        .int_value()? as u32;
    let start = byte_offset_from_line_col(ctx.code_text, line, column)?;
    Ok(Span::new(
        SourceId(ctx.code_id.as_u32()),
        start,
        start.saturating_add(length),
    ))
}

fn byte_offset_from_line_col(source: &str, line: u32, column: u32) -> Result<u32, QuotedFunctionError> {
    if line == 0 || column == 0 {
        return Err(QuotedFunctionError::new("quoted span line/column must be 1-based"));
    }
    let mut current_line = 1_u32;
    let mut current_col = 1_u32;
    for (index, byte) in source.as_bytes().iter().copied().enumerate() {
        if current_line == line && current_col == column {
            return Ok(index as u32);
        }
        if byte == b'\n' {
            current_line += 1;
            current_col = 1;
        } else {
            current_col += 1;
        }
    }
    if current_line == line && current_col == column {
        return Ok(source.len() as u32);
    }
    Err(QuotedFunctionError::new(format!(
        "quoted span line {line} column {column} does not exist in source"
    )))
}

fn binop_from_name(name: &str) -> Option<BinOp> {
    Some(match name {
        "+" => BinOp::Add,
        "-" => BinOp::Sub,
        "*" => BinOp::Mul,
        "/" => BinOp::Div,
        "%" => BinOp::Rem,
        "==" => BinOp::Eq,
        "!=" => BinOp::Neq,
        "<" => BinOp::Lt,
        "<=" => BinOp::LtEq,
        ">" => BinOp::Gt,
        ">=" => BinOp::GtEq,
        "and" => BinOp::And,
        "or" => BinOp::Or,
        "|>" => BinOp::Pipe,
        "|" => BinOp::Cons,
        "++" => BinOp::ListConcat,
        "--" => BinOp::ListSubtract,
        "<>" => BinOp::BinConcat,
        ".." => BinOp::Range,
        "//" => BinOp::RangeStep,
        "in" => BinOp::In,
        "not in" => BinOp::NotIn,
        _ => return None,
    })
}
