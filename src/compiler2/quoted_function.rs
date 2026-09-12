use crate::ast::{
    AfterClause, Attribute, BinOp, BitField, BitFieldSpec, BitSize, BitType, CallableName, Endian, Expr, FnClause,
    LambdaClause, MatchClause, Pattern, Spanned, SpecDecl, TypeExprBody, UnOp, WithBinding,
};
use crate::function_surface::{FunctionSurface, NativeDeclaration};
use crate::modules::identity::ModuleName;
use crate::parser::lexer::{Tok, Token};
use crate::source::{SourceMap, Span};

use super::source::{QuotedAstNode, QuotedSourceCursor, QuotedSourceError, QuotedSourceRoot};
use super::token_payload;

type DecodedFnHead = (
    String,
    Vec<Spanned<Pattern>>,
    Vec<Option<TypeExprBody>>,
    Span,
    Option<Spanned<Expr>>,
);

type ExprPair = (Spanned<Expr>, Spanned<Expr>);

#[derive(Default)]
struct LambdaOccurrences(u32);

impl LambdaOccurrences {
    fn next(&mut self) -> crate::ast::LambdaOccurrence {
        let occurrence = crate::ast::LambdaOccurrence::from_u32(self.0);
        self.0 = self.0.checked_add(1).expect("source lambda occurrence space exhausted");
        occurrence
    }
}

pub(crate) fn derive_function_surface(
    root: &QuotedSourceRoot,
    sources: &SourceMap,
) -> Result<FunctionSurface, QuotedSourceError> {
    let occurrences = &mut LambdaOccurrences::default();
    let mut attrs = Vec::new();
    let mut attr_spans = Vec::new();
    let mut forms = Vec::new();
    for item in root.cursor().list_items()? {
        let node = expect_ast_node(&item, "grouped function item", sources)?;
        let head = atom_name(&node.head)?;
        if head.starts_with('@') {
            attr_spans.push(node.span.unwrap_or(Span::DUMMY));
            attrs.push(decode_attribute(&item, sources)?);
        } else {
            forms.push(item);
        }
    }

    if forms.is_empty() {
        return Err(QuotedSourceError::new("grouped quoted function source is empty"));
    }

    let first = expect_ast_node(&forms[0], "function form", sources)?;
    let form_head = atom_name(&first.head)?;
    if matches!(form_head.as_str(), "extern" | "intrinsic") {
        if forms.len() != 1 {
            return Err(QuotedSourceError::new(
                "grouped quoted extern source cannot contain multiple non-attribute forms",
            ));
        }
        return decode_native_fn(&first, attrs, &form_head, sources);
    }

    let is_macro = form_head == "defmacro";
    let mut clauses = Vec::new();
    let mut group_name: Option<String> = None;
    let mut name_span = Span::DUMMY;
    let mut group_span = Span::DUMMY;

    for form in forms {
        let node = expect_ast_node(&form, "function clause", sources)?;
        let head_name = atom_name(&node.head)?;
        if head_name != form_head {
            return Err(QuotedSourceError::new(format!(
                "grouped quoted function mixes `{form_head}` and `{head_name}`"
            )));
        }
        let (name, clause, clause_name_span) = decode_function_clause(occurrences, &node, sources)?;
        match &group_name {
            None => {
                group_name = Some(name);
                name_span = clause_name_span;
            }
            Some(current) if current == &name => {}
            Some(current) => {
                return Err(QuotedSourceError::new(format!(
                    "grouped quoted function mixes `{current}` and `{name}` clauses"
                )));
            }
        }
        group_span = group_span.merge(clause.span);
        clauses.push(clause);
    }

    for (attr, attr_span) in attrs.iter().zip(&attr_spans) {
        if let Attribute::Spec(spec) = attr {
            let expected_name = group_name.as_deref().unwrap_or_default();
            let expected_arity = clauses.first().map(|clause| clause.params.len()).unwrap_or_default();
            if spec.name != expected_name {
                return Err(QuotedSourceError::user(
                    crate::diag::codes::PARSE_SPEC_NAME_MISMATCH,
                    Some(*attr_span),
                    format!("@spec name `{}` doesn't match function `{expected_name}`", spec.name),
                ));
            }
            if spec.param_body_tokens.len() != expected_arity {
                return Err(QuotedSourceError::user(
                    crate::diag::codes::PARSE_SPEC_ARITY_MISMATCH,
                    Some(*attr_span),
                    format!(
                        "@spec arity {} doesn't match function `{expected_name}/{expected_arity}`",
                        spec.param_body_tokens.len()
                    ),
                ));
            }
        }
    }

    let name = group_name.expect("non-empty grouped function should establish a name");
    Ok(FunctionSurface {
        name,
        name_span,
        clauses,
        is_macro,
        declaration: None,
        native_param_tokens: Vec::new(),
        native_ret_tokens: TypeExprBody(Vec::new()),
        native_constraints: Vec::new(),
        variadic: false,
        attrs,
        span: group_span,
    })
}

fn decode_attribute(cursor: &QuotedSourceCursor, sources: &SourceMap) -> Result<Attribute, QuotedSourceError> {
    let node = expect_ast_node(cursor, "function attribute", sources)?;
    let head = atom_name(&node.head)?;
    let args = node.tail.list_items()?;
    let Some(value) = args.first() else {
        return Err(QuotedSourceError::new(format!(
            "quoted function attribute `{head}` is missing its payload"
        )));
    };
    match head.as_str() {
        "@doc" => Ok(Attribute::Doc(value.utf8_binary_text()?)),
        "@spec" => decode_spec_attribute(value, sources),
        other => Err(QuotedSourceError::new(format!(
            "unsupported quoted function attribute `{other}`"
        ))),
    }
}

fn decode_native_fn(
    node: &QuotedAstNode,
    attrs: Vec<Attribute>,
    form: &str,
    sources: &SourceMap,
) -> Result<FunctionSurface, QuotedSourceError> {
    let args = node.tail.list_items()?;
    if args.len() != 2 {
        return Err(QuotedSourceError::new("quoted extern expects ABI and detail map"));
    }
    let abi = args[0].utf8_binary_text()?;
    let details = &args[1];
    let name = required_map_utf8(details, "name")?;
    let params = required_map_list_tokens(details, "params", sources)?;
    let ret = required_map_tokens(details, "return", sources)?;
    let variadic = required_map_bool(details, "variadic")?;
    let constraints = optional_map_keyword_tokens(details, "when", sources)?;
    let span = node.span.unwrap_or(Span::DUMMY);

    let native_param_tokens = params
        .into_iter()
        .map(strip_extern_param_name)
        .map(|result| result.map(TypeExprBody))
        .collect::<Result<Vec<_>, _>>()?;
    let native_ret_tokens = TypeExprBody(ret);
    let native_constraints = constraints
        .into_iter()
        .map(|(name, body)| Ok((name, TypeExprBody(body))))
        .collect::<Result<Vec<_>, QuotedSourceError>>()?;

    Ok(FunctionSurface {
        name,
        name_span: span,
        clauses: Vec::new(),
        is_macro: false,
        declaration: Some(if form == "intrinsic" {
            NativeDeclaration::Intrinsic(abi)
        } else {
            NativeDeclaration::Extern(abi)
        }),
        native_param_tokens,
        native_ret_tokens,
        native_constraints,
        variadic,
        attrs,
        span,
    })
}

fn decode_function_clause(
    occurrences: &mut LambdaOccurrences,
    node: &QuotedAstNode,
    sources: &SourceMap,
) -> Result<(String, FnClause, Span), QuotedSourceError> {
    let span = node.span.unwrap_or(Span::DUMMY);
    let args = node.tail.list_items()?;
    if args.len() != 2 {
        return Err(QuotedSourceError::new(
            "quoted function clause expects head and do-body",
        ));
    }
    let (name, params, param_annotations, name_span, guard) = decode_function_head(occurrences, &args[0], sources)?;
    let body = decode_do_body(occurrences, &args[1], Some(span), sources)?;
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
    occurrences: &mut LambdaOccurrences,
    cursor: &QuotedSourceCursor,
    sources: &SourceMap,
) -> Result<DecodedFnHead, QuotedSourceError> {
    let node = expect_ast_node(cursor, "function head", sources)?;
    let span = node.span.unwrap_or(Span::DUMMY);
    if atom_name(&node.head)? == "when" {
        let parts = node.tail.list_items()?;
        if parts.len() != 2 {
            return Err(QuotedSourceError::new(
                "quoted `when` function head expects head and guard",
            ));
        }
        let (name, params, annotations, name_span, _) = decode_function_head(occurrences, &parts[0], sources)?;
        let guard = decode_expr(occurrences, &parts[1], Some(span), sources)?;
        return Ok((name, params, annotations, name_span, Some(guard)));
    }

    let name = atom_name(&node.head)?;
    let mut params = Vec::new();
    let mut annotations = Vec::new();
    for arg in node.tail.list_items()? {
        if let Some(ascribe) = arg.ast_node(sources)?
            && atom_name(&ascribe.head)? == "::"
        {
            let parts = ascribe.tail.list_items()?;
            if parts.len() != 2 {
                return Err(QuotedSourceError::new("quoted `::` parameter expects lhs and rhs"));
            }
            params.push(decode_pattern(&parts[0], Some(span), sources)?);
            annotations.push(Some(quoted_type_expr_body(&parts[1], sources)?));
            continue;
        }
        params.push(decode_pattern(&arg, Some(span), sources)?);
        annotations.push(None);
    }
    Ok((name, params, annotations, span, None))
}

fn decode_do_body(
    occurrences: &mut LambdaOccurrences,
    cursor: &QuotedSourceCursor,
    fallback_span: Option<Span>,
    sources: &SourceMap,
) -> Result<Spanned<Expr>, QuotedSourceError> {
    let entries = decode_keyword_entries(cursor)?;
    let Some((_, body)) = entries.into_iter().find(|(key, _)| key == "do") else {
        return Err(QuotedSourceError::new(
            "quoted function clause is missing its `do` body",
        ));
    };
    decode_expr(occurrences, &body, fallback_span, sources)
}

fn decode_expr(
    occurrences: &mut LambdaOccurrences,
    cursor: &QuotedSourceCursor,
    fallback_span: Option<Span>,
    sources: &SourceMap,
) -> Result<Spanned<Expr>, QuotedSourceError> {
    if let Some(node) = cursor.ast_node(sources)? {
        let span = node.span.unwrap_or(Span::DUMMY);
        if let Some(module) = node.meta.module_denotation()? {
            return Ok(Spanned::new(Expr::Module(module), span));
        }
        if !is_list_like(&node.tail) {
            return Ok(Spanned::new(Expr::Var(atom_name(&node.head)?), span));
        }

        let args = node.tail.list_items()?;
        if node.head.root().tag() != fz_runtime::any_value::ValueKind::ATOM {
            if let Some(head_node) = node.head.ast_node(sources)?
                && atom_name(&head_node.head)? == "."
            {
                let callee_parts = head_node.tail.list_items()?;
                if callee_parts.len() == 1 {
                    let callee = decode_expr(occurrences, &callee_parts[0], Some(span), sources)?;
                    let call_args = decode_exprs(occurrences, &args, Some(span), sources)?;
                    return Ok(Spanned::new(Expr::ClosureCall(Box::new(callee), call_args), span));
                }
                if callee_parts.len() == 2 && is_bracket_access_callee(&head_node)? && args.len() == 2 {
                    let base = decode_expr(occurrences, &args[0], Some(span), sources)?;
                    let key = decode_expr(occurrences, &args[1], Some(span), sources)?;
                    return Ok(Spanned::new(Expr::Index(Box::new(base), Box::new(key)), span));
                }
            }
            let callee = decode_expr(occurrences, &node.head, Some(span), sources)?;
            let call_args = decode_exprs(occurrences, &args, Some(span), sources)?;
            return Ok(Spanned::new(Expr::Call(Box::new(callee), call_args), span));
        }

        return decode_named_expr(occurrences, atom_name(&node.head)?, &args, span, sources);
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
        fz_runtime::any_value::ValueKind::LIST => decode_list_expr(occurrences, cursor, span, sources),
        fz_runtime::any_value::ValueKind::STRUCT => {
            let items = cursor.tuple_items()?;
            let elems = decode_exprs(occurrences, &items, Some(span), sources)?;
            Ok(Spanned::new(Expr::Tuple(elems), span))
        }
        fz_runtime::any_value::ValueKind::MAP => {
            let entries = cursor
                .map_entries()?
                .iter()
                .map(|(key, value)| {
                    Ok((
                        decode_expr(occurrences, key, Some(span), sources)?,
                        decode_expr(occurrences, value, Some(span), sources)?,
                    ))
                })
                .collect::<Result<Vec<_>, QuotedSourceError>>()?;
            Ok(Spanned::new(Expr::Map(entries), span))
        }
        other => Err(QuotedSourceError::new(format!(
            "unsupported quoted expression runtime kind {:?}",
            other
        ))),
    }
}

fn decode_named_expr(
    occurrences: &mut LambdaOccurrences,
    name: String,
    args: &[QuotedSourceCursor],
    span: Span,
    sources: &SourceMap,
) -> Result<Spanned<Expr>, QuotedSourceError> {
    if name == "%" && args.len() == 2 && is_alias(&args[0], sources)? {
        return decode_struct_expr(occurrences, args, span, sources);
    }
    if let Some(op) = binop_from_name(&name)
        && args.len() == 2
    {
        let left = decode_expr(occurrences, &args[0], Some(span), sources)?;
        let right = decode_expr(occurrences, &args[1], Some(span), sources)?;
        return Ok(Spanned::new(Expr::BinOp(op, Box::new(left), Box::new(right)), span));
    }
    match (name.as_str(), args.len()) {
        ("-", 1) => {
            let inner = decode_expr(occurrences, &args[0], Some(span), sources)?;
            // A negative LITERAL is a literal, exactly as in patterns
            // (`decode_negative_pattern`). Folding it keeps `-3` a constant
            // instead of a call to `Kernel.negate/1`, which is what
            // `source_sugar` rewrites every other unary minus into.
            match inner.node {
                Expr::Int(value) => Ok(Spanned::new(Expr::Int(-value), span)),
                Expr::Float(value) => Ok(Spanned::new(Expr::Float(-value), span)),
                _ => Ok(Spanned::new(Expr::UnOp(UnOp::Neg, Box::new(inner)), span)),
            }
        }
        ("not", 1) => {
            let inner = decode_expr(occurrences, &args[0], Some(span), sources)?;
            Ok(Spanned::new(Expr::UnOp(UnOp::Not, Box::new(inner)), span))
        }
        ("=", 2) => {
            let lhs = decode_pattern(&args[0], Some(span), sources)?;
            let rhs = decode_expr(occurrences, &args[1], Some(span), sources)?;
            Ok(Spanned::new(Expr::Match(lhs, Box::new(rhs)), span))
        }
        ("::", 2) => {
            let value = decode_expr(occurrences, &args[0], Some(span), sources)?;
            let ty = quoted_type_expr_body(&args[1], sources)?;
            Ok(Spanned::new(Expr::Ascribe(Box::new(value), ty), span))
        }
        ("__aliases__", _) => Ok(Spanned::new(Expr::Var(alias_name_from_args(args)?), span)),
        (".", 2) => {
            let base = decode_expr(occurrences, &args[0], Some(span), sources)?;
            let field = Spanned::new(Expr::Atom(args[1].atom_name()?), span);
            Ok(Spanned::new(Expr::Index(Box::new(base), Box::new(field)), span))
        }
        ("__block__", _) => Ok(Spanned::new(
            Expr::Block(decode_exprs(occurrences, args, Some(span), sources)?),
            span,
        )),
        ("if", 2) => decode_if(occurrences, args, span, sources),
        ("case", 1 | 2) => decode_case(occurrences, args, span, sources),
        ("cond", 1) => decode_cond(occurrences, args, span, sources),
        ("with", _) => decode_with(occurrences, args, span, sources),
        ("receive", 1) => decode_receive(occurrences, args, span, sources),
        ("fn", _) => decode_lambda(occurrences, args, span, sources),
        ("quote", 1) => decode_quote(occurrences, args, span, sources),
        ("unquote", 1) => {
            let inner = decode_expr(occurrences, &args[0], Some(span), sources)?;
            Ok(Spanned::new(Expr::Unquote(Box::new(inner)), span))
        }
        ("{}", _) => Ok(Spanned::new(
            Expr::Tuple(decode_exprs(occurrences, args, Some(span), sources)?),
            span,
        )),
        ("%{}", _) => decode_map_expr(occurrences, args, span, sources),
        ("<<>>", _) => decode_bitstring_expr(occurrences, args, span, sources),
        ("&", 1) => decode_fn_ref_expr(&args[0], span, sources),
        _ => {
            let callee = Spanned::new(Expr::Var(name), span);
            let call_args = decode_exprs(occurrences, args, Some(span), sources)?;
            Ok(Spanned::new(Expr::Call(Box::new(callee), call_args), span))
        }
    }
}

fn decode_pattern(
    cursor: &QuotedSourceCursor,
    fallback_span: Option<Span>,
    sources: &SourceMap,
) -> Result<Spanned<Pattern>, QuotedSourceError> {
    if let Some(node) = cursor.ast_node(sources)? {
        let span = node.span.unwrap_or(Span::DUMMY);
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
                let Some(name) = pattern_var_name(&args[0], Some(span), sources)? else {
                    return Err(QuotedSourceError::new("pattern as-bind lhs must be a variable"));
                };
                let inner = decode_pattern(&args[1], Some(span), sources)?;
                Ok(Spanned::new(Pattern::As(name, Box::new(inner)), span))
            }
            "^" => {
                let Some(name) = pattern_var_name(&args[0], Some(span), sources)? else {
                    return Err(QuotedSourceError::new("pinned pattern expects a variable"));
                };
                Ok(Spanned::new(Pattern::Pinned(name), span))
            }
            "%{}" => decode_map_pattern(&args, span, sources),
            "%" if is_alias(&args[0], sources)? => decode_struct_pattern(&args, span, sources),
            "{}" => Ok(Spanned::new(
                Pattern::Tuple(
                    args.iter()
                        .map(|arg| decode_pattern(arg, Some(span), sources))
                        .collect::<Result<Vec<_>, _>>()?,
                ),
                span,
            )),
            "<<>>" => decode_bitstring_pattern(&args, span, sources),
            "-" if args.len() == 1 => decode_negative_pattern(&args[0], span, sources),
            "__aliases__" => Err(QuotedSourceError::new("module aliases are not valid patterns")),
            other => Err(QuotedSourceError::new(format!(
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
        fz_runtime::any_value::ValueKind::LIST => decode_list_pattern(cursor, span, sources),
        fz_runtime::any_value::ValueKind::STRUCT => {
            let items = cursor.tuple_items()?;
            let elems = items
                .into_iter()
                .map(|item| decode_pattern(&item, Some(span), sources))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Spanned::new(Pattern::Tuple(elems), span))
        }
        other => Err(QuotedSourceError::new(format!(
            "unsupported quoted pattern runtime kind {:?}",
            other
        ))),
    }
}

fn decode_if(
    occurrences: &mut LambdaOccurrences,
    args: &[QuotedSourceCursor],
    span: Span,
    sources: &SourceMap,
) -> Result<Spanned<Expr>, QuotedSourceError> {
    let cond = decode_expr(occurrences, &args[0], Some(span), sources)?;
    let entries = decode_keyword_entries(&args[1])?;
    let mut then_branch = None;
    let mut else_branch = None;
    for (key, value) in entries {
        match key.as_str() {
            "do" => then_branch = Some(decode_expr(occurrences, &value, Some(span), sources)?),
            "else" => else_branch = Some(decode_expr(occurrences, &value, Some(span), sources)?),
            other => {
                return Err(QuotedSourceError::new(format!(
                    "unsupported quoted `if` keyword `{other}`"
                )));
            }
        }
    }
    Ok(Spanned::new(
        Expr::If(
            Box::new(cond),
            Box::new(then_branch.ok_or_else(|| QuotedSourceError::new("quoted `if` is missing `do`"))?),
            else_branch.map(Box::new),
        ),
        span,
    ))
}

fn decode_case(
    occurrences: &mut LambdaOccurrences,
    args: &[QuotedSourceCursor],
    span: Span,
    sources: &SourceMap,
) -> Result<Spanned<Expr>, QuotedSourceError> {
    let (subject, kw_cursor) = match args {
        [kw] => (None, kw),
        [subject, kw] => (Some(decode_expr(occurrences, subject, Some(span), sources)?), kw),
        _ => {
            return Err(QuotedSourceError::new("quoted `case` expects a subject and `do` body"));
        }
    };
    let entries = decode_keyword_entries(kw_cursor)?;
    let Some((_, body)) = entries.into_iter().find(|(key, _)| key == "do") else {
        return Err(QuotedSourceError::new("quoted `case` is missing `do` clauses"));
    };
    let clauses = body
        .list_items()?
        .into_iter()
        .map(|clause| decode_match_clause(occurrences, &clause, sources))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Spanned::new(Expr::Case(subject.map(Box::new), clauses), span))
}

fn decode_cond(
    occurrences: &mut LambdaOccurrences,
    args: &[QuotedSourceCursor],
    span: Span,
    sources: &SourceMap,
) -> Result<Spanned<Expr>, QuotedSourceError> {
    let entries = decode_keyword_entries(&args[0])?;
    let Some((_, body)) = entries.into_iter().find(|(key, _)| key == "do") else {
        return Err(QuotedSourceError::new("quoted `cond` is missing `do` clauses"));
    };
    let mut clauses = Vec::new();
    for clause in body.list_items()? {
        let node = expect_ast_node(&clause, "cond clause", sources)?;
        if atom_name(&node.head)? != "->" {
            return Err(QuotedSourceError::new("quoted `cond` body expects `->` clauses"));
        }
        let parts = node.tail.list_items()?;
        if parts.len() != 2 {
            return Err(QuotedSourceError::new(
                "quoted `cond` clause expects test list and body",
            ));
        }
        let tests = parts[0].list_items()?;
        if tests.len() != 1 {
            return Err(QuotedSourceError::new("quoted `cond` clause expects one test"));
        }
        clauses.push((
            decode_expr(occurrences, &tests[0], Some(span), sources)?,
            decode_expr(occurrences, &parts[1], Some(span), sources)?,
        ));
    }
    Ok(Spanned::new(Expr::Cond(clauses), span))
}

fn decode_with(
    occurrences: &mut LambdaOccurrences,
    args: &[QuotedSourceCursor],
    span: Span,
    sources: &SourceMap,
) -> Result<Spanned<Expr>, QuotedSourceError> {
    let Some((kw_cursor, binding_args)) = args.split_last() else {
        return Err(QuotedSourceError::new("quoted `with` expects bindings and a body"));
    };
    let entries = decode_keyword_entries(kw_cursor)?;
    let mut body = None;
    let mut else_clauses = Vec::new();
    for (key, value) in entries {
        match key.as_str() {
            "do" => body = Some(decode_expr(occurrences, &value, Some(span), sources)?),
            "else" => {
                else_clauses = value
                    .list_items()?
                    .into_iter()
                    .map(|clause| decode_match_clause(occurrences, &clause, sources))
                    .collect::<Result<Vec<_>, _>>()?;
            }
            other => {
                return Err(QuotedSourceError::new(format!(
                    "unsupported quoted `with` keyword `{other}`"
                )));
            }
        }
    }

    let mut bindings = Vec::new();
    for binding in binding_args {
        if let Some(node) = binding.ast_node(sources)?
            && atom_name(&node.head)? == "<-"
        {
            let parts = node.tail.list_items()?;
            if parts.len() != 2 {
                return Err(QuotedSourceError::new(
                    "quoted `with` match binding expects pattern and expression",
                ));
            }
            bindings.push(WithBinding::Match(
                decode_pattern(&parts[0], Some(span), sources)?,
                decode_expr(occurrences, &parts[1], Some(span), sources)?,
            ));
            continue;
        }
        bindings.push(WithBinding::Bare(decode_expr(
            occurrences,
            binding,
            Some(span),
            sources,
        )?));
    }

    Ok(Spanned::new(
        Expr::With(
            bindings,
            Box::new(body.ok_or_else(|| QuotedSourceError::new("quoted `with` is missing `do`"))?),
            else_clauses,
        ),
        span,
    ))
}

fn decode_receive(
    occurrences: &mut LambdaOccurrences,
    args: &[QuotedSourceCursor],
    span: Span,
    sources: &SourceMap,
) -> Result<Spanned<Expr>, QuotedSourceError> {
    let entries = decode_keyword_entries(&args[0])?;
    let mut clauses = Vec::new();
    let mut after = None;
    for (key, value) in entries {
        match key.as_str() {
            "do" => {
                clauses = value
                    .list_items()?
                    .into_iter()
                    .map(|clause| decode_match_clause(occurrences, &clause, sources))
                    .collect::<Result<Vec<_>, _>>()?;
            }
            "after" => {
                let after_items = value.list_items()?;
                let Some(clause) = after_items.first() else {
                    return Err(QuotedSourceError::new("quoted `receive after` is empty"));
                };
                after = Some(Box::new(decode_after_clause(occurrences, clause, sources)?));
            }
            other => {
                return Err(QuotedSourceError::new(format!(
                    "unsupported quoted `receive` keyword `{other}`"
                )));
            }
        }
    }
    Ok(Spanned::new(Expr::Receive { clauses, after }, span))
}

fn decode_lambda(
    occurrences: &mut LambdaOccurrences,
    args: &[QuotedSourceCursor],
    span: Span,
    sources: &SourceMap,
) -> Result<Spanned<Expr>, QuotedSourceError> {
    let occurrence = occurrences.next();
    let clauses = args
        .iter()
        .map(|clause| decode_lambda_clause(occurrences, clause, sources))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Spanned::new(Expr::Lambda { occurrence, clauses }, span))
}

fn decode_quote(
    occurrences: &mut LambdaOccurrences,
    args: &[QuotedSourceCursor],
    span: Span,
    sources: &SourceMap,
) -> Result<Spanned<Expr>, QuotedSourceError> {
    let entries = decode_keyword_entries(&args[0])?;
    let Some((_, body)) = entries.into_iter().find(|(key, _)| key == "do") else {
        return Err(QuotedSourceError::new("quoted `quote` is missing `do` body"));
    };
    Ok(Spanned::new(
        Expr::Quote(Box::new(decode_expr(occurrences, &body, Some(span), sources)?)),
        span,
    ))
}

fn decode_map_expr(
    occurrences: &mut LambdaOccurrences,
    args: &[QuotedSourceCursor],
    span: Span,
    sources: &SourceMap,
) -> Result<Spanned<Expr>, QuotedSourceError> {
    if args.len() == 1
        && let Some(node) = args[0].ast_node(sources)?
        && atom_name(&node.head)? == "|"
    {
        let parts = node.tail.list_items()?;
        if parts.len() != 2 {
            return Err(QuotedSourceError::new(
                "quoted map update expects base and keyword list",
            ));
        }
        let base = decode_expr(occurrences, &parts[0], Some(span), sources)?;
        let entries = decode_expr_keyword_pairs(occurrences, &parts[1], Some(span), sources)?;
        return Ok(Spanned::new(Expr::MapUpdate(Box::new(base), entries), span));
    }

    let entries = args
        .iter()
        .map(|entry| decode_expr_pair(occurrences, entry, Some(span), sources))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Spanned::new(Expr::Map(entries), span))
}

fn decode_struct_expr(
    occurrences: &mut LambdaOccurrences,
    args: &[QuotedSourceCursor],
    span: Span,
    sources: &SourceMap,
) -> Result<Spanned<Expr>, QuotedSourceError> {
    let module = decode_module_target(&args[0], sources)?;
    let map = expect_ast_node(&args[1], "struct map payload", sources)?;
    if atom_name(&map.head)? != "%{}" {
        return Err(QuotedSourceError::new("quoted struct payload must be a `%{}` node"));
    }
    let mut fields = Vec::new();
    for entry in map.tail.list_items()? {
        let (key, value) = decode_expr_pair(occurrences, &entry, Some(span), sources)?;
        let Expr::Atom(field) = key.node else {
            return Err(QuotedSourceError::new("quoted struct keys must be atoms"));
        };
        fields.push((field, value));
    }
    Ok(Spanned::new(Expr::Struct { module, fields }, span))
}

fn decode_bitstring_expr(
    occurrences: &mut LambdaOccurrences,
    args: &[QuotedSourceCursor],
    span: Span,
    sources: &SourceMap,
) -> Result<Spanned<Expr>, QuotedSourceError> {
    let mut fields = Vec::new();
    for field in args {
        if let Some(node) = field.ast_node(sources)?
            && atom_name(&node.head)? == "::"
        {
            let parts = node.tail.list_items()?;
            if parts.len() != 2 {
                return Err(QuotedSourceError::new("quoted bitstring field expects value and spec"));
            }
            let field_span = node.span.unwrap_or(Span::DUMMY);
            fields.push(BitField {
                value: decode_expr(occurrences, &parts[0], Some(span), sources)?,
                spec: decode_bit_spec(&parts[1], field_span, sources)?,
            });
            continue;
        }
        let value = decode_expr(occurrences, field, Some(span), sources)?;
        let spec = match &value.node {
            Expr::Binary(bytes) => binary_literal_bit_spec(BitFieldSpec::default(), bytes.len(), false),
            _ => BitFieldSpec::default(),
        };
        fields.push(BitField { value, spec });
    }
    Ok(Spanned::new(Expr::Bitstring(fields), span))
}

fn decode_fn_ref_expr(
    cursor: &QuotedSourceCursor,
    span: Span,
    sources: &SourceMap,
) -> Result<Spanned<Expr>, QuotedSourceError> {
    let node = expect_ast_node(cursor, "function reference payload", sources)?;
    if atom_name(&node.head)? != "/" {
        return Err(QuotedSourceError::new("quoted `&` expects a `/` target"));
    }
    let parts = node.tail.list_items()?;
    if parts.len() != 2 {
        return Err(QuotedSourceError::new(
            "quoted function reference expects target and arity",
        ));
    }
    let target = decode_expr(&mut LambdaOccurrences::default(), &parts[0], Some(span), sources)?;
    let name = CallableName::from_expr(&target.node)
        .ok_or_else(|| QuotedSourceError::new("unsupported quoted function-ref target"))?;
    let arity = parts[1].int_value()? as usize;
    Ok(Spanned::new(Expr::FnRef { name, arity }, span))
}

fn decode_match_clause(
    occurrences: &mut LambdaOccurrences,
    cursor: &QuotedSourceCursor,
    sources: &SourceMap,
) -> Result<MatchClause, QuotedSourceError> {
    let node = expect_ast_node(cursor, "match clause", sources)?;
    let span = node.span.unwrap_or(Span::DUMMY);
    if atom_name(&node.head)? != "->" {
        return Err(QuotedSourceError::new("quoted clause expects a `->` head"));
    }
    let parts = node.tail.list_items()?;
    if parts.len() != 2 {
        return Err(QuotedSourceError::new("quoted clause expects pattern list and body"));
    }
    let patterns = parts[0].list_items()?;
    if patterns.len() != 1 {
        return Err(QuotedSourceError::new("quoted match clause expects one pattern"));
    }
    let (pattern, guard) = if let Some(when) = patterns[0].ast_node(sources)?
        && atom_name(&when.head)? == "when"
    {
        let args = when.tail.list_items()?;
        if args.len() != 2 {
            return Err(QuotedSourceError::new(
                "quoted guarded clause expects pattern and guard",
            ));
        }
        (
            decode_pattern(&args[0], Some(span), sources)?,
            Some(decode_expr(occurrences, &args[1], Some(span), sources)?),
        )
    } else {
        (decode_pattern(&patterns[0], Some(span), sources)?, None)
    };
    Ok(MatchClause {
        pattern,
        guard,
        body: decode_expr(occurrences, &parts[1], Some(span), sources)?,
        span,
    })
}

fn decode_after_clause(
    occurrences: &mut LambdaOccurrences,
    cursor: &QuotedSourceCursor,
    sources: &SourceMap,
) -> Result<AfterClause, QuotedSourceError> {
    let node = expect_ast_node(cursor, "after clause", sources)?;
    let span = node.span.unwrap_or(Span::DUMMY);
    if atom_name(&node.head)? != "->" {
        return Err(QuotedSourceError::new("quoted `after` clause expects `->`"));
    }
    let parts = node.tail.list_items()?;
    if parts.len() != 2 {
        return Err(QuotedSourceError::new("quoted `after` clause expects timeout and body"));
    }
    let patterns = parts[0].list_items()?;
    if patterns.len() != 1 {
        return Err(QuotedSourceError::new(
            "quoted `after` clause expects one timeout expression",
        ));
    }
    Ok(AfterClause {
        timeout: decode_expr(occurrences, &patterns[0], Some(span), sources)?,
        body: decode_expr(occurrences, &parts[1], Some(span), sources)?,
        span,
    })
}

fn decode_lambda_clause(
    occurrences: &mut LambdaOccurrences,
    cursor: &QuotedSourceCursor,
    sources: &SourceMap,
) -> Result<LambdaClause, QuotedSourceError> {
    let node = expect_ast_node(cursor, "lambda clause", sources)?;
    let span = node.span.unwrap_or(Span::DUMMY);
    if atom_name(&node.head)? != "->" {
        return Err(QuotedSourceError::new("quoted lambda clause expects `->`"));
    }
    let parts = node.tail.list_items()?;
    if parts.len() != 2 {
        return Err(QuotedSourceError::new("quoted lambda clause expects params and body"));
    }
    let params_root = parts[0].list_items()?;
    let (params, guard) = if params_root.len() == 1 {
        if let Some(when) = params_root[0].ast_node(sources)?
            && atom_name(&when.head)? == "when"
        {
            let args = when.tail.list_items()?;
            let Some((guard_cursor, param_cursors)) = args.split_last() else {
                return Err(QuotedSourceError::new("quoted guarded lambda clause is empty"));
            };
            let params = param_cursors
                .iter()
                .map(|param| decode_pattern(param, Some(span), sources))
                .collect::<Result<Vec<_>, _>>()?;
            let guard = decode_expr(occurrences, guard_cursor, Some(span), sources)?;
            (params, Some(guard))
        } else {
            (
                params_root
                    .iter()
                    .map(|param| decode_pattern(param, Some(span), sources))
                    .collect::<Result<Vec<_>, _>>()?,
                None,
            )
        }
    } else {
        (
            params_root
                .iter()
                .map(|param| decode_pattern(param, Some(span), sources))
                .collect::<Result<Vec<_>, _>>()?,
            None,
        )
    };
    Ok(LambdaClause {
        params,
        guard,
        body: decode_expr(occurrences, &parts[1], Some(span), sources)?,
        span,
    })
}

fn decode_map_pattern(
    args: &[QuotedSourceCursor],
    span: Span,
    sources: &SourceMap,
) -> Result<Spanned<Pattern>, QuotedSourceError> {
    let entries = args
        .iter()
        .map(|entry| decode_pattern_pair(entry, Some(span), sources))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Spanned::new(Pattern::Map(entries), span))
}

fn decode_struct_pattern(
    args: &[QuotedSourceCursor],
    span: Span,
    sources: &SourceMap,
) -> Result<Spanned<Pattern>, QuotedSourceError> {
    let module = decode_module_target(&args[0], sources)?;
    let map = expect_ast_node(&args[1], "struct pattern payload", sources)?;
    if atom_name(&map.head)? != "%{}" {
        return Err(QuotedSourceError::new("quoted struct pattern payload must be `%{}`"));
    }
    let mut fields = Vec::new();
    for entry in map.tail.list_items()? {
        let (key, value) = decode_pattern_pair(&entry, Some(span), sources)?;
        let Pattern::Atom(field) = key.node else {
            return Err(QuotedSourceError::new("quoted struct pattern keys must be atoms"));
        };
        fields.push((field, value));
    }
    Ok(Spanned::new(Pattern::Struct { module, fields }, span))
}

/// A STRING LITERAL segment is a binary, not the integer field default.
///
/// Quoted source represents an unsuffixed string field as the raw binary value,
/// with no `:: binary` node to carry its type. This is the one place that turns
/// that source shape into the binary field spec used by both construction and
/// matching.
///
/// A construction consumes the whole source binary when size is absent. A
/// pattern may put another field after the literal, so it needs the literal's
/// byte length made explicit. An authored size remains authoritative.
fn binary_literal_bit_spec(mut spec: BitFieldSpec, byte_len: usize, size_when_missing: bool) -> BitFieldSpec {
    if spec.size.is_some() {
        return spec;
    }
    spec.ty = BitType::Binary;
    if size_when_missing {
        // BYTES, not bits: a `binary` segment's size is in units of 8, which is
        // what `binary-size(1)` means for one byte.
        spec.size = Some(BitSize::Literal(byte_len as u32));
    }
    spec
}

fn sized_for_binary_literal(value: &Pattern, spec: BitFieldSpec) -> BitFieldSpec {
    let Pattern::Binary(bytes) = value else {
        return spec;
    };
    binary_literal_bit_spec(spec, bytes.len(), true)
}

fn decode_bitstring_pattern(
    args: &[QuotedSourceCursor],
    span: Span,
    sources: &SourceMap,
) -> Result<Spanned<Pattern>, QuotedSourceError> {
    let mut fields = Vec::new();
    for field in args {
        if let Some(node) = field.ast_node(sources)?
            && atom_name(&node.head)? == "::"
        {
            let parts = node.tail.list_items()?;
            if parts.len() != 2 {
                return Err(QuotedSourceError::new(
                    "quoted bitstring pattern field expects value and spec",
                ));
            }
            let field_span = node.span.unwrap_or(Span::DUMMY);
            let value = decode_pattern(&parts[0], Some(span), sources)?;
            let spec = sized_for_binary_literal(&value.node, decode_bit_spec(&parts[1], field_span, sources)?);
            fields.push(BitField { value, spec });
            continue;
        }
        let value = decode_pattern(field, Some(span), sources)?;
        let spec = sized_for_binary_literal(&value.node, BitFieldSpec::default());
        fields.push(BitField { value, spec });
    }
    Ok(Spanned::new(Pattern::Bitstring(fields), span))
}

fn decode_negative_pattern(
    cursor: &QuotedSourceCursor,
    span: Span,
    sources: &SourceMap,
) -> Result<Spanned<Pattern>, QuotedSourceError> {
    let decoded = decode_pattern(cursor, Some(span), sources)?;
    match decoded.node {
        Pattern::Int(value) => Ok(Spanned::new(Pattern::Int(-value), span)),
        Pattern::Float(value) => Ok(Spanned::new(Pattern::Float(-value), span)),
        other => Err(QuotedSourceError::new(format!(
            "quoted negative pattern expects a number, got {:?}",
            other
        ))),
    }
}

fn decode_list_expr(
    occurrences: &mut LambdaOccurrences,
    cursor: &QuotedSourceCursor,
    span: Span,
    sources: &SourceMap,
) -> Result<Spanned<Expr>, QuotedSourceError> {
    let items = cursor.list_items()?;
    let (items, tail) = split_improper_list(occurrences, items, span, sources)?;
    Ok(Spanned::new(
        Expr::List(
            decode_exprs(occurrences, &items, Some(span), sources)?,
            tail.map(Box::new),
        ),
        span,
    ))
}

fn decode_list_pattern(
    cursor: &QuotedSourceCursor,
    span: Span,
    sources: &SourceMap,
) -> Result<Spanned<Pattern>, QuotedSourceError> {
    let items = cursor.list_items()?;
    let (items, tail) = split_improper_pattern_list(items, span, sources)?;
    Ok(Spanned::new(
        Pattern::List(
            items
                .iter()
                .map(|item| decode_pattern(item, Some(span), sources))
                .collect::<Result<Vec<_>, _>>()?,
            tail.map(Box::new),
        ),
        span,
    ))
}

fn split_improper_list(
    occurrences: &mut LambdaOccurrences,
    items: Vec<QuotedSourceCursor>,
    span: Span,
    sources: &SourceMap,
) -> Result<(Vec<QuotedSourceCursor>, Option<Spanned<Expr>>), QuotedSourceError> {
    let Some((last, prefix)) = items.split_last() else {
        return Ok((Vec::new(), None));
    };
    if let Some(node) = last.ast_node(sources)?
        && node_head_is_atom_named(&node, "|")?
    {
        let parts = node.tail.list_items()?;
        if parts.len() != 2 {
            return Err(QuotedSourceError::new(
                "quoted improper list marker expects head and tail",
            ));
        }
        let mut heads = prefix.to_vec();
        heads.push(parts[0].clone());
        return Ok((heads, Some(decode_expr(occurrences, &parts[1], Some(span), sources)?)));
    }
    Ok((items, None))
}

fn split_improper_pattern_list(
    items: Vec<QuotedSourceCursor>,
    span: Span,
    sources: &SourceMap,
) -> Result<(Vec<QuotedSourceCursor>, Option<Spanned<Pattern>>), QuotedSourceError> {
    let Some((last, prefix)) = items.split_last() else {
        return Ok((Vec::new(), None));
    };
    if let Some(node) = last.ast_node(sources)?
        && node_head_is_atom_named(&node, "|")?
    {
        let parts = node.tail.list_items()?;
        if parts.len() != 2 {
            return Err(QuotedSourceError::new(
                "quoted improper pattern list marker expects head and tail",
            ));
        }
        let mut heads = prefix.to_vec();
        heads.push(parts[0].clone());
        return Ok((heads, Some(decode_pattern(&parts[1], Some(span), sources)?)));
    }
    Ok((items, None))
}

fn decode_exprs(
    occurrences: &mut LambdaOccurrences,
    args: &[QuotedSourceCursor],
    fallback_span: Option<Span>,
    sources: &SourceMap,
) -> Result<Vec<Spanned<Expr>>, QuotedSourceError> {
    args.iter()
        .map(|arg| decode_expr(occurrences, arg, fallback_span, sources))
        .collect::<Result<Vec<_>, _>>()
}

fn decode_expr_pair(
    occurrences: &mut LambdaOccurrences,
    cursor: &QuotedSourceCursor,
    fallback_span: Option<Span>,
    sources: &SourceMap,
) -> Result<(Spanned<Expr>, Spanned<Expr>), QuotedSourceError> {
    let items = cursor.tuple_items()?;
    if items.len() != 2 {
        return Err(QuotedSourceError::new("quoted pair expects a 2-tuple"));
    }
    Ok((
        decode_expr(occurrences, &items[0], fallback_span, sources)?,
        decode_expr(occurrences, &items[1], fallback_span, sources)?,
    ))
}

fn decode_pattern_pair(
    cursor: &QuotedSourceCursor,
    fallback_span: Option<Span>,
    sources: &SourceMap,
) -> Result<(Spanned<Pattern>, Spanned<Pattern>), QuotedSourceError> {
    let items = cursor.tuple_items()?;
    if items.len() != 2 {
        return Err(QuotedSourceError::new("quoted pair expects a 2-tuple"));
    }
    Ok((
        decode_pattern(&items[0], fallback_span, sources)?,
        decode_pattern(&items[1], fallback_span, sources)?,
    ))
}

fn decode_expr_keyword_pairs(
    occurrences: &mut LambdaOccurrences,
    cursor: &QuotedSourceCursor,
    fallback_span: Option<Span>,
    sources: &SourceMap,
) -> Result<Vec<ExprPair>, QuotedSourceError> {
    cursor
        .list_items()?
        .into_iter()
        .map(|entry| decode_expr_pair(occurrences, &entry, fallback_span, sources))
        .collect::<Result<Vec<_>, _>>()
}

fn decode_keyword_entries(cursor: &QuotedSourceCursor) -> Result<Vec<(String, QuotedSourceCursor)>, QuotedSourceError> {
    let mut out = Vec::new();
    for entry in cursor.list_items()? {
        let items = entry.tuple_items()?;
        if items.len() != 2 {
            return Err(QuotedSourceError::new("quoted keyword entry expects a 2-tuple"));
        }
        out.push((items[0].atom_name()?, items[1].clone()));
    }
    Ok(out)
}

fn decode_module_target(
    cursor: &QuotedSourceCursor,
    sources: &SourceMap,
) -> Result<crate::ast::ModuleTarget, QuotedSourceError> {
    let node = expect_ast_node(cursor, "module alias", sources)?;
    if let Some(module) = node.meta.module_denotation()? {
        if module.named_path().is_none() {
            return Err(QuotedSourceError::new("a protocol implementation cannot name a struct"));
        }
        return Ok(crate::ast::ModuleTarget::Exact(module));
    }
    if atom_name(&node.head)? != "__aliases__" {
        return Err(QuotedSourceError::new("quoted module path expects an __aliases__ node"));
    }
    Ok(crate::ast::ModuleTarget::Unresolved(ModuleName::from_segments(
        node.tail.list_atom_names()?,
    )))
}

fn pattern_var_name(
    cursor: &QuotedSourceCursor,
    fallback_span: Option<Span>,
    sources: &SourceMap,
) -> Result<Option<String>, QuotedSourceError> {
    let decoded = decode_pattern(cursor, fallback_span, sources)?;
    Ok(match decoded.node {
        Pattern::Var(name) => Some(name),
        Pattern::Wildcard => Some("_".to_string()),
        _ => None,
    })
}

fn quoted_type_expr_body(cursor: &QuotedSourceCursor, sources: &SourceMap) -> Result<TypeExprBody, QuotedSourceError> {
    Ok(TypeExprBody(token_payload::decode_tokens(cursor, sources)?))
}

fn decode_spec_attribute(payload: &QuotedSourceCursor, sources: &SourceMap) -> Result<Attribute, QuotedSourceError> {
    let mut parser = FragmentCursor::new(token_payload::decode_tokens(payload, sources)?);
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
                    let span = parser.current_span();
                    let tokens = parser.collect_type_tokens(TypeTokenBoundary::SpecParam);
                    if tokens.is_empty() {
                        return Err(QuotedSourceError::user(
                            crate::diag::codes::PARSE_EXPECTED_TOKEN,
                            Some(span),
                            "expected type expression in @spec param list",
                        ));
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
            let left_span = parser.current_span();
            let left = parser.collect_type_tokens(TypeTokenBoundary::SpecInfixOperand);
            if left.is_empty() {
                return Err(QuotedSourceError::user(
                    crate::diag::codes::PARSE_EXPECTED_TOKEN,
                    Some(left_span),
                    "expected type expression before operator in @spec",
                ));
            }
            let op_span = parser.current_span();
            let name = parser
                .bump()
                .and_then(|tok| operator_token_name(&tok).map(str::to_string))
                .ok_or_else(|| {
                    QuotedSourceError::user(
                        crate::diag::codes::PARSE_EXPECTED_TOKEN,
                        Some(op_span),
                        "expected `@spec name(` or `@spec T1 <op> T2`",
                    )
                })?;
            let right_span = parser.current_span();
            let right = parser.collect_type_tokens(TypeTokenBoundary::SpecInfixOperand);
            if right.is_empty() {
                return Err(QuotedSourceError::user(
                    crate::diag::codes::PARSE_EXPECTED_TOKEN,
                    Some(right_span),
                    "expected type expression after operator in @spec",
                ));
            }
            (name, vec![TypeExprBody(left), TypeExprBody(right)])
        };

    parser.expect_colon_colon("`::` in @spec")?;
    let result_span = parser.current_span();
    let result_body_tokens = parser.collect_type_tokens(TypeTokenBoundary::TypeBody);
    if result_body_tokens.is_empty() {
        return Err(QuotedSourceError::user(
            crate::diag::codes::PARSE_EXPECTED_TOKEN,
            Some(result_span),
            "expected result type expression after `::` in @spec",
        ));
    }

    let mut constraints = Vec::new();
    if parser.eat_when() {
        loop {
            let var_span = parser.current_span();
            let (var, kw_colon) = match parser.bump() {
                Some(Tok::Ident(name)) => (name, false),
                Some(Tok::KwKey(name)) => (name, true),
                Some(other) => {
                    return Err(QuotedSourceError::user(
                        crate::diag::codes::PARSE_EXPECTED_TOKEN,
                        Some(var_span),
                        format!("expected type variable after `when`, got {:?}", other),
                    ));
                }
                None => {
                    return Err(QuotedSourceError::user(
                        crate::diag::codes::PARSE_EXPECTED_TOKEN,
                        Some(var_span),
                        "expected type variable after `when`",
                    ));
                }
            };
            if !kw_colon {
                parser.expect_colon("`:` after constrained type variable")?;
            }
            let body_span = parser.current_span();
            let body = parser.collect_type_tokens(TypeTokenBoundary::Constraint);
            if body.is_empty() {
                return Err(QuotedSourceError::user(
                    crate::diag::codes::PARSE_EXPECTED_TOKEN,
                    Some(body_span),
                    format!("expected constraint type expression after `{}:`", var),
                ));
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

/// `field_span` brackets the whole `value :: spec` bitstring field. It is the
/// fallback error span for a bare-literal modifier (`3.14`, `[1]`, a 2-tuple),
/// since frontdoor quotes literals without their own span metadata (only
/// call/var nodes carry one). A modifier shaped as a node -- `size(...)`,
/// `unit(...)`, a variable, or an unsupported name-with-args -- carries its own
/// `__fz_span__`, and `apply_bit_spec_modifier` threads that tighter node span
/// through to the error instead.
fn decode_bit_spec(
    cursor: &QuotedSourceCursor,
    field_span: Span,
    sources: &SourceMap,
) -> Result<BitFieldSpec, QuotedSourceError> {
    let mut spec = BitFieldSpec::default();
    apply_bit_spec_modifier(cursor, &mut spec, field_span, sources)?;
    Ok(spec)
}

fn apply_bit_spec_modifier(
    cursor: &QuotedSourceCursor,
    spec: &mut BitFieldSpec,
    field_span: Span,
    sources: &SourceMap,
) -> Result<(), QuotedSourceError> {
    if let Some(node) = cursor.ast_node(sources)? {
        let node_span = node.span.unwrap_or(Span::DUMMY);
        let args = if is_list_like(&node.tail) {
            node.tail.list_items()?
        } else {
            Vec::new()
        };
        return match atom_name(&node.head)?.as_str() {
            "-" if args.len() == 2 => {
                apply_bit_spec_modifier(&args[0], spec, field_span, sources)?;
                apply_bit_spec_modifier(&args[1], spec, field_span, sources)
            }
            "size" if args.len() == 1 => {
                spec.size = Some(decode_bit_size(&args[0], node_span, sources)?);
                Ok(())
            }
            "unit" if args.len() == 1 => {
                spec.unit = Some(decode_bit_unit(&args[0], node_span)?);
                Ok(())
            }
            name if args.is_empty() => apply_bit_modifier_name(spec, name, node_span),
            other => Err(QuotedSourceError::user(
                crate::diag::codes::PARSE_BITSTRING_BAD_MODIFIER,
                Some(node_span),
                format!("unsupported quoted bit-spec modifier `{other}`"),
            )),
        };
    }

    match cursor.root().tag() {
        fz_runtime::any_value::ValueKind::INT => {
            let raw = cursor.int_value()?;
            let size = u32::try_from(raw).map_err(|_| {
                QuotedSourceError::user(
                    crate::diag::codes::PARSE_BITSTRING_BAD_SIZE,
                    Some(field_span),
                    format!("bitstring size literal must fit in u32, got {raw}"),
                )
            })?;
            spec.size = Some(BitSize::Literal(size));
            Ok(())
        }
        fz_runtime::any_value::ValueKind::ATOM => apply_bit_modifier_name(spec, &cursor.atom_name()?, field_span),
        fz_runtime::any_value::ValueKind::BITSTRING | fz_runtime::any_value::ValueKind::PROCBIN => {
            apply_bit_modifier_name(spec, &cursor.utf8_binary_text()?, field_span)
        }
        // Reachable from valid source: a bitstring segment's `::` modifier is
        // parsed as a fully generic expr (frontdoor `parse_bitstring_literal`),
        // so a float literal (`<<x :: 3.14>>`), a list literal (`<<x :: [1]>>`,
        // including `nil`/`[]`), or a bare 2-element tuple literal
        // (`<<x :: {1, 2}>>` -- Elixir represents exactly-2-tuples as a raw
        // struct rather than wrapping them in a `{}` call node) all land here
        // with none of INT/ATOM/BITSTRING/PROCBIN. Every other modifier shape
        // (calls, atoms with args, N-tuples with N != 2) is caught earlier by
        // the `ast_node()` arm above. This is a plain user typo, not an
        // internal-compiler-bug shape. None of these literal kinds carry their
        // own span (frontdoor quotes bare literals unwrapped), so `field_span`
        // -- the enclosing `value :: spec` field -- is the tightest bracket
        // available.
        other => Err(QuotedSourceError::user(
            crate::diag::codes::PARSE_BITSTRING_BAD_MODIFIER,
            Some(field_span),
            format!("unsupported bitstring modifier value of kind {:?}", other),
        )),
    }
}

/// `error_span` is the tightest span the caller has for this modifier: the
/// enclosing `size(...)` call construct when reached from the `size` branch,
/// so a bad size argument points at the modifier itself.
fn decode_bit_size(
    cursor: &QuotedSourceCursor,
    error_span: Span,
    sources: &SourceMap,
) -> Result<BitSize, QuotedSourceError> {
    if let Ok(value) = cursor.int_value() {
        return u32::try_from(value).map(BitSize::Literal).map_err(|_| {
            QuotedSourceError::user(
                crate::diag::codes::PARSE_BITSTRING_BAD_SIZE,
                Some(error_span),
                format!("bitstring size literal must fit in u32, got {value}"),
            )
        });
    }
    if let Some(node) = cursor.ast_node(sources)?
        && !is_list_like(&node.tail)
    {
        return Ok(BitSize::Var(atom_name(&node.head)?));
    }
    match cursor.root().tag() {
        fz_runtime::any_value::ValueKind::ATOM => Ok(BitSize::Var(cursor.atom_name()?)),
        other => Err(QuotedSourceError::user(
            crate::diag::codes::PARSE_BITSTRING_BAD_SIZE,
            Some(error_span),
            format!("bitstring size expects int or variable, got {:?}", other),
        )),
    }
}

fn decode_bit_unit(cursor: &QuotedSourceCursor, error_span: Span) -> Result<u32, QuotedSourceError> {
    let raw = cursor.int_value()?;
    u32::try_from(raw).map_err(|_| {
        QuotedSourceError::user(
            crate::diag::codes::PARSE_BITSTRING_BAD_SIZE,
            Some(error_span),
            format!("bitstring unit must fit in u32, got {raw}"),
        )
    })
}

/// `error_span` is the tightest span the caller has for this modifier: the
/// modifier's own variable/call node when reached from the name branch of
/// `apply_bit_spec_modifier`, or the enclosing `::` field for a bare atom or
/// binary literal (frontdoor gives those no span of their own).
fn apply_bit_modifier_name(spec: &mut BitFieldSpec, name: &str, error_span: Span) -> Result<(), QuotedSourceError> {
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
        other => {
            return Err(QuotedSourceError::user(
                crate::diag::codes::PARSE_BITSTRING_BAD_MODIFIER,
                Some(error_span),
                format!("unknown bitstring modifier: {other}"),
            ));
        }
    }
    Ok(())
}

fn strip_extern_param_name(tokens: Vec<Token>) -> Result<Vec<Token>, QuotedSourceError> {
    let mut depth = 0_i32;
    for (index, token) in tokens.iter().enumerate() {
        match token.tok {
            Tok::LParen | Tok::LBrack | Tok::LBrace => depth += 1,
            Tok::RParen | Tok::RBrack | Tok::RBrace => depth -= 1,
            Tok::ColonColon if depth == 0 => {
                let body = tokens[index + 1..].to_vec();
                if body.is_empty() {
                    return Err(QuotedSourceError::new("expected extern parameter type after `::`"));
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

    /// The span of the next unconsumed token. Falls back to the last token's
    /// end (or `Span::DUMMY` for an empty fragment) at end-of-fragment, so an
    /// "expected X, got eof" error still points at a real location.
    fn current_span(&self) -> Span {
        self.toks
            .get(self.pos)
            .or_else(|| self.toks.last())
            .map(|token| token.span)
            .unwrap_or(Span::DUMMY)
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

    fn expect_lparen(&mut self, label: &str) -> Result<(), QuotedSourceError> {
        self.expect(|tok| matches!(tok, Tok::LParen), label)
    }

    fn expect_rparen(&mut self, label: &str) -> Result<(), QuotedSourceError> {
        self.expect(|tok| matches!(tok, Tok::RParen), label)
    }

    fn expect_colon_colon(&mut self, label: &str) -> Result<(), QuotedSourceError> {
        self.expect(|tok| matches!(tok, Tok::ColonColon), label)
    }

    fn expect_colon(&mut self, label: &str) -> Result<(), QuotedSourceError> {
        self.expect(|tok| matches!(tok, Tok::Colon), label)
    }

    fn expect_eof(&mut self, label: &str) -> Result<(), QuotedSourceError> {
        let span = self.current_span();
        match self.peek_at(0) {
            None => Ok(()),
            Some(Tok::Eof) => {
                self.pos += 1;
                Ok(())
            }
            Some(other) => Err(QuotedSourceError::user(
                crate::diag::codes::PARSE_EXPECTED_TOKEN,
                Some(span),
                format!("expected {label}, got {:?}", other),
            )),
        }
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

    fn expect(&mut self, pred: impl FnOnce(&Tok) -> bool, label: &str) -> Result<(), QuotedSourceError> {
        let span = self.current_span();
        match self.bump() {
            Some(tok) if pred(&tok) => Ok(()),
            Some(other) => Err(QuotedSourceError::user(
                crate::diag::codes::PARSE_EXPECTED_TOKEN,
                Some(span),
                format!("expected {label}, got {:?}", other),
            )),
            None => Err(QuotedSourceError::user(
                crate::diag::codes::PARSE_EXPECTED_TOKEN,
                Some(span),
                format!("expected {label}, got eof"),
            )),
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
        Tok::EqEqEq => "===",
        Tok::NotEqEq => "!==",
        Tok::Lt => "<",
        Tok::LtEq => "<=",
        Tok::Gt => ">",
        Tok::GtEq => ">=",
        _ => return None,
    })
}

fn required_map_utf8(cursor: &QuotedSourceCursor, key: &str) -> Result<String, QuotedSourceError> {
    cursor
        .map_value(key)?
        .ok_or_else(|| QuotedSourceError::new(format!("quoted map is missing `{key}`")))?
        .utf8_binary_text()
}

fn required_map_tokens(
    cursor: &QuotedSourceCursor,
    key: &str,
    sources: &SourceMap,
) -> Result<Vec<Token>, QuotedSourceError> {
    let value = cursor
        .map_value(key)?
        .ok_or_else(|| QuotedSourceError::new(format!("quoted map is missing `{key}`")))?;
    token_payload::decode_tokens(&value, sources)
}

fn required_map_list_tokens(
    cursor: &QuotedSourceCursor,
    key: &str,
    sources: &SourceMap,
) -> Result<Vec<Vec<Token>>, QuotedSourceError> {
    cursor
        .map_value(key)?
        .ok_or_else(|| QuotedSourceError::new(format!("quoted map is missing `{key}`")))?
        .list_items()?
        .into_iter()
        .map(|item| token_payload::decode_tokens(&item, sources))
        .collect::<Result<Vec<_>, _>>()
}

fn required_map_bool(cursor: &QuotedSourceCursor, key: &str) -> Result<bool, QuotedSourceError> {
    let value = cursor
        .map_value(key)?
        .ok_or_else(|| QuotedSourceError::new(format!("quoted map is missing `{key}`")))?;
    match value.atom_name()?.as_str() {
        "true" => Ok(true),
        "false" => Ok(false),
        other => Err(QuotedSourceError::new(format!(
            "quoted map bool `{key}` expected true/false, got `{other}`"
        ))),
    }
}

fn optional_map_keyword_tokens(
    cursor: &QuotedSourceCursor,
    key: &str,
    sources: &SourceMap,
) -> Result<Vec<(String, Vec<Token>)>, QuotedSourceError> {
    let Some(list) = cursor.map_value(key)? else {
        return Ok(Vec::new());
    };
    let mut out = Vec::new();
    for entry in list.list_items()? {
        let items = entry.tuple_items()?;
        if items.len() != 2 {
            return Err(QuotedSourceError::new("quoted keyword entry expects a 2-tuple"));
        }
        out.push((items[0].atom_name()?, token_payload::decode_tokens(&items[1], sources)?));
    }
    Ok(out)
}

fn expect_ast_node(
    cursor: &QuotedSourceCursor,
    context: &str,
    sources: &SourceMap,
) -> Result<QuotedAstNode, QuotedSourceError> {
    cursor
        .ast_node(sources)?
        .ok_or_else(|| QuotedSourceError::new(format!("expected quoted AST node for {context}")))
}

fn atom_name(cursor: &QuotedSourceCursor) -> Result<String, QuotedSourceError> {
    cursor.atom_name()
}

/// True when `node.head` is itself an atom equal to `name`.
///
/// An AST node's `head` is not always an atom: remote calls and closure
/// calls carry a quoted callee AST there instead (see `decode_expr`'s own
/// `node.head.root().tag() != ATOM` guard). Special-form markers such as the
/// improper-list `|` node are only ever atom-headed, so a non-atom head just
/// means "not this marker" rather than a decode error.
fn node_head_is_atom_named(node: &QuotedAstNode, name: &str) -> Result<bool, QuotedSourceError> {
    if node.head.root().tag() != fz_runtime::any_value::ValueKind::ATOM {
        return Ok(false);
    }
    Ok(atom_name(&node.head)? == name)
}

fn alias_name_from_args(args: &[QuotedSourceCursor]) -> Result<String, QuotedSourceError> {
    args.iter()
        .map(|segment| segment.atom_name())
        .collect::<Result<Vec<_>, _>>()
        .map(|segments| segments.join("."))
}

fn is_alias(cursor: &QuotedSourceCursor, sources: &SourceMap) -> Result<bool, QuotedSourceError> {
    let Some(node) = cursor.ast_node(sources)? else {
        return Ok(false);
    };
    Ok(atom_name(&node.head)? == "__aliases__")
}

/// True for the callee the front door synthesises for `lhs[key]`, and for
/// nothing a user can write.
///
/// Recognising the access by its `Access` alias is not sound: this decode runs
/// BEFORE alias resolution, so `alias Foo, as: Access` and `alias Foo.Access`
/// present the same segments as the real thing, and a user's `get/2` was
/// silently replaced by a map index with no diagnostic. The front door stamps
/// `__fz_from_brackets__` instead, which no source text can produce -- the same
/// separation Elixir makes with `from_brackets: true`.
fn is_bracket_access_callee(head_node: &QuotedAstNode) -> Result<bool, QuotedSourceError> {
    let Some(value) = head_node
        .meta
        .map_value(crate::compiler2::source::META_FROM_BRACKETS_KEY)?
    else {
        return Ok(false);
    };
    Ok(value.atom_name()? == "true")
}

fn is_list_like(cursor: &QuotedSourceCursor) -> bool {
    cursor.root().tag() == fz_runtime::any_value::ValueKind::LIST
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
