use fz_runtime::any_value::AnyValueRef;

use crate::compiler::source::{Id as SourceId, Span};
use crate::parser::lexer::{Tok, Token};

use super::source::{QuotedSourceBuilder, QuotedSourceCursor, QuotedSourceError};

pub(crate) fn encode_tokens(builder: &QuotedSourceBuilder, tokens: &[Token]) -> Result<AnyValueRef, QuotedSourceError> {
    let encoded = tokens
        .iter()
        .map(|token| encode_token(builder, token))
        .collect::<Result<Vec<_>, _>>()?;
    builder.list(&encoded)
}

pub(crate) fn decode_tokens(cursor: &QuotedSourceCursor) -> Result<Vec<Token>, QuotedSourceError> {
    cursor
        .list_items()?
        .into_iter()
        .map(|item| decode_token(&item))
        .collect()
}

fn encode_token(builder: &QuotedSourceBuilder, token: &Token) -> Result<AnyValueRef, QuotedSourceError> {
    let (kind, payload) = encode_tok(builder, &token.tok)?;
    builder.tuple(&[
        builder.atom(kind),
        payload,
        builder.int(token.span.start as i64),
        builder.int(token.span.end as i64),
        builder.bool(token.space_before),
    ])
}

fn encode_tok(builder: &QuotedSourceBuilder, tok: &Tok) -> Result<(&'static str, AnyValueRef), QuotedSourceError> {
    let nil = || builder.nil();
    Ok(match tok {
        Tok::Int(value) => ("int", builder.int(*value)),
        Tok::Float(value) => ("float", builder.float(*value)),
        Tok::Atom(value) => ("atom", builder.utf8_binary(value)?),
        Tok::Ident(value) => ("ident", builder.utf8_binary(value)?),
        Tok::Upper(value) => ("upper", builder.utf8_binary(value)?),
        Tok::KwKey(value) => ("kw_key", builder.utf8_binary(value)?),
        Tok::Sigil(value) => ("sigil", builder.utf8_binary(value)?),
        Tok::Binary(bytes) => {
            let items = bytes
                .iter()
                .map(|byte| builder.int(i64::from(*byte)))
                .collect::<Vec<_>>();
            ("binary", builder.list(&items)?)
        }
        Tok::True => ("true", nil()),
        Tok::False => ("false", nil()),
        Tok::Nil => ("nil", nil()),
        Tok::Fn => ("fn", nil()),
        Tok::Fnp => ("fnp", nil()),
        Tok::Extern => ("extern", nil()),
        Tok::Defmacro => ("defmacro", nil()),
        Tok::Defmodule => ("defmodule", nil()),
        Tok::Defstruct => ("defstruct", nil()),
        Tok::Defprotocol => ("defprotocol", nil()),
        Tok::Defimpl => ("defimpl", nil()),
        Tok::Alias => ("alias", nil()),
        Tok::Import => ("import", nil()),
        Tok::Require => ("require", nil()),
        Tok::Do => ("do", nil()),
        Tok::End => ("end", nil()),
        Tok::If => ("if", nil()),
        Tok::Else => ("else", nil()),
        Tok::Case => ("case", nil()),
        Tok::Cond => ("cond", nil()),
        Tok::When => ("when", nil()),
        Tok::With => ("with", nil()),
        Tok::Quote => ("quote", nil()),
        Tok::Unquote => ("unquote", nil()),
        Tok::Type => ("type", nil()),
        Tok::In => ("in", nil()),
        Tok::Not => ("not", nil()),
        Tok::And => ("and", nil()),
        Tok::Or => ("or", nil()),
        Tok::Receive => ("receive", nil()),
        Tok::After => ("after", nil()),
        Tok::LParen => ("l_paren", nil()),
        Tok::RParen => ("r_paren", nil()),
        Tok::LBrack => ("l_brack", nil()),
        Tok::RBrack => ("r_brack", nil()),
        Tok::LBrace => ("l_brace", nil()),
        Tok::RBrace => ("r_brace", nil()),
        Tok::LBitstr => ("l_bitstr", nil()),
        Tok::RBitstr => ("r_bitstr", nil()),
        Tok::PercentLBrace => ("percent_l_brace", nil()),
        Tok::Comma => ("comma", nil()),
        Tok::Dot => ("dot", nil()),
        Tok::Ellipsis => ("ellipsis", nil()),
        Tok::Semi => ("semi", nil()),
        Tok::Colon => ("colon", nil()),
        Tok::ColonColon => ("colon_colon", nil()),
        Tok::Arrow => ("arrow", nil()),
        Tok::FatArrow => ("fat_arrow", nil()),
        Tok::LArrow => ("l_arrow", nil()),
        Tok::Pipe => ("pipe", nil()),
        Tok::Bar => ("bar", nil()),
        Tok::Caret => ("caret", nil()),
        Tok::Underscore => ("underscore", nil()),
        Tok::Eq => ("eq", nil()),
        Tok::EqEq => ("eq_eq", nil()),
        Tok::NotEq => ("not_eq", nil()),
        Tok::Lt => ("lt", nil()),
        Tok::LtEq => ("lt_eq", nil()),
        Tok::Gt => ("gt", nil()),
        Tok::GtEq => ("gt_eq", nil()),
        Tok::Plus => ("plus", nil()),
        Tok::Minus => ("minus", nil()),
        Tok::Star => ("star", nil()),
        Tok::Slash => ("slash", nil()),
        Tok::Percent => ("percent", nil()),
        Tok::At => ("at", nil()),
        Tok::Amp => ("amp", nil()),
        Tok::PlusPlus => ("plus_plus", nil()),
        Tok::MinusMinus => ("minus_minus", nil()),
        Tok::Concat => ("concat", nil()),
        Tok::DotDot => ("dot_dot", nil()),
        Tok::SlashSlash => ("slash_slash", nil()),
        Tok::Newline => ("newline", nil()),
        Tok::Eof => ("eof", nil()),
    })
}

fn decode_token(cursor: &QuotedSourceCursor) -> Result<Token, QuotedSourceError> {
    let fields = cursor.tuple_items()?;
    if fields.len() != 5 {
        return Err(QuotedSourceError::new(format!(
            "encoded token expects 5 fields, got {}",
            fields.len()
        )));
    }
    let kind = fields[0].atom_name()?;
    let tok = decode_tok(&kind, &fields[1])?;
    let start = decode_u32(&fields[2], "token start")?;
    let end = decode_u32(&fields[3], "token end")?;
    let space_before = decode_bool(&fields[4], "token space_before")?;
    Ok(Token {
        tok,
        span: Span::new(SourceId(0), start, end),
        space_before,
    })
}

fn decode_tok(kind: &str, payload: &QuotedSourceCursor) -> Result<Tok, QuotedSourceError> {
    Ok(match kind {
        "int" => Tok::Int(payload.int_value()?),
        "float" => Tok::Float(payload.root().load_float().map_err(QuotedSourceError::from)?),
        "atom" => Tok::Atom(payload.utf8_binary_text()?),
        "ident" => Tok::Ident(payload.utf8_binary_text()?),
        "upper" => Tok::Upper(payload.utf8_binary_text()?),
        "kw_key" => Tok::KwKey(payload.utf8_binary_text()?),
        "sigil" => Tok::Sigil(payload.utf8_binary_text()?),
        "binary" => Tok::Binary(decode_bytes(payload)?),
        "true" => Tok::True,
        "false" => Tok::False,
        "nil" => Tok::Nil,
        "fn" => Tok::Fn,
        "fnp" => Tok::Fnp,
        "extern" => Tok::Extern,
        "defmacro" => Tok::Defmacro,
        "defmodule" => Tok::Defmodule,
        "defstruct" => Tok::Defstruct,
        "defprotocol" => Tok::Defprotocol,
        "defimpl" => Tok::Defimpl,
        "alias" => Tok::Alias,
        "import" => Tok::Import,
        "require" => Tok::Require,
        "do" => Tok::Do,
        "end" => Tok::End,
        "if" => Tok::If,
        "else" => Tok::Else,
        "case" => Tok::Case,
        "cond" => Tok::Cond,
        "when" => Tok::When,
        "with" => Tok::With,
        "quote" => Tok::Quote,
        "unquote" => Tok::Unquote,
        "type" => Tok::Type,
        "in" => Tok::In,
        "not" => Tok::Not,
        "and" => Tok::And,
        "or" => Tok::Or,
        "receive" => Tok::Receive,
        "after" => Tok::After,
        "l_paren" => Tok::LParen,
        "r_paren" => Tok::RParen,
        "l_brack" => Tok::LBrack,
        "r_brack" => Tok::RBrack,
        "l_brace" => Tok::LBrace,
        "r_brace" => Tok::RBrace,
        "l_bitstr" => Tok::LBitstr,
        "r_bitstr" => Tok::RBitstr,
        "percent_l_brace" => Tok::PercentLBrace,
        "comma" => Tok::Comma,
        "dot" => Tok::Dot,
        "ellipsis" => Tok::Ellipsis,
        "semi" => Tok::Semi,
        "colon" => Tok::Colon,
        "colon_colon" => Tok::ColonColon,
        "arrow" => Tok::Arrow,
        "fat_arrow" => Tok::FatArrow,
        "l_arrow" => Tok::LArrow,
        "pipe" => Tok::Pipe,
        "bar" => Tok::Bar,
        "caret" => Tok::Caret,
        "underscore" => Tok::Underscore,
        "eq" => Tok::Eq,
        "eq_eq" => Tok::EqEq,
        "not_eq" => Tok::NotEq,
        "lt" => Tok::Lt,
        "lt_eq" => Tok::LtEq,
        "gt" => Tok::Gt,
        "gt_eq" => Tok::GtEq,
        "plus" => Tok::Plus,
        "minus" => Tok::Minus,
        "star" => Tok::Star,
        "slash" => Tok::Slash,
        "percent" => Tok::Percent,
        "at" => Tok::At,
        "amp" => Tok::Amp,
        "plus_plus" => Tok::PlusPlus,
        "minus_minus" => Tok::MinusMinus,
        "concat" => Tok::Concat,
        "dot_dot" => Tok::DotDot,
        "slash_slash" => Tok::SlashSlash,
        "newline" => Tok::Newline,
        "eof" => Tok::Eof,
        other => return Err(QuotedSourceError::new(format!("unknown encoded token kind `{other}`"))),
    })
}

fn decode_u32(cursor: &QuotedSourceCursor, label: &str) -> Result<u32, QuotedSourceError> {
    u32::try_from(cursor.int_value()?).map_err(|_| QuotedSourceError::new(format!("{label} must fit in u32")))
}

fn decode_bool(cursor: &QuotedSourceCursor, label: &str) -> Result<bool, QuotedSourceError> {
    match cursor.atom_name()?.as_str() {
        "true" => Ok(true),
        "false" => Ok(false),
        other => Err(QuotedSourceError::new(format!(
            "{label} expected true/false, got `{other}`"
        ))),
    }
}

fn decode_bytes(cursor: &QuotedSourceCursor) -> Result<Vec<u8>, QuotedSourceError> {
    cursor
        .list_items()?
        .into_iter()
        .map(|item| {
            let value = item.int_value()?;
            u8::try_from(value)
                .map_err(|_| QuotedSourceError::new(format!("encoded binary byte must fit in u8, got {value}")))
        })
        .collect()
}
