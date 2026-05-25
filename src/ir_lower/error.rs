use super::*;
use crate::ast::{
    BinOp as AstBinOp, BitField as AstBitField, BitSize as AstBitSize, Expr, FnClause, FnDef, Item,
    MatchClause, Pattern, Program, Spanned, UnOp as AstUnOp, WithBinding,
};
use crate::diag::Span;
use crate::fz_ir::{
    BinOp, BitFieldIr, BitSizeIr, BlockId, Const, Cont, ExternDecl, ExternId, ExternTy, FnBuilder,
    FnId, Module, ModuleBuilder, Prim, SourceInfo, Term, UnOp, Var,
};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq)]
pub enum LowerError {
    Unsupported {
        span: Span,
        what: String,
    },
    Unbound {
        span: Span,
        name: String,
    },
    PostExpansionNode {
        span: Span,
        what: String,
    },
    /// fz-axu.24 (M3) — a `Prim::Brand(_, T)` mint reaches the
    /// pre-erasure visibility pass from a fn that doesn't own brand
    /// `T`. `T` is the qualified brand tag; `owner_module` is the
    /// module that declared it; `using_module` is the module path of
    /// the fn doing the mint. v1 only emits Brand prims for the
    /// built-in `utf8` (no owner), so this fires only when user-
    /// declared brands acquire a mint syntax. The plumbing is here.
    BrandMintVisibility {
        span: Span,
        brand: String,
        owner_module: String,
        using_module: String,
    },
}

impl LowerError {
    pub fn to_diagnostic(&self) -> crate::diag::Diagnostic {
        use crate::diag::{Diagnostic, codes};
        match self {
            LowerError::Unsupported { span, what } => Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("unsupported: {}", what),
                *span,
            ),
            LowerError::Unbound { span, name } => {
                Diagnostic::error(codes::LOWER_UNBOUND, format!("unbound: {}", name), *span)
            }
            LowerError::PostExpansionNode { span, what } => Diagnostic::error(
                codes::LOWER_POST_EXPANSION_LEFTOVER,
                format!("post-expansion node leaked: {}", what),
                *span,
            ),
            LowerError::BrandMintVisibility {
                span,
                brand,
                owner_module,
                using_module,
            } => Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!(
                    "brand `{}` can only be minted from inside module `{}`; \
                     minted from `{}` here",
                    brand,
                    owner_module,
                    if using_module.is_empty() {
                        "<top-level>"
                    } else {
                        using_module.as_str()
                    },
                ),
                *span,
            ),
        }
    }
}

impl std::fmt::Display for LowerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.to_diagnostic().message)
    }
}

impl std::error::Error for LowerError {}
