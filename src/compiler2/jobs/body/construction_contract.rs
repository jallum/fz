//! What a binary construction's segments must hold, as the source that tests
//! it. Each segment has a contract: an `integer` takes an integer, a `float` a
//! float or an integer, a `binary` a bitstring of whole units (or at least
//! `size` units), a `bits` a bitstring, a `utf` segment a Unicode scalar value,
//! and a named size is a non-negative integer (16, 32 or 64 for a `float`).
//! Lowering evaluates the segments' values, tests the conjunction of every
//! term the program text does not already settle, and builds on the true edge.
//! The false edge calls `Kernel.__construction_failed__/1`, which raises the
//! `ArgumentError` Elixir raises. A term whose value's type already proves it
//! folds away, so a construction of proven values compiles to the build alone.

use crate::ast::{BinOp, BitField, BitSize, BitType, Expr, Spanned, Var};
use crate::modules::identity::{ModuleDenotation, ModuleName};
use crate::source::Span;

/// The test a construction's segments must pass, and the call that raises
/// when they do not.
pub(super) struct ConstructionCheck {
    pub(super) test: Spanned<Expr>,
    pub(super) failure: Spanned<Expr>,
}

/// The check of `fields`, whose values `values` name in order; `None` when the
/// program text settles every term.
pub(super) fn construction_check(
    fields: &[BitField<Spanned<Expr>>],
    values: &[Var],
    span: Span,
) -> Option<ConstructionCheck> {
    let build = Build { span };
    let test = fields
        .iter()
        .zip(values)
        .flat_map(|(field, value)| build.terms(field, value))
        .reduce(|left, right| build.op(BinOp::And, left, right))?;
    let segments = fields
        .iter()
        .zip(values)
        .map(|(field, value)| build.segment(field, value));
    let failure = build.kernel(
        "__construction_failed__",
        vec![build.expr(Expr::List(segments.collect(), None))],
    );
    Some(ConstructionCheck { test, failure })
}

struct Build {
    span: Span,
}

impl Build {
    fn expr(&self, expr: Expr) -> Spanned<Expr> {
        Spanned::new(expr, self.span)
    }

    fn int(&self, value: i64) -> Spanned<Expr> {
        self.expr(Expr::Int(value))
    }

    fn op(&self, op: BinOp, left: Spanned<Expr>, right: Spanned<Expr>) -> Spanned<Expr> {
        self.expr(Expr::BinOp(op, Box::new(left), Box::new(right)))
    }

    fn all(&self, terms: impl IntoIterator<Item = Spanned<Expr>>) -> Option<Spanned<Expr>> {
        terms.into_iter().reduce(|left, right| self.op(BinOp::And, left, right))
    }

    fn kernel(&self, function: &str, args: Vec<Spanned<Expr>>) -> Spanned<Expr> {
        let kernel = ModuleDenotation::Named(ModuleName::from_segments(vec!["Kernel".to_string()]));
        let callee = Expr::Index(
            Box::new(self.expr(Expr::Module(kernel))),
            Box::new(self.expr(Expr::Atom(function.to_string()))),
        );
        self.expr(Expr::Call(Box::new(self.expr(callee)), args))
    }

    /// `{type, value, size, unit}`, as `Kernel.__construction_failed__/1`
    /// takes a segment.
    fn segment(&self, field: &BitField<Spanned<Expr>>, value: &Var) -> Spanned<Expr> {
        let size = match &field.spec.size {
            Some(BitSize::Literal(size)) => self.int(i64::from(*size)),
            Some(BitSize::Var(size) | BitSize::ByteSizeOf(size)) => self.expr(Expr::Var(size.clone())),
            None => self.expr(Expr::Nil),
        };
        self.expr(Expr::Tuple(vec![
            self.int(i64::from(field.spec.ty.runtime_tag())),
            self.expr(Expr::Var(value.clone())),
            size,
            self.int(i64::from(unit(field))),
        ]))
    }

    /// The terms of `field`'s contract the program text leaves open: its size's,
    /// then its value's.
    fn terms(&self, field: &BitField<Spanned<Expr>>, value: &Var) -> Vec<Spanned<Expr>> {
        let size = match &field.spec.size {
            Some(BitSize::Var(size)) => Some(self.expr(Expr::Var(size.clone()))),
            _ => None,
        };
        let value_expr = self.expr(Expr::Var(value.clone()));
        let mut terms = Vec::new();
        if let Some(size) = &size {
            terms.extend(self.size_terms(field.spec.ty, size));
        }
        if !settled_by_literal(field) {
            terms.extend(self.value_terms(field, &value_expr, size.as_ref()));
        }
        terms
    }

    fn size_terms(&self, ty: BitType, size: &Spanned<Expr>) -> Vec<Spanned<Expr>> {
        let is_integer = self.kernel("is_integer", vec![size.clone()]);
        let range = match ty {
            BitType::Float => [16, 32, 64]
                .into_iter()
                .map(|bits| self.op(BinOp::Eq, size.clone(), self.int(bits)))
                .reduce(|left, right| self.op(BinOp::Or, left, right))
                .expect("three float sizes"),
            _ => self.op(BinOp::GtEq, size.clone(), self.int(0)),
        };
        vec![is_integer, range]
    }

    fn value_terms(
        &self,
        field: &BitField<Spanned<Expr>>,
        value: &Spanned<Expr>,
        size: Option<&Spanned<Expr>>,
    ) -> Vec<Spanned<Expr>> {
        let is = |test: &str| self.kernel(test, vec![value.clone()]);
        match field.spec.ty {
            BitType::Integer => vec![is("is_integer")],
            BitType::Float => vec![is("is_number")],
            BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => {
                let below_surrogates = self.op(BinOp::Lt, value.clone(), self.int(0xD800));
                let above_surrogates = self.op(BinOp::Gt, value.clone(), self.int(0xDFFF));
                vec![
                    is("is_integer"),
                    self.op(BinOp::GtEq, value.clone(), self.int(0)),
                    self.op(BinOp::LtEq, value.clone(), self.int(0x10FFFF)),
                    self.op(BinOp::Or, below_surrogates, above_surrogates),
                ]
            }
            BitType::Binary | BitType::Bits => {
                let bit_size = || self.kernel("bit_size", vec![value.clone()]);
                let unit = i64::from(unit(field));
                let length = match (&field.spec.size, size) {
                    (Some(BitSize::Literal(bits)), _) => {
                        Some(self.op(BinOp::GtEq, bit_size(), self.int(i64::from(*bits) * unit)))
                    }
                    (_, Some(size)) => {
                        let needed = self.op(BinOp::Mul, size.clone(), self.int(unit));
                        Some(self.op(BinOp::GtEq, bit_size(), needed))
                    }
                    _ if unit == 1 => None,
                    _ if unit == 8 => return vec![is("is_binary")],
                    _ => Some(self.op(BinOp::Eq, self.op(BinOp::Rem, bit_size(), self.int(unit)), self.int(0))),
                };
                vec![
                    self.all([is("is_bitstring")].into_iter().chain(length))
                        .expect("a bitstring test"),
                ]
            }
        }
    }
}

/// A literal value whose contract the program text already keeps.
fn settled_by_literal(field: &BitField<Spanned<Expr>>) -> bool {
    match (&field.value.node, field.spec.ty) {
        (Expr::Int(_), BitType::Integer | BitType::Float) | (Expr::Float(_), BitType::Float) => true,
        (Expr::Int(cp), BitType::Utf8 | BitType::Utf16 | BitType::Utf32) => {
            (0..=0x10FFFF).contains(cp) && !(0xD800..=0xDFFF).contains(cp)
        }
        (Expr::Binary(bytes), BitType::Binary | BitType::Bits) => match field.spec.size {
            None => (8 * bytes.len() as u64).is_multiple_of(u64::from(unit(field))),
            Some(BitSize::Literal(size)) => 8 * bytes.len() as u64 >= u64::from(size) * u64::from(unit(field)),
            Some(_) => false,
        },
        _ => false,
    }
}

fn unit(field: &BitField<Spanned<Expr>>) -> u32 {
    field.spec.unit.unwrap_or(field.spec.ty.default_unit())
}
