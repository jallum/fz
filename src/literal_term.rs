//! A value written out in full.

use crate::ast::{CallableName, Expr, ModuleTarget, Spanned};
use crate::ground_value::{GroundValue, entries_in_atom_key_order};
use crate::source::Span;
use fz_runtime::module_name::ModuleName;

/// A value written out in full: a scalar, a function named by its module, or
/// a list, tuple or map of such values. It reads no alias, import or
/// variable, so it means the same wherever it is read. A field default is
/// one, which is why a struct literal in any module can start from it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LiteralTerm {
    Ground(GroundValue),
    List(Vec<LiteralTerm>),
    Tuple(Vec<LiteralTerm>),
    Map(Vec<(LiteralTerm, LiteralTerm)>),
    /// `&Mod.fun/arity`, with `Mod` the module itself and not a spelling an
    /// alias could redirect.
    Function {
        module: ModuleName,
        name: String,
        arity: usize,
    },
}

impl From<GroundValue> for LiteralTerm {
    fn from(value: GroundValue) -> Self {
        Self::Ground(value)
    }
}

impl LiteralTerm {
    /// `expr` as a constant: a literal term that holds no function, whose
    /// value is therefore known where the source is read.
    pub fn constant(expr: &Expr) -> Option<Self> {
        Self::of(expr).filter(|term| !term.holds_a_function())
    }

    /// A map literal's entries in the runtime's key order with no key
    /// repeated, when every key is an atom.
    pub fn entries_in_key_order(entries: &[(LiteralTerm, LiteralTerm)]) -> Option<Vec<&(LiteralTerm, LiteralTerm)>> {
        entries_in_atom_key_order(entries.iter().map(|entry| match &entry.0 {
            Self::Ground(key) => (Some(key), entry),
            _ => (None, entry),
        }))
    }

    /// `expr` as a literal term, or `None` when it computes or names anything.
    pub fn of(expr: &Expr) -> Option<Self> {
        let all = |items: &[Spanned<Expr>]| {
            items
                .iter()
                .map(|item| Self::of(&item.node))
                .collect::<Option<Vec<_>>>()
        };
        Some(match expr {
            Expr::Int(value) => Self::Ground(GroundValue::Int(*value)),
            Expr::Float(value) => Self::Ground(GroundValue::from_f64(*value)),
            Expr::Binary(bytes) => Self::Ground(GroundValue::Binary(bytes.clone())),
            Expr::Atom(name) => Self::Ground(GroundValue::Atom(name.clone())),
            Expr::Bool(value) => Self::Ground(GroundValue::Bool(*value)),
            Expr::Nil => Self::Ground(GroundValue::Nil),
            Expr::List(items, None) => Self::List(all(items)?),
            Expr::Tuple(items) => Self::Tuple(all(items)?),
            Expr::Map(entries) => Self::Map(
                entries
                    .iter()
                    .map(|(key, value)| Some((Self::of(&key.node)?, Self::of(&value.node)?)))
                    .collect::<Option<_>>()?,
            ),
            Expr::FnRef {
                name:
                    CallableName {
                        module: Some(ModuleTarget::Exact(module)),
                        name,
                    },
                arity,
            } => Self::Function {
                module: module.clone(),
                name: name.clone(),
                arity: *arity,
            },
            _ => return None,
        })
    }

    /// The expression that writes this term, placed at `span`.
    pub fn expr(&self, span: Span) -> Spanned<Expr> {
        let all = |items: &[LiteralTerm]| items.iter().map(|item| item.expr(span)).collect();
        let node = match self {
            Self::Ground(GroundValue::Int(value)) => Expr::Int(*value),
            Self::Ground(GroundValue::Float(bits)) => Expr::Float(f64::from_bits(*bits)),
            Self::Ground(GroundValue::Binary(bytes) | GroundValue::Utf8Binary(bytes)) => Expr::Binary(bytes.clone()),
            Self::Ground(GroundValue::Atom(name)) => Expr::Atom(name.clone()),
            Self::Ground(GroundValue::Bool(value)) => Expr::Bool(*value),
            Self::Ground(GroundValue::Nil) => Expr::Nil,
            Self::List(items) => Expr::List(all(items), None),
            Self::Tuple(items) => Expr::Tuple(all(items)),
            Self::Map(entries) => Expr::Map(
                entries
                    .iter()
                    .map(|(key, value)| (key.expr(span), value.expr(span)))
                    .collect(),
            ),
            Self::Function { module, name, arity } => Expr::FnRef {
                name: CallableName {
                    module: Some(ModuleTarget::Exact(module.clone())),
                    name: name.clone(),
                },
                arity: *arity,
            },
        };
        Spanned::new(node, span)
    }

    /// Whether a function is anywhere in this term.
    pub fn holds_a_function(&self) -> bool {
        match self {
            Self::Ground(_) => false,
            Self::Function { .. } => true,
            Self::List(items) | Self::Tuple(items) => items.iter().any(Self::holds_a_function),
            Self::Map(entries) => entries
                .iter()
                .any(|(key, value)| key.holds_a_function() || value.holds_a_function()),
        }
    }

    /// Every scalar this term is built from, in the order it writes them.
    pub fn each_ground<'a>(&'a self, visit: &mut impl FnMut(&'a GroundValue)) {
        match self {
            Self::Ground(value) => visit(value),
            Self::Function { .. } => {}
            Self::List(items) | Self::Tuple(items) => items.iter().for_each(|item| item.each_ground(visit)),
            Self::Map(entries) => entries.iter().for_each(|(key, value)| {
                key.each_ground(visit);
                value.each_ground(visit);
            }),
        }
    }
}
