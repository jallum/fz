use crate::types::Types;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallableClause<T> {
    pub args: Vec<T>,
    pub ret: T,
    pub closure: Option<ClosureLitInfo<T>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ClosureTarget(pub u32);

impl From<crate::fz_ir::FnId> for ClosureTarget {
    fn from(value: crate::fz_ir::FnId) -> Self {
        Self(value.0)
    }
}

impl From<ClosureTarget> for crate::fz_ir::FnId {
    fn from(value: ClosureTarget) -> Self {
        Self(value.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClosureLitInfo<T> {
    pub target: ClosureTarget,
    pub captures: Vec<T>,
}

pub trait ClosureTypes: Types {
    fn closure_lit(
        &mut self,
        target: ClosureTarget,
        captures: Vec<Self::Ty>,
        n_args: usize,
    ) -> Self::Ty;

    /// If `a` is a singleton closure literal, return the callee target
    /// and captured literal values.
    fn closure_lit_parts(&self, a: &Self::Ty) -> Option<ClosureLitInfo<Self::Ty>>;

    /// If `a` has only pure positive callable clauses, return each
    /// clause's argument pattern, return type, and optional closure-literal
    /// target metadata. `None` means the callable shape is absent or too
    /// broad to drive closure-return narrowing.
    fn callable_clauses(&mut self, a: &Self::Ty) -> Option<Vec<CallableClause<Self::Ty>>>;

    /// Erase concrete closure-literal identity (`fn_id` + captures) while
    /// preserving the callable surface shape. Used for higher-order fixed-point
    /// key slots whose behavior matters, but whose specific closure value
    /// should not fork specialization.
    fn erase_closure_identity(&mut self, a: &Self::Ty) -> Self::Ty;
}
