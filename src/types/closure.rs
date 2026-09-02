use crate::fz_ir::FnId;
use crate::types::Types;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallableClause<T> {
    pub args: Vec<T>,
    pub ret: T,
    pub closure: Option<ClosureLitInfo<T>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CallableValueKind {
    FnRef,
    Closure,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ClosureTarget(pub u32);

impl From<FnId> for ClosureTarget {
    fn from(value: FnId) -> Self {
        Self(value.0)
    }
}

impl From<ClosureTarget> for FnId {
    fn from(value: ClosureTarget) -> Self {
        Self(value.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClosureLitInfo<T> {
    pub target: ClosureTarget,
    pub captures: Vec<T>,
    pub kind: CallableValueKind,
}

pub trait ClosureTypes: Types {
    fn fn_ref_lit(&mut self, target: ClosureTarget, n_args: usize) -> Self::Ty;

    fn closure_lit(&mut self, target: ClosureTarget, captures: Vec<Self::Ty>, n_args: usize) -> Self::Ty;

    /// If `a` is a singleton closure literal, return the callee target
    /// and captured literal values plus callable kind.
    fn closure_lit_parts(&self, a: &Self::Ty) -> Option<ClosureLitInfo<Self::Ty>>;

    /// If `a` has only pure positive callable clauses, return each
    /// clause's argument pattern, return type, and optional closure-literal
    /// target metadata. `None` means the callable shape is absent or too
    /// broad to drive closure-return narrowing.
    fn callable_clauses(&mut self, a: &Self::Ty) -> Option<Vec<CallableClause<Self::Ty>>>;

    /// Erase a closure literal's BRAND -- which lambda the value was minted
    /// from -- at every depth, keeping its capture TYPES and the callable
    /// surface shape. Used for higher-order fixed-point key slots that only
    /// transport a closure: which lambda arrived must not fork specialization,
    /// while what it closed over must, because a body keyed at one capture type
    /// grounds its callees' capture lanes to that type. A capture-free literal
    /// has nothing left to say once its brand is gone and erases to its arrow.
    fn erase_closure_identity(&mut self, a: &Self::Ty) -> Self::Ty;
}
