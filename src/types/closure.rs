use crate::types::Types;
use std::collections::HashMap;

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

    /// Resolve a closure-typed callee's return under the given arg
    /// witnesses and accumulated effective-return table.
    ///
    /// Returns `None` when a closure-literal clause refers to a spec
    /// whose return has not yet been registered, so callers can defer to
    /// a later fixpoint iteration.
    fn resolve_closure_return(
        &mut self,
        closure_ty: &Self::Ty,
        effective_returns: &HashMap<(ClosureTarget, Vec<Self::Ty>), Self::Ty>,
        arg_tys: &[Self::Ty],
    ) -> Option<Self::Ty> {
        let Some(clauses) = self.callable_clauses(closure_ty) else {
            return Some(self.any());
        };
        let mut acc = self.none();
        for clause in clauses {
            match clause.closure {
                None => {
                    let contrib = if self.has_vars(&clause.ret)
                        || clause.args.iter().any(|arg| self.has_vars(arg))
                    {
                        if clause.args.len() == arg_tys.len() {
                            let mut sigma = HashMap::new();
                            for (pat, wit) in clause.args.iter().zip(arg_tys.iter()) {
                                self.collect_instantiation_subst(pat, wit, &mut sigma);
                            }
                            self.instantiate(&clause.ret, &sigma)
                        } else {
                            clause.ret
                        }
                    } else {
                        clause.ret
                    };
                    acc = self.union(acc, contrib);
                }
                Some(ClosureLitInfo { target, captures }) => {
                    if clause.args.len() != arg_tys.len() {
                        return Some(self.any());
                    }
                    let mut full_key = captures.clone();
                    full_key.extend_from_slice(arg_tys);
                    match effective_returns.get(&(target, full_key)) {
                        Some(r) => acc = self.union(acc, r.clone()),
                        None => return None,
                    }
                }
            }
        }
        Some(acc)
    }
}
