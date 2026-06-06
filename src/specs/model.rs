use std::collections::HashMap;

use crate::modules::identity::ModuleName;
use crate::types::{Ty, TypeVarId};

/// Resolved form of a `SpecDecl` after type-expression lookup. The
/// type-expression layer constructs this model; spec consumers own the
/// semantic operations over it.
#[derive(Debug, Clone)]
pub(crate) struct ResolvedSpec {
    pub params: Vec<Ty>,
    pub param_shapes: Vec<ResolvedTypeShape>,
    pub result: Ty,
    pub result_shape: ResolvedTypeShape,
    pub constraints: HashMap<TypeVarId, Ty>,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct ResolvedSpecSet {
    pub arrows: Vec<ResolvedSpec>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ResolvedSpecMatch {
    pub params: Vec<Ty>,
    pub result: Ty,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct StructuralCorrespondenceGroup {
    pub var: TypeVarId,
    pub occurrences: Vec<StructuralOccurrence>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct ResolvedStructFieldShape {
    pub name: String,
    pub ty: ResolvedTypeShape,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) enum ResolvedTypeShape {
    #[default]
    Any,
    Never,
    Nil,
    Bool,
    Integer,
    Float,
    CPointer,
    Binary,
    Atom,
    Utf8,
    Pid,
    Ref,
    Var(TypeVarId),
    AtomLit(String),
    IntLit(i64),
    FloatLit(u64),
    Named {
        name: String,
        args: Vec<ResolvedTypeShape>,
    },
    Resource(Box<ResolvedTypeShape>),
    List(Box<ResolvedTypeShape>),
    Tuple(Vec<ResolvedTypeShape>),
    Arrow {
        params: Vec<ResolvedTypeShape>,
        result: Box<ResolvedTypeShape>,
    },
    Union(Vec<ResolvedTypeShape>),
    StructRecord {
        module: ModuleName,
        fields: Vec<ResolvedStructFieldShape>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum StructuralPathStep {
    NamedArg(usize),
    ResourceInner,
    ListElem,
    TupleElem(usize),
    ArrowParam(usize),
    ArrowResult,
    UnionMember(usize),
    StructField(String),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum StructuralOccurrence {
    Param {
        param_index: usize,
        path: Vec<StructuralPathStep>,
    },
    Result {
        path: Vec<StructuralPathStep>,
    },
    CallbackArg {
        param_index: usize,
        arg_index: usize,
        path: Vec<StructuralPathStep>,
    },
    CallbackResult {
        param_index: usize,
        path: Vec<StructuralPathStep>,
    },
}
