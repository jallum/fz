use std::collections::HashMap;

use crate::modules::identity::ModuleName;

/// Resolved form of a `SpecDecl` after type-expression lookup. The
/// type-expression layer constructs this model; spec consumers own the
/// semantic operations over it.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub(crate) struct ResolvedSpec {
    pub params: Vec<crate::types::Ty>,
    #[serde(default)]
    pub param_shapes: Vec<ResolvedTypeShape>,
    pub result: crate::types::Ty,
    #[serde(default)]
    pub result_shape: ResolvedTypeShape,
    /// `TypeVarId` is a `u32` newtype, which serde_json renders as a number,
    /// not a valid object key, so this map serializes as a sequence of
    /// `(TypeVarId, Ty)` entries.
    #[serde(with = "constraints_as_seq")]
    pub constraints: HashMap<crate::types::TypeVarId, crate::types::Ty>,
}

#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
pub(crate) struct ResolvedSpecSet {
    pub arrows: Vec<ResolvedSpec>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ResolvedSpecMatch {
    pub params: Vec<crate::types::Ty>,
    pub result: crate::types::Ty,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct StructuralCorrespondenceGroup {
    pub var: crate::types::TypeVarId,
    pub occurrences: Vec<StructuralOccurrence>,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize, Default)]
pub(crate) struct ResolvedStructFieldShape {
    pub name: String,
    pub ty: ResolvedTypeShape,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize, Default)]
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
    Var(crate::types::TypeVarId),
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
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

/// (De)serialize `HashMap<TypeVarId, Ty>` as a `Vec<(TypeVarId, Ty)>` so the
/// numeric key survives serde_json, which forbids non-string object keys.
mod constraints_as_seq {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use std::collections::HashMap;

    type Constraints = HashMap<crate::types::TypeVarId, crate::types::Ty>;

    pub fn serialize<S: Serializer>(map: &Constraints, s: S) -> Result<S::Ok, S::Error> {
        map.iter().collect::<Vec<_>>().serialize(s)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Constraints, D::Error> {
        Ok(
            Vec::<(crate::types::TypeVarId, crate::types::Ty)>::deserialize(d)?
                .into_iter()
                .collect(),
        )
    }
}
