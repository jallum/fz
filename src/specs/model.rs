use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::modules::identity::ModuleName;
use crate::types::ClosureTypes;

use super::{SchemeInstantiation, SchemeMatch, instantiate_match};

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

impl ResolvedSpecSet {
    pub(crate) fn structural_correspondence_groups(&self) -> Vec<StructuralCorrespondenceGroup> {
        let mut groups = BTreeSet::new();
        for spec in &self.arrows {
            for group in spec.structural_correspondence_groups() {
                groups.insert(group);
            }
        }
        groups.into_iter().collect()
    }

    pub(crate) fn matching_arrows<T>(
        &self,
        t: &mut T,
        arg_tys: &[crate::types::Ty],
    ) -> Vec<ResolvedSpecMatch>
    where
        T: ClosureTypes<Ty = crate::types::Ty>,
    {
        self.arrows
            .iter()
            .filter_map(|spec| instantiate_matching_arrow(t, spec, arg_tys))
            .collect()
    }

    pub(crate) fn unique_matching_params<T>(
        &self,
        t: &mut T,
        arg_tys: &[crate::types::Ty],
    ) -> Option<Vec<crate::types::Ty>>
    where
        T: ClosureTypes<Ty = crate::types::Ty>,
    {
        match self.matching_arrows(t, arg_tys).as_slice() {
            [matched] => Some(matched.params.clone()),
            _ => None,
        }
    }

    #[cfg(test)]
    pub(crate) fn matching_result<T>(
        &self,
        t: &mut T,
        arg_tys: &[crate::types::Ty],
    ) -> Option<crate::types::Ty>
    where
        T: ClosureTypes<Ty = crate::types::Ty>,
    {
        let mut result = None;
        for matched in self.matching_arrows(t, arg_tys) {
            result = Some(match result {
                Some(prev) => t.union(prev, matched.result),
                None => matched.result,
            });
        }
        result
    }
}

impl ResolvedSpec {
    pub(crate) fn structural_correspondence_groups(&self) -> Vec<StructuralCorrespondenceGroup> {
        fn walk_shape(
            shape: &ResolvedTypeShape,
            path: &mut Vec<StructuralPathStep>,
            emit: &mut impl FnMut(crate::types::TypeVarId, Vec<StructuralPathStep>),
        ) {
            match shape {
                ResolvedTypeShape::Var(var) => emit(*var, path.clone()),
                ResolvedTypeShape::Named { args, .. } => {
                    for (idx, arg) in args.iter().enumerate() {
                        path.push(StructuralPathStep::NamedArg(idx));
                        walk_shape(arg, path, emit);
                        path.pop();
                    }
                }
                ResolvedTypeShape::Resource(inner) => {
                    path.push(StructuralPathStep::ResourceInner);
                    walk_shape(inner, path, emit);
                    path.pop();
                }
                ResolvedTypeShape::List(inner) => {
                    path.push(StructuralPathStep::ListElem);
                    walk_shape(inner, path, emit);
                    path.pop();
                }
                ResolvedTypeShape::Tuple(elems) | ResolvedTypeShape::Union(elems) => {
                    for (idx, elem) in elems.iter().enumerate() {
                        path.push(match shape {
                            ResolvedTypeShape::Tuple(_) => StructuralPathStep::TupleElem(idx),
                            ResolvedTypeShape::Union(_) => StructuralPathStep::UnionMember(idx),
                            _ => unreachable!(),
                        });
                        walk_shape(elem, path, emit);
                        path.pop();
                    }
                }
                ResolvedTypeShape::Arrow { params, result } => {
                    for (idx, param) in params.iter().enumerate() {
                        path.push(StructuralPathStep::ArrowParam(idx));
                        walk_shape(param, path, emit);
                        path.pop();
                    }
                    path.push(StructuralPathStep::ArrowResult);
                    walk_shape(result, path, emit);
                    path.pop();
                }
                ResolvedTypeShape::StructRecord { fields, .. } => {
                    for field in fields {
                        path.push(StructuralPathStep::StructField(field.name.clone()));
                        walk_shape(&field.ty, path, emit);
                        path.pop();
                    }
                }
                ResolvedTypeShape::Any
                | ResolvedTypeShape::Never
                | ResolvedTypeShape::Nil
                | ResolvedTypeShape::Bool
                | ResolvedTypeShape::Integer
                | ResolvedTypeShape::Float
                | ResolvedTypeShape::CPointer
                | ResolvedTypeShape::Binary
                | ResolvedTypeShape::Atom
                | ResolvedTypeShape::Utf8
                | ResolvedTypeShape::Pid
                | ResolvedTypeShape::Ref
                | ResolvedTypeShape::AtomLit(_)
                | ResolvedTypeShape::IntLit(_)
                | ResolvedTypeShape::FloatLit(_) => {}
            }
        }

        let mut groups: BTreeMap<crate::types::TypeVarId, BTreeSet<StructuralOccurrence>> =
            BTreeMap::new();
        let mut path = Vec::new();

        for (param_index, shape) in self.param_shapes.iter().enumerate() {
            match shape {
                ResolvedTypeShape::Arrow { params, result } => {
                    for (arg_index, arg) in params.iter().enumerate() {
                        walk_shape(arg, &mut path, &mut |var, shape_path| {
                            groups.entry(var).or_default().insert(
                                StructuralOccurrence::CallbackArg {
                                    param_index,
                                    arg_index,
                                    path: shape_path,
                                },
                            );
                        });
                    }
                    walk_shape(result, &mut path, &mut |var, shape_path| {
                        groups.entry(var).or_default().insert(
                            StructuralOccurrence::CallbackResult {
                                param_index,
                                path: shape_path,
                            },
                        );
                    });
                }
                _ => walk_shape(shape, &mut path, &mut |var, shape_path| {
                    groups
                        .entry(var)
                        .or_default()
                        .insert(StructuralOccurrence::Param {
                            param_index,
                            path: shape_path,
                        });
                }),
            }
        }

        walk_shape(&self.result_shape, &mut path, &mut |var, shape_path| {
            groups
                .entry(var)
                .or_default()
                .insert(StructuralOccurrence::Result { path: shape_path });
        });

        groups
            .into_iter()
            .filter_map(|(var, occurrences)| {
                (occurrences.len() > 1).then_some(StructuralCorrespondenceGroup {
                    var,
                    occurrences: occurrences.into_iter().collect(),
                })
            })
            .collect()
    }
}

fn instantiate_matching_arrow<T>(
    t: &mut T,
    spec: &ResolvedSpec,
    arg_tys: &[crate::types::Ty],
) -> Option<ResolvedSpecMatch>
where
    T: ClosureTypes<Ty = crate::types::Ty>,
{
    match instantiate_match(t, &spec.params, &spec.result, &spec.constraints, arg_tys) {
        SchemeInstantiation::Known(SchemeMatch { params, result }) => {
            Some(ResolvedSpecMatch { params, result })
        }
        SchemeInstantiation::Underconstrained(_) | SchemeInstantiation::Invalid => None,
    }
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
