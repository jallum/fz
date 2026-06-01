use std::collections::{BTreeMap, BTreeSet};

use crate::types::ClosureTypes;

use super::model::ResolvedSpecMatch;
use super::{
    ResolvedSpec, ResolvedSpecSet, ResolvedTypeShape, SchemeInstantiation, SchemeMatch,
    StructuralCorrespondenceGroup, StructuralOccurrence, StructuralPathStep, instantiate_match,
};

pub(crate) fn spec_set_correspondence_groups(
    spec_set: &ResolvedSpecSet,
) -> Vec<StructuralCorrespondenceGroup> {
    let mut groups = BTreeSet::new();
    for spec in &spec_set.arrows {
        for group in spec_correspondence_groups(spec) {
            groups.insert(group);
        }
    }
    groups.into_iter().collect()
}

pub(crate) fn spec_correspondence_groups(
    spec: &ResolvedSpec,
) -> Vec<StructuralCorrespondenceGroup> {
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

    for (param_index, shape) in spec.param_shapes.iter().enumerate() {
        match shape {
            ResolvedTypeShape::Arrow { params, result } => {
                for (arg_index, arg) in params.iter().enumerate() {
                    walk_shape(arg, &mut path, &mut |var, shape_path| {
                        groups
                            .entry(var)
                            .or_default()
                            .insert(StructuralOccurrence::CallbackArg {
                                param_index,
                                arg_index,
                                path: shape_path,
                            });
                    });
                }
                walk_shape(result, &mut path, &mut |var, shape_path| {
                    groups
                        .entry(var)
                        .or_default()
                        .insert(StructuralOccurrence::CallbackResult {
                            param_index,
                            path: shape_path,
                        });
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

    walk_shape(&spec.result_shape, &mut path, &mut |var, shape_path| {
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

pub(crate) fn unique_matching_params<T>(
    t: &mut T,
    spec_set: &ResolvedSpecSet,
    arg_tys: &[crate::types::Ty],
) -> Option<Vec<crate::types::Ty>>
where
    T: ClosureTypes<Ty = crate::types::Ty>,
{
    match matching_arrows(t, spec_set, arg_tys).as_slice() {
        [matched] => Some(matched.params.clone()),
        _ => None,
    }
}

#[cfg(test)]
pub(crate) fn matching_result<T>(
    t: &mut T,
    spec_set: &ResolvedSpecSet,
    arg_tys: &[crate::types::Ty],
) -> Option<crate::types::Ty>
where
    T: ClosureTypes<Ty = crate::types::Ty>,
{
    let mut result = None;
    for matched in matching_arrows(t, spec_set, arg_tys) {
        result = Some(match result {
            Some(prev) => t.union(prev, matched.result),
            None => matched.result,
        });
    }
    result
}

fn matching_arrows<T>(
    t: &mut T,
    spec_set: &ResolvedSpecSet,
    arg_tys: &[crate::types::Ty],
) -> Vec<ResolvedSpecMatch>
where
    T: ClosureTypes<Ty = crate::types::Ty>,
{
    spec_set
        .arrows
        .iter()
        .filter_map(|spec| instantiate_matching_arrow(t, spec, arg_tys))
        .collect()
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
