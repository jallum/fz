use super::expr_types::{
    lookup, numeric_result, numeric_result_fold, type_binop, type_const, var_as_map_key,
};
use crate::fz_ir::{BinOp, Module, Prim, UnOp, Var};
use crate::types::MapKey;
use std::collections::{HashMap, HashSet};

pub(crate) fn type_prim<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    prim: &Prim,
    env: &HashMap<Var, crate::types::Ty>,
    m: &Module,
    const_vars: &HashSet<Var>,
) -> T::Ty {
    match prim {
        Prim::Const(c) => type_const(t, c, &m.atom_names),

        Prim::BinOp(op, a, b) => {
            let at = lookup(t, env, *a);
            let bt = lookup(t, env, *b);
            let fold = const_vars.contains(a) && const_vars.contains(b);
            type_binop(t, *op, &at, &bt, fold)
        }
        Prim::UnOp(op, v) => {
            let vt = lookup(t, env, *v);
            match op {
                UnOp::Neg => {
                    if const_vars.contains(v) {
                        let zero = t.int_lit(0);
                        numeric_result_fold(t, BinOp::Sub, &zero, &vt)
                    } else {
                        numeric_result(t, &vt, &vt)
                    }
                }
                UnOp::Not => t.bool(),
            }
        }

        Prim::MakeTuple(vs) => {
            let elem_tys: Vec<T::Ty> = vs.iter().map(|v| lookup(t, env, *v)).collect();
            t.tuple(&elem_tys)
        }
        Prim::MakeStruct { module, .. } => crate::frontend::protocols::struct_impl_target_type(
            t,
            module.rsplit('.').next().unwrap_or(module),
        ),
        Prim::DestTupleBegin { .. } => t.any(),
        Prim::DestTupleSet { .. } => t.nil(),
        Prim::DestFreeze { dest, .. } => lookup(t, env, *dest),
        Prim::TupleField(v, i) => type_tuple_field(t, env, *v, *i),
        Prim::StructField(v, field) => type_struct_field(t, env, m, *v, field),

        Prim::MakeList(els, tail) => type_make_list(t, env, els, *tail),
        Prim::DestListBegin { .. } => t.nil(),
        Prim::DestListCons { head, tail, .. } => type_dest_list_cons(t, env, *head, *tail),
        Prim::DestListFreeze { list, .. } => lookup(t, env, *list),
        Prim::ListHead(l) => {
            let dy = lookup(t, env, *l);
            t.list_element_type(&dy)
        }
        Prim::ListTail(l) => {
            // The tail of a non-empty list is a list, possibly empty, with
            // the same element evidence as the input list.
            let lt = lookup(t, env, *l);
            let elem_ty = t.list_element_type(&lt);
            t.list(elem_ty)
        }
        Prim::IsEmptyList(_) | Prim::IsListCons(_) => t.bool(),

        Prim::MakeMap(entries) => type_make_map(t, env, entries),
        Prim::DestMapBegin { base, .. } => {
            if let Some(base) = base {
                lookup(t, env, *base)
            } else {
                t.map(&[])
            }
        }
        Prim::DestMapPut { .. } => t.nil(),
        Prim::DestMapFreeze { map, .. } => lookup(t, env, *map),
        Prim::MapUpdate(base, entries) => type_map_update(t, env, *base, entries),
        Prim::MapGet(map, k) => type_map_get(t, env, m, *map, *k, true),
        Prim::MatcherMapGet(map, k) => type_map_get(t, env, m, *map, *k, false),
        Prim::IsMatcherMapMiss(_) => t.bool(),

        // Raw bitstring constructors type as the binary/bitstring top.
        Prim::MakeBitstring(_) => t.str_t(),
        Prim::ConstBitstring(_, _) => t.str_t(),

        Prim::MakeClosure(_, fn_id, captured) => type_make_closure(t, env, m, *fn_id, captured),

        Prim::Extern(_, eid, _) => {
            let ret_ty = m
                .extern_idx
                .get(eid)
                .map(|&i| m.externs[i].ret_descr.clone());
            ret_ty.unwrap_or_else(|| t.any())
        }

        Prim::TypeTest(v, descr) => type_type_test(t, env, *v, descr),

        // Preserve the source's structural axes and add the brand tag.
        Prim::Brand(v, name) => {
            let inner = lookup(t, env, *v);
            t.mint_brand(inner, name)
        }

        Prim::BitReaderInit(_) => t.any(),
        Prim::BitReadField { ty, .. } => type_bit_read_field(t, ty),
        Prim::BitReaderDone(_) => t.bool(),
    }
}

fn type_tuple_field<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    env: &HashMap<Var, crate::types::Ty>,
    v: Var,
    i: u32,
) -> crate::types::Ty {
    let vt = lookup(t, env, v);
    let max_arity = t.max_tuple_arity(&vt);
    if (i as usize) < max_arity {
        let comps = t.tuple_projections(&vt, max_arity);
        comps.into_iter().nth(i as usize).unwrap_or_else(|| t.any())
    } else {
        t.any()
    }
}

fn type_struct_field<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    env: &HashMap<Var, crate::types::Ty>,
    m: &Module,
    v: Var,
    field: &str,
) -> crate::types::Ty {
    let vt = lookup(t, env, v);
    let Some(tag) = t.opaque_singleton(&vt) else {
        return t.any();
    };
    let Some(order) = struct_schema_for_impl_target(m, &tag) else {
        return t.any();
    };
    let Some(index) = order.iter().position(|name| name == field) else {
        return t.any();
    };
    let Some(inner) = m.opaque_inners.get(&tag).cloned() else {
        return t.any();
    };
    let comps = t.tuple_projections(&inner, order.len());
    comps.into_iter().nth(index).unwrap_or_else(|| t.any())
}

fn struct_schema_for_impl_target<'a>(m: &'a Module, tag: &str) -> Option<&'a Vec<String>> {
    let target = tag.strip_prefix("impl-target::")?;
    let mut matches = m
        .struct_schemas
        .iter()
        .filter(|(name, _fields)| name.rsplit('.').next().unwrap_or(name.as_str()) == target)
        .map(|(_name, fields)| fields);
    let fields = matches.next()?;
    matches.next().is_none().then_some(fields)
}

fn type_make_list<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    env: &HashMap<Var, crate::types::Ty>,
    els: &[Var],
    tail: Option<Var>,
) -> crate::types::Ty {
    let mut elem = t.none();
    for v in els {
        let vy = lookup(t, env, *v);
        elem = t.union(elem, vy);
    }
    if let Some(tl) = tail {
        let tt = lookup(t, env, tl);
        let tail_elem_ty = t.list_element_type(&tt);
        elem = t.union(elem, tail_elem_ty);
    }
    if els.is_empty() {
        t.list(elem)
    } else {
        t.non_empty_list(elem)
    }
}

fn type_dest_list_cons<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    env: &HashMap<Var, crate::types::Ty>,
    head: Var,
    tail: Option<Var>,
) -> crate::types::Ty {
    let mut elem = lookup(t, env, head);
    if let Some(tl) = tail {
        let tt = lookup(t, env, tl);
        let tail_elem = t.list_element_type(&tt);
        elem = t.union(elem, tail_elem);
    }
    t.non_empty_list(elem)
}

fn type_make_map<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    env: &HashMap<Var, crate::types::Ty>,
    entries: &[(Var, Var)],
) -> crate::types::Ty {
    let mut fields: Vec<(MapKey, T::Ty)> = Vec::new();
    for (k, v) in entries {
        let Some(mk) = var_as_map_key(t, *k, env) else {
            return t.map_top();
        };
        let vy = lookup(t, env, *v);
        fields.push((mk, vy));
    }
    t.map(&fields)
}

fn type_map_update<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    env: &HashMap<Var, crate::types::Ty>,
    base: Var,
    entries: &[(Var, Var)],
) -> crate::types::Ty {
    let mut dy = lookup(t, env, base);
    for (k, v) in entries {
        let vt_ty = lookup(t, env, *v);
        if let Some(mk) = var_as_map_key(t, *k, env) {
            dy = t.refine_map_field(&dy, &mk, &vt_ty);
        }
    }
    dy
}

fn type_map_get<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    env: &HashMap<Var, crate::types::Ty>,
    m: &Module,
    map: Var,
    key_v: Var,
    allow_opaque_value: bool,
) -> crate::types::Ty {
    let mt = lookup(t, env, map);
    if allow_opaque_value && let Some(inner) = opaque_value_inner(t, env, m, &mt, key_v) {
        return inner;
    }
    let a = t.any();
    let n = t.nil();
    let fallback = t.union(a, n);
    if let Some(mk) = var_as_map_key(t, key_v, env) {
        t.map_field_lookup(&mt, &mk).unwrap_or(fallback)
    } else {
        fallback
    }
}

fn opaque_value_inner<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    env: &HashMap<Var, crate::types::Ty>,
    m: &Module,
    mt: &crate::types::Ty,
    key_v: Var,
) -> Option<crate::types::Ty> {
    let tag = t.opaque_singleton(mt)?;
    let Some(MapKey::Atom(key)) = var_as_map_key(t, key_v, env) else {
        return None;
    };
    (key == "value")
        .then(|| m.opaque_inners.get(&tag).cloned())
        .flatten()
}

fn type_make_closure<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes>(
    t: &mut T,
    env: &HashMap<Var, crate::types::Ty>,
    m: &Module,
    fn_id: crate::fz_ir::FnId,
    captured: &[Var],
) -> crate::types::Ty {
    let callee = m.fn_by_id(fn_id);
    let entry = callee.block(callee.entry);
    let n_args = entry.params.len().saturating_sub(captured.len());
    let captures: Vec<T::Ty> = captured
        .iter()
        .map(|cv| env.get(cv).cloned().unwrap_or_else(|| t.any()))
        .collect();
    t.closure_lit(fn_id.into(), captures, n_args)
}

fn type_type_test<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    env: &HashMap<Var, crate::types::Ty>,
    v: Var,
    descr: &crate::types::Ty,
) -> crate::types::Ty {
    let vy = lookup(t, env, v);
    if t.is_subtype(&vy, descr) {
        return t.atom_lit("true");
    }
    let inter = t.intersect(vy, descr.clone());
    if t.is_empty(&inter) {
        t.atom_lit("false")
    } else {
        t.bool()
    }
}

fn type_bit_read_field<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    ty: &crate::ast::BitType,
) -> crate::types::Ty {
    use crate::ast::BitType;
    let value_t = match ty {
        BitType::Integer | BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => t.int(),
        BitType::Float => t.float(),
        BitType::Binary | BitType::Bits => t.str_t(),
    };
    let bool1 = t.bool();
    let any_ty = t.any();
    let success = t.tuple(&[bool1, value_t, any_ty]);
    let bool2 = t.bool();
    let failure = t.tuple(&[bool2]);
    t.union(success, failure)
}
