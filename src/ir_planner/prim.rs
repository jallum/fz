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
        Prim::DestTupleBegin { .. } => t.any(),
        Prim::DestTupleSet { .. } => t.nil(),
        Prim::DestFreeze { dest, .. } => lookup(t, env, *dest),
        Prim::TupleField(v, i) => {
            let vt = lookup(t, env, *v);
            // Find the widest arity in v's tuple clauses that covers index i;
            // project that component. Falls back to any when there's no
            // matching tuple shape.
            let max_arity = t.max_tuple_arity(&vt);
            if (*i as usize) < max_arity {
                let comps = t.tuple_projections(&vt, max_arity);
                comps
                    .into_iter()
                    .nth(*i as usize)
                    .unwrap_or_else(|| t.any())
            } else {
                t.any()
            }
        }

        Prim::MakeList(els, tail) => {
            let mut elem = t.none();
            for v in els {
                let vy = lookup(t, env, *v);
                elem = t.union(elem, vy);
            }
            if let Some(tl) = tail {
                let tt = lookup(t, env, *tl);
                let tail_elem_ty = t.list_element_type(&tt);
                elem = t.union(elem, tail_elem_ty);
            }
            if els.is_empty() {
                t.list(elem)
            } else {
                t.non_empty_list(elem)
            }
        }
        Prim::DestListBegin { .. } => t.nil(),
        Prim::DestListCons { head, tail, .. } => {
            let mut elem = lookup(t, env, *head);
            if let Some(tl) = tail {
                let tt = lookup(t, env, *tl);
                let tail_elem = t.list_element_type(&tt);
                elem = t.union(elem, tail_elem);
            }
            t.non_empty_list(elem)
        }
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
        Prim::IsEmptyList(_) => t.bool(),

        Prim::MakeMap(entries) => {
            let mut fields: Vec<(MapKey, T::Ty)> = Vec::new();
            let mut all_static = true;
            for (k, v) in entries {
                let vy = lookup(t, env, *v);
                match var_as_map_key(t, *k, env) {
                    Some(mk) => {
                        fields.push((mk, vy));
                    }
                    None => {
                        all_static = false;
                        break;
                    }
                }
            }
            if all_static && !entries.is_empty() {
                t.map(&fields)
            } else if entries.is_empty() {
                t.map(&[])
            } else {
                t.map_top()
            }
        }
        Prim::DestMapBegin { base, .. } => {
            if let Some(base) = base {
                lookup(t, env, *base)
            } else {
                t.map(&[])
            }
        }
        Prim::DestMapPut { .. } => t.nil(),
        Prim::DestMapFreeze { map, .. } => lookup(t, env, *map),
        Prim::MapUpdate(base, entries) => {
            let mut dy = lookup(t, env, *base);
            for (k, v) in entries {
                let vt_ty = lookup(t, env, *v);
                if let Some(mk) = var_as_map_key(t, *k, env) {
                    dy = t.refine_map_field(&dy, &mk, &vt_ty);
                }
            }
            dy
        }
        Prim::MapGet(map, k) => {
            let mt = lookup(t, env, *map);
            // fz-swt.8 — `handle.value` on an opaque-typed handle.
            // When the subject is a singleton opaque and the key is
            // the atom `:value`, the typer answers with the inner
            // type T recorded for that opaque tag at alias
            // resolution. Visibility gating (declaring module vs
            // using module) is a *separate* concern surfaced in
            // `collect_diagnostics`; the lookup itself is unconditional
            // so out-of-module access reads its true T in the dead
            // path before the diagnostic fires.
            if let (Some(tag), Some(MapKey::Atom(key))) =
                (t.opaque_singleton(&mt), var_as_map_key(t, *k, env).as_ref())
                && key == "value"
                && let Some(inner) = m.opaque_inners.get(&tag)
            {
                return inner.clone();
            }
            let a = t.any();
            let n = t.nil();
            let fallback = t.union(a, n);
            if let Some(mk) = var_as_map_key(t, *k, env) {
                t.map_field_lookup(&mt, &mk).unwrap_or(fallback)
            } else {
                fallback
            }
        }
        Prim::MatcherMapGet(map, k) => {
            let mt = lookup(t, env, *map);
            let a = t.any();
            let n = t.nil();
            let fallback = t.union(a, n);
            if let Some(mk) = var_as_map_key(t, *k, env) {
                t.map_field_lookup(&mt, &mk).unwrap_or(fallback)
            } else {
                fallback
            }
        }
        Prim::IsMatcherMapMiss(_) => t.bool(),

        // fz-axu.1 (K0) — bitstring construction types as the binary/bitstring
        // top (`str_t()`). Branded subset types (e.g. `utf8`) will layer on top
        // of this in later tickets.
        Prim::MakeBitstring(_) => t.str_t(),
        Prim::ConstBitstring(_, _) => t.str_t(),

        Prim::MakeClosure(_, fn_id, captured) => {
            // fz-ul4.27.22.10 — type MakeClosure's result as a closure
            // literal: a singleton-typed arrow tagged with (fn_id,
            // capture_descrs). Downstream consumers (cont_slot0_descr,
            // codegen chain_repr / TailCallClosure lowering) read the lit
            // to resolve the body spec by exact-key lookup instead of
            // joining over the saturated arrow's return.
            let callee = m.fn_by_id(*fn_id);
            let entry = callee.block(callee.entry);
            let arity = entry.params.len();
            let n_caps = captured.len();
            let n_args = arity.saturating_sub(n_caps);
            let captures: Vec<T::Ty> = captured
                .iter()
                .map(|cv| env.get(cv).cloned().unwrap_or_else(|| t.any()))
                .collect();
            t.closure_lit((*fn_id).into(), captures, n_args)
        }

        Prim::Extern(eid, _) => {
            let ret_ty = m
                .extern_idx
                .get(eid)
                .map(|&i| m.externs[i].ret_descr.clone());
            ret_ty.unwrap_or_else(|| t.any())
        }

        Prim::TypeTest(v, descr) => {
            let vy = lookup(t, env, *v);
            // If vt ⊆ descr → always true; if vt ∩ descr = ∅ → always false;
            // otherwise unknown bool. Branch pruning in the typer's If-rewriting
            // pass then eliminates dead branches when the result is a singleton.
            if t.is_subtype(&vy, descr) {
                t.atom_lit("true")
            } else {
                let inter = t.intersect(vy, (**descr).clone());
                if t.is_empty(&inter) {
                    t.atom_lit("false")
                } else {
                    t.bool()
                }
            }
        }

        // fz-axu.4 (K3) — brand-mint. Take the source's structural type
        // and overlay `brands = {name}`. The result is a *minted brand
        // value*: its type carries both the brand tag (for nominal
        // identity / visibility) and the underlying structural axes (so
        // it remains usable as the underlying type wherever the K4 rule
        // grants `brand(name) ⊆ inner`). Pre-K4, the structural axes
        // alone keep it usable; the brand tag is just an extra label.
        Prim::Brand(v, name) => {
            let inner = lookup(t, env, *v);
            t.mint_brand(inner, name)
        }

        // Reader ops: conservative Top until later tickets refine.
        Prim::BitReaderInit(_) => t.any(),
        Prim::BitReadField { ty, .. } => {
            use crate::ast::BitType;
            // Returns Tuple([ok, value, new_reader]) on success, Tuple([false])
            // on failure. We over-approximate to a generic tuple shape; pattern
            // narrowing on TupleField then projects per-position. Field value
            // depends on the BitType.
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
        Prim::BitReaderDone(_) => t.bool(),
    }
}
