//! Display helpers for interned descriptors.

use super::MapKey;
use super::TyCtx;
use super::bits::BASIC_NAMES;
use super::conj::Conj;
use super::descr::Descr;
use super::lit_set::LiteralSet;
use super::sigs::{ArrowSig, ListSig, MapSig, ResourceSig, TupleSig};

pub(crate) fn display(cx: TyCtx<'_>, d: &Descr) -> String {
    if d.looks_empty() {
        return "none".to_string();
    }
    if d.looks_full() {
        return "any".to_string();
    }
    let mut parts = Vec::new();
    for (bit, name) in BASIC_NAMES {
        if d.basic.contains_all(*bit) {
            parts.push((*name).to_string());
        }
    }
    append_axis(&mut parts, &d.atoms, "atom", |s| format!(":{}", s));
    append_axis(&mut parts, &d.opaques, "opaque", Clone::clone);
    append_axis(&mut parts, &d.brands, "brand", Clone::clone);
    append_axis(&mut parts, &d.vars, "var", |id| id.to_string());
    parts.extend(d.tuples.iter().map(|c| format_tuple_clause(cx, c)));
    parts.extend(d.lists.iter().map(|c| format_list_clause(cx, c)));
    parts.extend(d.resources.iter().map(|c| format_resource_clause(cx, c)));
    parts.extend(d.funcs.iter().map(|c| format_arrow_clause(cx, c)));
    parts.extend(d.maps.iter().map(|c| format_map_clause(cx, c)));
    parts.join(" | ")
}

pub(crate) fn display_for_diag(cx: TyCtx<'_>, d: &Descr) -> String {
    display(cx, d)
}

fn append_axis<T, F>(parts: &mut Vec<String>, set: &LiteralSet<T>, top_name: &str, render: F)
where
    T: Ord + Clone,
    F: Fn(&T) -> String,
{
    if set.is_none() {
        return;
    }
    if set.is_any() {
        parts.push(top_name.to_string());
        return;
    }
    let rendered: Vec<String> = set.set.iter().map(render).collect();
    if set.cofinite {
        parts.push(format!("not({})", rendered.join(" | ")));
    } else {
        parts.push(rendered.join(" | "));
    }
}

fn format_tuple_clause(cx: TyCtx<'_>, c: &Conj<TupleSig>) -> String {
    format_conj(c, |sig| {
        let elems: Vec<String> = sig.elems.iter().map(|ty| display(cx, cx.descr(ty))).collect();
        format!("{{{}}}", elems.join(", "))
    })
}

fn format_list_clause(cx: TyCtx<'_>, c: &Conj<ListSig>) -> String {
    format_conj(c, |sig| match (sig.empty, sig.elem) {
        (true, None) => "[]".to_string(),
        (_, Some(elem)) => format!("[{}]", display(cx, cx.descr(&elem))),
        (false, None) => "nonempty([])".to_string(),
    })
}

fn format_resource_clause(cx: TyCtx<'_>, c: &Conj<ResourceSig>) -> String {
    format_conj(c, |sig| format!("resource({})", display(cx, cx.descr(&sig.payload))))
}

fn format_arrow_clause(cx: TyCtx<'_>, c: &Conj<ArrowSig>) -> String {
    format_conj(c, |sig| {
        let args: Vec<String> = sig.args.iter().map(|ty| display(cx, cx.descr(ty))).collect();
        let base = format!("({}) -> {}", args.join(", "), display(cx, cx.descr(&sig.ret)));
        match &sig.lit {
            Some(lit) => format!("{}#{}", base, lit.fn_id.0),
            None => base,
        }
    })
}

fn format_map_clause(cx: TyCtx<'_>, c: &Conj<MapSig>) -> String {
    format_conj(c, |sig| {
        let fields: Vec<String> = sig
            .fields
            .iter()
            .map(|(k, v)| format!("{}: {}", format_map_key(k), display(cx, cx.descr(v))))
            .collect();
        format!("%{{{}}}", fields.join(", "))
    })
}

fn format_conj<T, F>(c: &Conj<T>, render: F) -> String
where
    F: Fn(&T) -> String,
{
    if c.pos.is_empty() && c.neg.is_empty() {
        return "any".to_string();
    }
    let mut parts: Vec<String> = c.pos.iter().map(&render).collect();
    parts.extend(c.neg.iter().map(|sig| format!("not({})", render(sig))));
    parts.join(" & ")
}

fn format_map_key(k: &MapKey) -> String {
    match k {
        MapKey::Atom(name) => format!(":{}", name),
        MapKey::Int(n) => n.to_string(),
    }
}
