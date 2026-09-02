//! Display helpers for interned descriptors.

use super::CallableValueKind;
use super::MapKey;
use super::TyCtx;
use super::bits::BASIC_NAMES;
use super::conj::Conj;
use super::descr::Descr;
use super::sigs::{ArrowSig, ListSig, MapSig, ResourceSig, TupleSig};
use crate::finite_set::FiniteSet;

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
    append_axis(&mut parts, &d.vars, "var", |id| cx.render_var(*id));
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

fn append_axis<T, F>(parts: &mut Vec<String>, set: &FiniteSet<T>, top_name: &str, render: F)
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
    let rendered: Vec<String> = set.values.iter().map(render).collect();
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
            Some(lit) => format_closure_lit_suffix(cx, &base, lit),
            None => base,
        }
    })
}

/// Render a `ClosureLit`-bearing arrow's suffix so that distinct `ClosureLit`
/// identities (which differ by `kind`, `fn_id`, and/or elementwise `captures`
/// — see `ClosureLit`'s doc comment in `sigs.rs`) never collide on the same
/// rendered string.
///
/// `kind = FnRef` clauses always carry empty `captures` (a `ClosureLit`
/// invariant), so the plain `#{fn_id}` suffix stays as it was — this keeps
/// the overwhelmingly common case (a bare function reference) readable and
/// unchanged. It is also why a `FnRef` literal is never ANONYMOUS: the erasure
/// drops a capture-free literal whole instead of anonymising it, so the `#?` an
/// erased brand renders as only ever appears in front of a `closure[...]`
/// tail. `kind = Closure` clauses additionally render their captures
/// structurally (never as raw interner ids) behind a `closure[...]` tag, so a
/// `Closure` lit can never collide with a `FnRef` lit on the same `fn_id`,
/// and two `Closure` lits on the same `fn_id` collide only if their captures
/// also render identically.
fn format_closure_lit_suffix(cx: TyCtx<'_>, base: &str, lit: &super::sigs::ClosureLit) -> String {
    let head = match lit.fn_id {
        Some(fn_id) => format!("{}#{}", base, fn_id.0),
        None => format!("{base}#?"),
    };
    match lit.kind {
        CallableValueKind::FnRef => head,
        CallableValueKind::Closure => {
            let caps: Vec<String> = lit.captures.iter().map(|ty| display(cx, cx.descr(ty))).collect();
            format!("{}closure[{}]", head, caps.join(", "))
        }
    }
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
