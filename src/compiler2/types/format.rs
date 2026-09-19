//! Display helpers for interned descriptors.

use super::bits::BASIC_NAMES;
use super::conj::Conj;
use super::descr::Descr;
use super::render_bindings::{BindingVisit, RenderBindings};
use super::sigs::{ArrowSig, ListSig, MapSig, MapTag, ResourceSig, TupleSig};
use super::{CallableValueKind, MapKey, Ty, TyCtx};
use crate::finite_set::FiniteSet;

pub(crate) fn display(cx: TyCtx<'_>, ty: Ty) -> String {
    TypeDisplay {
        cx,
        bindings: RenderBindings::default(),
    }
    .body(ty)
}

/// A brand is a REFINEMENT of the structure beside it, not another member of
/// the union: `utf8(binary)` says "one of the binaries", where `binary | utf8`
/// would read as a supertype of `binary`. An unconstrained slot is the
/// unbranded case and adds nothing.
///
/// The one renderer for the slot: `display` here and `TyCanon`'s body both
/// call it, so the two surfaces cannot drift. `brands.values` is a `BTreeSet`,
/// so the name order is already deterministic.
pub(super) fn brand_refinement(brands: &FiniteSet<String>, body: String) -> String {
    if brands.is_any() {
        return body;
    }
    if brands.is_none() {
        return "none".to_string();
    }
    let names: Vec<&str> = brands.values.iter().map(String::as_str).collect();
    let joined = names.join(" | ");
    match (brands.cofinite, names.len()) {
        (true, _) => format!("not({joined})({body})"),
        (false, 1) => format!("{joined}({body})"),
        (false, _) => format!("({joined})({body})"),
    }
}

pub(crate) fn display_for_diag(cx: TyCtx<'_>, ty: Ty) -> String {
    display(cx, ty)
}

struct TypeDisplay<'a> {
    cx: TyCtx<'a>,
    bindings: RenderBindings,
}

impl TypeDisplay<'_> {
    fn body(&mut self, ty: Ty) -> String {
        match self.bindings.enter(ty) {
            BindingVisit::Reference(name) => name,
            BindingVisit::Fresh => {
                let body = self.descr(self.cx.descr(&ty));
                self.bindings.finish(ty, body)
            }
        }
    }

    fn descr(&mut self, d: &Descr) -> String {
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
        append_axis(&mut parts, &d.atoms, "atom", |s| format!(":{s}"));
        append_axis(&mut parts, &d.opaques, "opaque", ToString::to_string);
        append_axis(&mut parts, &d.vars, "var", |id| self.cx.render_var(*id));
        parts.extend(d.tuples.iter().map(|c| self.tuple_clause(c)));
        parts.extend(d.lists.iter().map(|c| self.list_clause(c)));
        parts.extend(d.resources.iter().map(|c| self.resource_clause(c)));
        parts.extend(d.funcs.iter().map(|c| self.arrow_clause(c)));
        parts.extend(d.maps.iter().map(|c| self.map_clause(c)));
        brand_refinement(&d.brands, parts.join(" | "))
    }

    fn tuple_clause(&mut self, c: &Conj<TupleSig>) -> String {
        format_conj(c, "tuple", |sig| {
            let elems = sig.elems.iter().map(|ty| self.body(*ty)).collect::<Vec<_>>();
            format!("{{{}}}", elems.join(", "))
        })
    }

    fn list_clause(&mut self, c: &Conj<ListSig>) -> String {
        format_conj(c, "[any]", |sig| match (sig.empty, sig.elem) {
            (true, None) => "[]".to_string(),
            (_, Some(elem)) => format!("[{}]", self.body(elem)),
            (false, None) => "nonempty([])".to_string(),
        })
    }

    fn resource_clause(&mut self, c: &Conj<ResourceSig>) -> String {
        format_conj(c, "resource(any)", |sig| {
            format!("resource({})", self.body(sig.payload))
        })
    }

    fn arrow_clause(&mut self, c: &Conj<ArrowSig>) -> String {
        format_conj(c, "fun", |sig| {
            let args = sig.args.iter().map(|ty| self.body(*ty)).collect::<Vec<_>>();
            let base = format!("({}) -> {}", args.join(", "), self.body(sig.ret));
            match &sig.lit {
                Some(lit) => self.closure_lit_suffix(&base, lit),
                None => base,
            }
        })
    }

    fn closure_lit_suffix(&mut self, base: &str, lit: &super::sigs::ClosureLit) -> String {
        let head = match lit.fn_id {
            Some(fn_id) => format!("{base}#{}", fn_id.0),
            None => format!("{base}#?"),
        };
        match lit.kind {
            CallableValueKind::FnRef => head,
            CallableValueKind::Closure => {
                let caps = lit.captures.iter().map(|ty| self.body(*ty)).collect::<Vec<_>>();
                format!("{}closure[{}]", head, caps.join(", "))
            }
        }
    }

    fn map_clause(&mut self, c: &Conj<MapSig>) -> String {
        format_conj(c, "map", |sig| {
            let fields = sig
                .fields
                .iter()
                .map(|(key, value)| format!("{}: {}", map_key(key), self.body(*value)))
                .collect::<Vec<_>>();
            match &sig.tag {
                MapTag::Plain => format!("%{{{}}}", fields.join(", ")),
                MapTag::Struct(tag) => format!("%{}{{{}}}", tag.name, fields.join(", ")),
            }
        })
    }
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
    let rendered = set.values.iter().map(render).collect::<Vec<_>>();
    if set.cofinite {
        parts.push(format!("not({})", rendered.join(" | ")));
    } else {
        parts.push(rendered.join(" | "));
    }
}

fn format_conj<T>(c: &Conj<T>, top: &str, mut render: impl FnMut(&T) -> String) -> String {
    if c.pos.is_empty() && c.neg.is_empty() {
        return top.to_string();
    }
    let mut parts = c.pos.iter().map(&mut render).collect::<Vec<_>>();
    parts.extend(c.neg.iter().map(|sig| format!("not({})", render(sig))));
    parts.join(" & ")
}

fn map_key(key: &MapKey) -> String {
    match key {
        MapKey::Atom(name) => format!(":{name}"),
        MapKey::Int(number) => number.to_string(),
    }
}
