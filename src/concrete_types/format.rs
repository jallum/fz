//! `Display`/`Debug` for `Descr` and the per-clause/per-sig formatter helpers.

use std::fmt;

use crate::types::MapKey;

use super::bits::BASIC_NAMES;
use super::conj::Conj;
use super::descr::Descr;
use super::lit_set::{AtomSet, LiteralSet};
use super::sigs::{ArrowSig, ListSig, MapSig, TupleSig};
use super::ty_descr;

impl fmt::Display for Descr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.looks_full() {
            return write!(f, "any");
        }
        if self.looks_empty() {
            return write!(f, "none");
        }

        let mut parts: Vec<String> = Vec::new();

        for (bit, name) in BASIC_NAMES {
            if self.basic.contains_all(*bit) {
                parts.push((*name).to_string());
            }
        }

        format_lit_set(&mut parts, &self.ints, "int", |n| format!("{}", n));
        format_lit_set(&mut parts, &self.floats, "float", |f| {
            let v = f.get();
            if v.fract() == 0.0 {
                format!("{:.1}", v)
            } else {
                format!("{}", v)
            }
        });
        // fz-yan.3 — the reserved atoms render without the `:` sigil to
        // preserve the conventional `nil`/`true`/`false` rendering and
        // collapse `:true | :false` to `bool` for `Descr::bool_t()`.
        if let Some(s) = render_reserved_atom_set(&self.atoms) {
            parts.push(s);
        } else {
            format_lit_set(&mut parts, &self.atoms, "atom", |a| format!(":{}", a));
        }
        format_lit_set(&mut parts, &self.opaques, "opaque", |n| n.clone());
        // fz-axu.2 (K1) — brands render as `brand <name>` (singular) or
        // `brand <name1> | brand <name2>` (multi). Matches the user-facing
        // `refines` declaration syntax conceptually; tests rely on it.
        format_lit_set(&mut parts, &self.brands, "brand", |n| n.clone());
        // fz-try.5 — render type variables as `α<id>`. A per-signature
        // greek-letter remap (α, β, γ, …) lands in fz-try.11 (formatter).
        format_lit_set(&mut parts, &self.vars, "var", |v| format!("{}", v));

        for c in &self.tuples {
            parts.push(format_tuple_clause(c));
        }
        for c in &self.lists {
            parts.push(format_list_clause(c));
        }
        for c in &self.funcs {
            parts.push(format_arrow_clause(c));
        }
        for c in &self.maps {
            parts.push(format_map_clause(c));
        }

        write!(f, "{}", parts.join(" | "))
    }
}

pub(crate) fn format_lit_set_capped<T: Ord + Clone>(
    parts: &mut Vec<String>,
    s: &LiteralSet<T>,
    top_name: &str,
    cap: usize,
    fmt_one: impl Fn(&T) -> String,
) {
    if s.is_none() {
        return;
    }
    if s.cofinite {
        if s.set.is_empty() {
            parts.push(top_name.into());
        } else {
            let mut exc: Vec<String> = s.set.iter().take(cap).map(&fmt_one).collect();
            if s.set.len() > cap {
                exc.push(format!("… (+{} more)", s.set.len() - cap));
            }
            parts.push(format!("{} \\ {{{}}}", top_name, exc.join(", ")));
        }
    } else {
        let mut iter = s.set.iter();
        for v in iter.by_ref().take(cap) {
            parts.push(fmt_one(v));
        }
        let rest = iter.count();
        if rest > 0 {
            parts.push(format!("… (+{} more)", rest));
        }
    }
}

impl fmt::Debug for Descr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

/// fz-yan.3 — render `AtomSet`s containing only reserved atom literals
/// (`nil`, `true`, `false`) with bareword/`bool` forms instead of the
/// generic `:atom` syntax. Returns `None` if the set contains any other
/// atom name (or is `cofinite`); the caller falls back to the generic
/// renderer.
pub(crate) fn render_reserved_atom_set(s: &AtomSet) -> Option<String> {
    if s.is_none() || s.is_any() || s.cofinite {
        return None;
    }
    let mut has_nil = false;
    let mut has_true = false;
    let mut has_false = false;
    let mut other = false;
    for name in &s.set {
        match name.as_str() {
            "nil" => has_nil = true,
            "true" => has_true = true,
            "false" => has_false = true,
            _ => other = true,
        }
    }
    if other {
        return None;
    }
    let mut parts: Vec<&str> = Vec::new();
    if has_nil {
        parts.push("nil");
    }
    if has_true && has_false {
        parts.push("bool");
    } else if has_true {
        parts.push("true");
    } else if has_false {
        parts.push("false");
    }
    Some(parts.join(" | "))
}

pub(crate) fn format_lit_set<T: Ord + Clone>(
    parts: &mut Vec<String>,
    s: &LiteralSet<T>,
    top_name: &str,
    fmt_one: impl Fn(&T) -> String,
) {
    if s.is_none() {
        return;
    }
    if s.cofinite {
        if s.set.is_empty() {
            parts.push(top_name.into());
        } else {
            let exc: Vec<String> = s.set.iter().map(&fmt_one).collect();
            parts.push(format!("{} \\ {{{}}}", top_name, exc.join(", ")));
        }
    } else {
        for v in &s.set {
            parts.push(fmt_one(v));
        }
    }
}

pub(crate) fn format_tuple_clause(c: &Conj<TupleSig>) -> String {
    let pos: Vec<String> = c.pos.iter().map(format_tuple).collect();
    let neg: Vec<String> = c
        .neg
        .iter()
        .map(|t| format!("¬{}", format_tuple(t)))
        .collect();
    join_clause(&pos, &neg, "tuple")
}
pub(crate) fn format_list_clause(c: &Conj<ListSig>) -> String {
    let pos: Vec<String> = c.pos.iter().map(format_list).collect();
    let neg: Vec<String> = c
        .neg
        .iter()
        .map(|t| format!("¬{}", format_list(t)))
        .collect();
    join_clause(&pos, &neg, "list")
}
pub(crate) fn format_arrow_clause(c: &Conj<ArrowSig>) -> String {
    let pos: Vec<String> = c.pos.iter().map(format_arrow).collect();
    let neg: Vec<String> = c
        .neg
        .iter()
        .map(|t| format!("¬{}", format_arrow(t)))
        .collect();
    join_clause(&pos, &neg, "fn")
}
fn format_tuple(t: &TupleSig) -> String {
    let inner: Vec<String> = t.elems.iter().map(|d| format!("{}", d)).collect();
    format!("{{{}}}", inner.join(", "))
}
fn format_list(t: &ListSig) -> String {
    match (t.empty, &t.elem) {
        (true, None) => "[]".to_string(),
        (true, Some(elem)) => format!("list({})", elem),
        (false, Some(elem)) => format!("nonempty_list({})", elem),
        (false, None) => "none".to_string(),
    }
}
fn format_arrow(t: &ArrowSig) -> String {
    let args: Vec<String> = t.args.iter().map(|d| format!("{}", d)).collect();
    let body = format!("({}) -> {}", args.join(", "), t.ret);
    match &t.lit {
        None => body,
        Some(l) => {
            let caps: Vec<String> = l
                .captures
                .iter()
                .map(|d| format!("{}", ty_descr(d)))
                .collect();
            format!("&fn{}[{}]:{}", l.fn_id.0, caps.join(", "), body)
        }
    }
}
pub(crate) fn format_map_clause(c: &Conj<MapSig>) -> String {
    let pos: Vec<String> = c.pos.iter().map(format_map).collect();
    let neg: Vec<String> = c
        .neg
        .iter()
        .map(|m| format!("¬{}", format_map(m)))
        .collect();
    join_clause(&pos, &neg, "map")
}
fn format_map(m: &MapSig) -> String {
    let inner: Vec<String> = m
        .fields
        .iter()
        .map(|(k, v)| format!("{}: {}", format_map_key(k), v))
        .collect();
    format!("%{{{}}}", inner.join(", "))
}
fn format_map_key(k: &MapKey) -> String {
    match k {
        MapKey::Atom(a) => format!(":{}", a),
        MapKey::Int(n) => format!("{}", n),
    }
}
fn join_clause(pos: &[String], neg: &[String], top: &str) -> String {
    let all: Vec<String> = pos.iter().cloned().chain(neg.iter().cloned()).collect();
    if all.is_empty() {
        top.to_string()
    } else {
        all.join(" & ")
    }
}
