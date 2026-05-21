//! Set-theoretic shape helpers consumed by `ir_typer`. The AST-walking
//! inference driver was retired by fz-ul4.11.24.1; the AST-shaped pattern /
//! expression orphans were pruned by fz-ul4.11.25.2. What survives:
//!
//! - tuple / list projection helpers (used by IR pattern narrowing)
//! - map field lookup / refinement
//! - widening operator for fixed-point termination (used by
//!   `ir_typer::specialize_return` per fz-ul4.11.24.7).

use crate::types::*;
use crate::types_seam::Types;

// ----------------------------------------------------------------------
// Tuple / list projection helpers
// ----------------------------------------------------------------------

/// Project the i-th component of any positive tuple shape in `scrut` of
/// the given arity, intersecting same-arity sigs within a Conj (fz-dhd)
/// and unioning across Conjs. Falls back to `any` when no matching
/// tuple shape is present.
pub(crate) fn tuple_projections(scrut: &Descr, arity: usize) -> Vec<Descr> {
    for component in scrut.components() {
        if let Component::Tuples(view) = component
            && let Some(comps) = view.project_all(arity)
        {
            return comps;
        }
    }
    vec![Descr::any(); arity]
}

// ----------------------------------------------------------------------
// Map helpers
// ----------------------------------------------------------------------

/// Look up the value type for `key` across all positive map shapes in
/// `d`, following fz-dhd open-map semantics. Returns `None` if `d` has
/// no map shapes (call site decides the fallback).
pub(crate) fn map_field_lookup(d: &Descr, key: &MapKey) -> Option<Descr> {
    for component in d.components() {
        if let Component::Maps(view) = component {
            return view.lookup(key);
        }
    }
    None
}

pub(crate) fn refine_map_field(d: &Descr, key: &MapKey, vt: &Descr) -> Descr {
    d.refine_map_field(key, vt)
}

/// Joined element type across all positive list shapes in `scrut`,
/// using fz-dhd DNF semantics (intersect within a Conj, union across).
/// Falls back to `any` when no list shapes are present.
pub(crate) fn list_element_type(scrut: &Descr) -> Descr {
    for component in scrut.components() {
        if let Component::Lists(view) = component {
            return view.element_type();
        }
    }
    Descr::any()
}

// ----------------------------------------------------------------------
// fz-swt.6 — opaque-type visibility gating
// ----------------------------------------------------------------------

/// Why a visibility check failed. Surfaced by `check_opaque_visibility`
/// and rendered by the caller into a `Diagnostic` once it has a span
/// (this module is span-free, like the rest of the helpers here).
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(dead_code)] // fz-swt.8 wires `.value` into this; tests exercise it now.
pub struct OpaqueVisibilityError {
    /// Qualified opaque tag (`"Mod::t"`).
    pub opaque: String,
    /// Module that declared the opaque (`"Mod"`).
    pub owner_module: String,
    /// Module that attempted the access.
    pub using_module: String,
}

impl std::fmt::Display for OpaqueVisibilityError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "field of opaque type `{}` is not accessible from module `{}` \
             (declared in module `{}`)",
            self.opaque, self.using_module, self.owner_module,
        )
    }
}

/// fz-swt.6 — gate field access on an opaque-typed value by declaring
/// module. The check passes when:
///
/// 1. `d` is not a singleton opaque (composite types, non-opaques, and
///    cofinite opaque sets all bypass the gate — the typer's existing
///    structural rules already cover access on those).
/// 2. The opaque tag has no module owner (built-in / runtime-prelude
///    opaques like `"resource"` are visible everywhere; their wrapping
///    user alias is what carries module ownership).
/// 3. The declaring module is exactly `using_module`.
///
/// This is the hook consumed by fz-swt.8's `.value` accessor and any
/// other future opaque-field accessor. Today no surface-syntax field
/// access on opaques exists in fz, so the only consumers are unit tests
/// — wiring at MapGet sites lands with fz-swt.8.
#[allow(dead_code)] // fz-swt.8 wires this into MapGet site typing.
pub(crate) fn check_opaque_visibility(
    d: &Descr,
    using_module: &str,
) -> Result<(), OpaqueVisibilityError> {
    let Some(tag) = d.as_opaque_singleton() else {
        return Ok(());
    };
    let Some(owner) = crate::type_expr::opaque_owner_module(tag) else {
        // Unqualified built-in opaque — no owner, visible from every
        // module by design.
        return Ok(());
    };
    if owner == using_module {
        Ok(())
    } else {
        Err(OpaqueVisibilityError {
            opaque: tag.to_string(),
            owner_module: owner.to_string(),
            using_module: using_module.to_string(),
        })
    }
}

/// fz-axu.5 (K4) — brand visibility. A *brand mint* (the L3 desugaring
/// pass emits `Prim::Brand(_, B)`) requires the using module to own B.
/// Reads and reads-as-inner are unrestricted: a value already carrying
/// brand B is freely usable as its inner T from any module — that is
/// the K4 subtype rule. Only the act of *creating* a B value is gated.
///
/// `using_module` is the qualified module path of the call site;
/// `brand_tag` is the qualified brand name from the mint IR. Wired
/// into `ir_lower::check_brand_visibility` as a pre-erasure pass by
/// fz-axu.24 (M3).
pub(crate) fn check_brand_mint_visibility<T: Types>(
    _t: &mut T,
    brand_tag: &str,
    using_module: &str,
) -> Result<(), OpaqueVisibilityError> {
    let Some(owner) = crate::type_expr::opaque_owner_module(brand_tag) else {
        // Unqualified built-in brand (e.g. `utf8` in runtime.fz) — no
        // owner; mint is allowed from every module.
        return Ok(());
    };
    if owner == using_module {
        Ok(())
    } else {
        Err(OpaqueVisibilityError {
            opaque: brand_tag.to_string(),
            owner_module: owner.to_string(),
            using_module: using_module.to_string(),
        })
    }
}

// ----------------------------------------------------------------------
// Widening (for fixed-point termination)
// ----------------------------------------------------------------------

/// Widen a Descr toward the fixed point: literal-set axes widen to
/// their cofinite tops (`int_lit(42)` → `int()`); structural axes
/// preserve shape and their nested Descrs are widened recursively.
/// Atoms are intentionally not widened — they are nominal singletons.
///
/// fz-ul4.27.22.8 — closure captures widen elementwise via
/// `map_nested_descrs`; the FnId identity is preserved, so widening at
/// SCC fixpoints loses literal precision but keeps the closure-target
/// FnId for per-callsite singleton resolution post-widen.
pub(crate) fn widen(d: &Descr) -> Descr {
    d.widen_literals().map_nested_descrs(&widen)
}

#[cfg(test)]
mod opaque_visibility_tests {
    use super::*;
    use crate::type_expr::{
        ModuleTypeEnv, build_module_type_env_for, opaque_owner_module, qualify_opaque_name,
    };

    fn alias_attr(name: &str, body_src: &str) -> crate::ast::Attribute {
        use crate::ast::{Attribute, TypeAliasDecl, TypeExprBody};
        use crate::diag::Span;
        use crate::lexer::{Lexer, Tok};
        let toks = Lexer::new(body_src).tokenize().expect("lex body");
        let body_tokens: Vec<_> = toks
            .into_iter()
            .filter(|t| !matches!(t.tok, Tok::Eof))
            .collect();
        Attribute::TypeAlias(TypeAliasDecl {
            name: name.to_string(),
            name_span: Span::DUMMY,
            body_tokens: TypeExprBody(body_tokens),
            span: Span::DUMMY,
        })
    }

    fn env_for(module: &str, attrs: &[crate::ast::Attribute]) -> ModuleTypeEnv {
        let mut ct = crate::types_seam::ConcreteTypes;
        build_module_type_env_for(&mut ct, attrs, module)
            .expect("build env")
            .0
    }

    #[test]
    fn qualify_and_invert_roundtrip() {
        let q = qualify_opaque_name("File", "t");
        assert_eq!(q, "File::t");
        assert_eq!(opaque_owner_module(&q), Some("File"));
    }

    #[test]
    fn unqualified_opaque_has_no_owner() {
        let q = qualify_opaque_name("", "resource");
        assert_eq!(q, "resource");
        assert_eq!(opaque_owner_module(&q), None);
    }

    #[test]
    fn opaque_alias_carries_declaring_module() {
        let attrs = vec![alias_attr("t", "opaque integer")];
        let env = env_for("File", &attrs);
        let ct = crate::types_seam::ConcreteTypes;
        let t = env.get("t").expect("alias resolved");
        assert_eq!(ct.opaque_singleton(t).as_deref(), Some("File::t"));
    }

    #[test]
    fn check_passes_inside_declaring_module() {
        let attrs = vec![alias_attr("t", "opaque integer")];
        let env = env_for("File", &attrs);
        let ct = crate::types_seam::ConcreteTypes;
        let t = env.get("t").unwrap();
        assert!(ct.check_opaque_visibility(t, "File").is_ok());
    }

    #[test]
    fn check_rejects_from_other_module() {
        let attrs = vec![alias_attr("t", "opaque integer")];
        let env = env_for("File", &attrs);
        let ct = crate::types_seam::ConcreteTypes;
        let t = env.get("t").unwrap();
        let err = ct
            .check_opaque_visibility(t, "Other")
            .expect_err("must reject");
        assert_eq!(err.opaque, "File::t");
        assert_eq!(err.owner_module, "File");
        assert_eq!(err.using_module, "Other");
        let msg = format!("{}", err);
        assert!(
            msg.contains("not accessible from module `Other`"),
            "expected visibility-gate diag, got: {}",
            msg,
        );
        assert!(
            msg.contains("declared in module `File`"),
            "expected declaring-module mention, got: {}",
            msg,
        );
    }

    #[test]
    fn check_passes_on_non_opaque_descrs() {
        // Non-opaque types are not subject to the gate.
        assert!(check_opaque_visibility(&Descr::int(), "Anywhere").is_ok());
        assert!(check_opaque_visibility(&Descr::any(), "Anywhere").is_ok());
        assert!(check_opaque_visibility(&Descr::none(), "Anywhere").is_ok());
    }

    #[test]
    fn check_passes_on_unqualified_builtin_opaque() {
        // `resource(T)` lowers to the unqualified built-in opaque tag
        // `"resource"`; it has no module owner and is visible everywhere.
        // (User-facing visibility is enforced by the wrapping alias.)
        let d = Descr::opaque_of("resource");
        assert!(check_opaque_visibility(&d, "AnyModule").is_ok());
    }

    #[test]
    fn two_modules_declaring_t_are_distinct_opaques() {
        let a = env_for("A", &[alias_attr("t", "opaque integer")]);
        let b = env_for("B", &[alias_attr("t", "opaque integer")]);
        let mut ct = crate::types_seam::ConcreteTypes;
        let ta = a.get("t").unwrap();
        let tb = b.get("t").unwrap();
        assert_eq!(ct.opaque_singleton(ta).as_deref(), Some("A::t"));
        assert_eq!(ct.opaque_singleton(tb).as_deref(), Some("B::t"));
        let inter = ct.intersect(ta.clone(), tb.clone());
        assert!(
            ct.is_empty(&inter),
            "opaques in different modules must be disjoint: A::t ∩ B::t = {}",
            ct.display(&inter),
        );
        // And the gate respects ownership.
        assert!(ct.check_opaque_visibility(ta, "A").is_ok());
        assert!(ct.check_opaque_visibility(ta, "B").is_err());
        assert!(ct.check_opaque_visibility(tb, "B").is_ok());
        assert!(ct.check_opaque_visibility(tb, "A").is_err());
    }

    // fz-axu.5 (K4) — brand-mint visibility parallels opaque visibility.

    #[test]
    fn brand_mint_visibility_module_qualified() {
        // `@type B :: refines integer` declared in module `M` qualifies
        // the brand tag as `M::B`. Mint is allowed from M, rejected
        // from other modules.
        let mut ct = crate::types_seam::ConcreteTypes;
        assert!(check_brand_mint_visibility(&mut ct, "M::B", "M").is_ok());
        let err = check_brand_mint_visibility(&mut ct, "M::B", "N").expect_err("must reject");
        assert_eq!(err.opaque, "M::B");
        assert_eq!(err.owner_module, "M");
        assert_eq!(err.using_module, "N");
    }

    #[test]
    fn brand_mint_visibility_unqualified_is_global() {
        // Runtime-prelude brands (`@type utf8 :: refines binary`) have
        // no module owner — mintable from any module.
        let mut ct = crate::types_seam::ConcreteTypes;
        assert!(check_brand_mint_visibility(&mut ct, "utf8", "AnyModule").is_ok());
        assert!(check_brand_mint_visibility(&mut ct, "utf8", "").is_ok());
    }

    #[test]
    fn opaque_alias_wrapping_resource_is_gated() {
        // Mirrors the design example: `@type t :: opaque resource(integer)`.
        // The alias's qualified tag — not the inner `resource` — drives
        // the visibility check.
        let attrs = vec![alias_attr("t", "opaque resource(integer)")];
        let env = env_for("File", &attrs);
        let ct = crate::types_seam::ConcreteTypes;
        let t = env.get("t").unwrap();
        assert_eq!(ct.opaque_singleton(t).as_deref(), Some("File::t"));
        assert!(ct.check_opaque_visibility(t, "File").is_ok());
        assert!(ct.check_opaque_visibility(t, "Other").is_err());
    }
}
