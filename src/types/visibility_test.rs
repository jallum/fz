use super::*;
use crate::ast::Attribute;
use crate::telemetry::Telemetry;
use crate::type_expr::{ModuleTypeEnv, build_module_type_env_for_with_base, opaque_owner_module, qualify_opaque_name};
use crate::types::Types;

fn alias_attr(name: &str, body_src: &str, tel: &dyn Telemetry) -> Attribute {
    use crate::ast::{Attribute, TypeAliasDecl, TypeExprBody};
    use crate::compiler::source::Span;
    use crate::parser::lexer::{Lexer, Tok};
    let toks = Lexer::with_source_name(body_src, "<test>")
        .tokenize(tel)
        .expect("lex body");
    let body_tokens: Vec<_> = toks.into_iter().filter(|t| !matches!(t.tok, Tok::Eof)).collect();
    Attribute::TypeAlias(TypeAliasDecl {
        name: name.to_string(),
        name_span: Span::DUMMY,
        params: vec![],
        body_tokens: TypeExprBody(body_tokens),
        span: Span::DUMMY,
    })
}

fn env_for(module: &str, attrs: &[Attribute]) -> ModuleTypeEnv {
    let mut ct = crate::types::new();
    build_module_type_env_for_with_base(&mut ct, attrs, module, &ModuleTypeEnv::new())
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
    let attrs = vec![alias_attr(
        "t",
        "opaque integer",
        &crate::telemetry::ConfiguredTelemetry::new(),
    )];
    let env = env_for("File", &attrs);
    let ct = crate::types::new();
    let t = env.get("t").expect("alias resolved");
    assert_eq!(ct.opaque_singleton(t), Some("File::t".to_string()));
}

#[test]
fn check_passes_inside_declaring_module() {
    let attrs = vec![alias_attr(
        "t",
        "opaque integer",
        &crate::telemetry::ConfiguredTelemetry::new(),
    )];
    let env = env_for("File", &attrs);
    let ct = crate::types::new();
    let t = env.get("t").unwrap();
    assert!(ct.check_opaque_visibility(t, "File").is_ok());
}

#[test]
fn check_rejects_from_other_module() {
    let attrs = vec![alias_attr(
        "t",
        "opaque integer",
        &crate::telemetry::ConfiguredTelemetry::new(),
    )];
    let env = env_for("File", &attrs);
    let ct = crate::types::new();
    let t = env.get("t").unwrap();
    let err = ct.check_opaque_visibility(t, "Other").expect_err("must reject");
    assert_eq!(err.opaque, "File::t");
    assert_eq!(err.owner_module, "File");
    assert_eq!(err.using_module, "Other");
    let msg = format!("{}", err);
    assert!(msg.contains("not accessible from module `Other`"));
    assert!(msg.contains("declared in module `File`"));
}

#[test]
fn check_passes_on_non_opaque_types() {
    let mut ct = crate::types::new();
    let int = ct.int();
    let any = ct.any();
    let none = ct.none();
    assert!(ct.check_opaque_visibility(&int, "Anywhere").is_ok());
    assert!(ct.check_opaque_visibility(&any, "Anywhere").is_ok());
    assert!(ct.check_opaque_visibility(&none, "Anywhere").is_ok());
}

#[test]
fn check_passes_on_unqualified_builtin_opaque() {
    let mut ct = crate::types::new();
    let d = ct.opaque_of("resource");
    assert!(ct.check_opaque_visibility(&d, "AnyModule").is_ok());
}

#[test]
fn two_modules_declaring_t_are_distinct_opaques() {
    let a = env_for(
        "A",
        &[alias_attr(
            "t",
            "opaque integer",
            &crate::telemetry::ConfiguredTelemetry::new(),
        )],
    );
    let b = env_for(
        "B",
        &[alias_attr(
            "t",
            "opaque integer",
            &crate::telemetry::ConfiguredTelemetry::new(),
        )],
    );
    let mut ct = crate::types::new();
    let ta = a.get("t").unwrap();
    let tb = b.get("t").unwrap();
    assert_eq!(ct.opaque_singleton(ta), Some("A::t".to_string()));
    assert_eq!(ct.opaque_singleton(tb), Some("B::t".to_string()));
    let inter = ct.intersect(ta.clone(), tb.clone());
    assert!(ct.is_empty(&inter));
    assert!(ct.check_opaque_visibility(ta, "A").is_ok());
    assert!(ct.check_opaque_visibility(ta, "B").is_err());
    assert!(ct.check_opaque_visibility(tb, "B").is_ok());
    assert!(ct.check_opaque_visibility(tb, "A").is_err());
}

#[test]
fn brand_mint_visibility_module_qualified() {
    assert!(check_brand_mint_visibility("M::B", "M").is_ok());
    let err = check_brand_mint_visibility("M::B", "N").expect_err("must reject");
    assert_eq!(err.opaque, "M::B");
    assert_eq!(err.owner_module, "M");
    assert_eq!(err.using_module, "N");
}

#[test]
fn brand_mint_visibility_unqualified_is_global() {
    assert!(check_brand_mint_visibility("utf8", "AnyModule").is_ok());
    assert!(check_brand_mint_visibility("utf8", "").is_ok());
}

#[test]
fn opaque_alias_wrapping_resource_is_gated() {
    let attrs = vec![alias_attr(
        "t",
        "opaque resource(integer)",
        &crate::telemetry::ConfiguredTelemetry::new(),
    )];
    let env = env_for("File", &attrs);
    let ct = crate::types::new();
    let t = env.get("t").unwrap();
    assert_eq!(ct.opaque_singleton(t), Some("File::t".to_string()));
    assert!(ct.check_opaque_visibility(t, "File").is_ok());
    assert!(ct.check_opaque_visibility(t, "Other").is_err());
}
