use super::*;
use crate::compiler2::Types;
use crate::type_expr::{opaque_owner_module, qualify_opaque_name};

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
    let mut ct = Types::new();
    let t = ct.opaque_of(&qualify_opaque_name("File", "t"));
    assert_eq!(ct.opaque_singleton(&t), Some("File::t".to_string()));
}

#[test]
fn check_passes_inside_declaring_module() {
    let mut ct = Types::new();
    let t = ct.opaque_of(&qualify_opaque_name("File", "t"));
    assert!(ct.check_opaque_visibility(&t, "File").is_ok());
}

#[test]
fn check_rejects_from_other_module() {
    let mut ct = Types::new();
    let t = ct.opaque_of(&qualify_opaque_name("File", "t"));
    let err = ct.check_opaque_visibility(&t, "Other").expect_err("must reject");
    assert_eq!(err.opaque, "File::t");
    assert_eq!(err.owner_module, "File");
    assert_eq!(err.using_module, "Other");
    let msg = format!("{}", err);
    assert!(msg.contains("not accessible from module `Other`"));
    assert!(msg.contains("declared in module `File`"));
}

#[test]
fn check_passes_on_non_opaque_types() {
    let mut ct = Types::new();
    let int = ct.int();
    let any = ct.any();
    let none = ct.none();
    assert!(ct.check_opaque_visibility(&int, "Anywhere").is_ok());
    assert!(ct.check_opaque_visibility(&any, "Anywhere").is_ok());
    assert!(ct.check_opaque_visibility(&none, "Anywhere").is_ok());
}

#[test]
fn check_passes_on_unqualified_builtin_opaque() {
    let mut ct = Types::new();
    let d = ct.opaque_of("resource");
    assert!(ct.check_opaque_visibility(&d, "AnyModule").is_ok());
}

#[test]
fn two_modules_declaring_t_are_distinct_opaques() {
    let mut ct = Types::new();
    let ta = ct.opaque_of(&qualify_opaque_name("A", "t"));
    let tb = ct.opaque_of(&qualify_opaque_name("B", "t"));
    assert_eq!(ct.opaque_singleton(&ta), Some("A::t".to_string()));
    assert_eq!(ct.opaque_singleton(&tb), Some("B::t".to_string()));
    let inter = ct.intersect(ta, tb);
    assert!(ct.is_empty(&inter));
    assert!(ct.check_opaque_visibility(&ta, "A").is_ok());
    assert!(ct.check_opaque_visibility(&ta, "B").is_err());
    assert!(ct.check_opaque_visibility(&tb, "B").is_ok());
    assert!(ct.check_opaque_visibility(&tb, "A").is_err());
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
    let mut ct = Types::new();
    let t = ct.opaque_of(&qualify_opaque_name("File", "t"));
    assert_eq!(ct.opaque_singleton(&t), Some("File::t".to_string()));
    assert!(ct.check_opaque_visibility(&t, "File").is_ok());
    assert!(ct.check_opaque_visibility(&t, "Other").is_err());
}
