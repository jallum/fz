//! Typed values carried in telemetry event measurements and metadata.
//!
//! `Value` is intentionally small: numeric primitives for measurements,
//! strings for identifiers, plus first-class slots for `Diagnostic` and
//! opaque byte blobs (artifact payloads). Anything richer than this should
//! be a string-rendered metadata field, not a new variant.

use std::borrow::Cow;
use std::sync::Arc;

use crate::diag::Diagnostic;

#[derive(Debug, Clone)]
pub enum Value {
    I64(i64),
    U64(u64),
    F64(f64),
    Bool(bool),
    Str(Cow<'static, str>),
    Diagnostic(Box<Diagnostic>),
    Bytes(Arc<[u8]>),
}

impl Value {
    /// True iff the variant carries a numeric measurement. Aggregators
    /// can ignore non-numeric fields without matching on every variant.
    pub fn is_numeric(&self) -> bool {
        matches!(self, Value::I64(_) | Value::U64(_) | Value::F64(_))
    }

    /// Stable, lower-snake-case tag for the variant. Useful for renderers
    /// that print `k=v` lines and for schema-validation against KeySpec.
    pub fn tag(&self) -> &'static str {
        match self {
            Value::I64(_) => "i64",
            Value::U64(_) => "u64",
            Value::F64(_) => "f64",
            Value::Bool(_) => "bool",
            Value::Str(_) => "str",
            Value::Diagnostic(_) => "diagnostic",
            Value::Bytes(_) => "bytes",
        }
    }
}

// `From` impls let macros write `Value::from(expr)` without callers
// caring whether their value is i64, &str, String, bool, etc.
impl From<i64> for Value {
    fn from(v: i64) -> Self {
        Value::I64(v)
    }
}
impl From<i32> for Value {
    fn from(v: i32) -> Self {
        Value::I64(v as i64)
    }
}
impl From<u64> for Value {
    fn from(v: u64) -> Self {
        Value::U64(v)
    }
}
impl From<u32> for Value {
    fn from(v: u32) -> Self {
        Value::U64(v as u64)
    }
}
impl From<usize> for Value {
    fn from(v: usize) -> Self {
        Value::U64(v as u64)
    }
}
impl From<f64> for Value {
    fn from(v: f64) -> Self {
        Value::F64(v)
    }
}
impl From<bool> for Value {
    fn from(v: bool) -> Self {
        Value::Bool(v)
    }
}
impl From<&'static str> for Value {
    fn from(v: &'static str) -> Self {
        Value::Str(Cow::Borrowed(v))
    }
}
impl From<String> for Value {
    fn from(v: String) -> Self {
        Value::Str(Cow::Owned(v))
    }
}
impl From<Cow<'static, str>> for Value {
    fn from(v: Cow<'static, str>) -> Self {
        Value::Str(v)
    }
}
impl From<Diagnostic> for Value {
    fn from(v: Diagnostic) -> Self {
        Value::Diagnostic(Box::new(v))
    }
}
impl From<Box<Diagnostic>> for Value {
    fn from(v: Box<Diagnostic>) -> Self {
        Value::Diagnostic(v)
    }
}
impl From<Arc<[u8]>> for Value {
    fn from(v: Arc<[u8]>) -> Self {
        Value::Bytes(v)
    }
}
impl From<Vec<u8>> for Value {
    fn from(v: Vec<u8>) -> Self {
        Value::Bytes(Arc::from(v))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diag::diagnostic::DiagCode;
    use crate::diag::span::Span;

    #[test]
    fn from_impls_cover_primitives() {
        assert!(matches!(Value::from(3i64), Value::I64(3)));
        assert!(matches!(Value::from(3i32), Value::I64(3)));
        assert!(matches!(Value::from(3u64), Value::U64(3)));
        assert!(matches!(Value::from(3u32), Value::U64(3)));
        assert!(matches!(Value::from(3usize), Value::U64(3)));
        assert!(matches!(Value::from(2.5f64), Value::F64(_)));
        assert!(matches!(Value::from(true), Value::Bool(true)));
    }

    #[test]
    fn str_from_static_is_borrowed() {
        match Value::from("hello") {
            Value::Str(Cow::Borrowed("hello")) => {}
            v => panic!("expected borrowed str, got {:?}", v),
        }
    }

    #[test]
    fn str_from_string_is_owned() {
        let s = String::from("dynamic");
        match Value::from(s) {
            Value::Str(Cow::Owned(s)) => assert_eq!(s, "dynamic"),
            v => panic!("expected owned str, got {:?}", v),
        }
    }

    #[test]
    fn diagnostic_round_trip() {
        let d = Diagnostic::warning(DiagCode("test/code"), "headline", Span::DUMMY);
        let v: Value = d.clone().into();
        match &v {
            Value::Diagnostic(b) => {
                assert_eq!(b.code, d.code);
                assert_eq!(b.message, d.message);
            }
            other => panic!("expected diagnostic, got {:?}", other),
        }
    }

    #[test]
    fn bytes_round_trip() {
        let v: Value = vec![1u8, 2, 3].into();
        match v {
            Value::Bytes(b) => assert_eq!(&*b, &[1, 2, 3]),
            other => panic!("expected bytes, got {:?}", other),
        }
    }

    #[test]
    fn is_numeric_classifies_correctly() {
        assert!(Value::I64(1).is_numeric());
        assert!(Value::U64(1).is_numeric());
        assert!(Value::F64(1.0).is_numeric());
        assert!(!Value::Bool(true).is_numeric());
        assert!(!Value::from("x").is_numeric());
    }

    #[test]
    fn tag_is_stable_lower_snake() {
        assert_eq!(Value::I64(0).tag(), "i64");
        assert_eq!(Value::U64(0).tag(), "u64");
        assert_eq!(Value::F64(0.0).tag(), "f64");
        assert_eq!(Value::Bool(false).tag(), "bool");
        assert_eq!(Value::from("s").tag(), "str");
        assert_eq!(Value::Bytes(Arc::from(vec![])).tag(), "bytes");
    }
}
