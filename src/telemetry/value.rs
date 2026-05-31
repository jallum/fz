//! Typed values carried in telemetry event measurements and metadata.
//!
//! `Value` is intentionally small: numeric primitives for measurements,
//! strings for identifiers, first-class slots for diagnostics and opaque byte
//! blobs, plus event-scoped opaque references for in-process handlers.

use std::any::Any;
use std::borrow::Cow;
use std::fmt;
use std::sync::Arc;

#[derive(Clone, Copy)]
pub struct OpaqueRef<'a> {
    type_name: &'static str,
    value: &'a dyn Any,
}

impl<'a> OpaqueRef<'a> {
    pub fn new<T: Any>(value: &'a T) -> Self {
        Self {
            type_name: std::any::type_name::<T>(),
            value,
        }
    }

    pub fn downcast_ref<T: Any>(self) -> Option<&'a T> {
        self.value.downcast_ref::<T>()
    }
}

impl fmt::Debug for OpaqueRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OpaqueRef")
            .field("type_name", &self.type_name)
            .finish_non_exhaustive()
    }
}

#[derive(Debug, Clone)]
pub enum Value<'a> {
    I64(i64),
    U64(u64),
    F64(f64),
    Bool(bool),
    Str(Cow<'a, str>),
    StrSeq(Arc<[String]>),
    Bytes(Arc<[u8]>),
    Opaque(OpaqueRef<'a>),
}

impl<'a> Value<'a> {
    pub fn opaque<T: Any>(value: &'a T) -> Self {
        Value::Opaque(OpaqueRef::new(value))
    }

    pub fn downcast_ref<T: Any>(&self) -> Option<&'a T> {
        match self {
            Value::Opaque(r) => r.downcast_ref::<T>(),
            _ => None,
        }
    }

    #[cfg(test)]
    pub fn to_owned_durable(&self) -> Option<Value<'static>> {
        match self {
            Value::I64(v) => Some(Value::I64(*v)),
            Value::U64(v) => Some(Value::U64(*v)),
            Value::F64(v) => Some(Value::F64(*v)),
            Value::Bool(v) => Some(Value::Bool(*v)),
            Value::Str(v) => Some(Value::Str(Cow::Owned(v.clone().into_owned()))),
            Value::StrSeq(v) => Some(Value::StrSeq(v.clone())),
            Value::Bytes(v) => Some(Value::Bytes(v.clone())),
            Value::Opaque(_) => None,
        }
    }

    /// True iff the variant carries a numeric measurement. Aggregators
    /// can ignore non-numeric fields without matching on every variant.
    #[cfg(test)]
    pub fn is_numeric(&self) -> bool {
        matches!(self, Value::I64(_) | Value::U64(_) | Value::F64(_))
    }

    /// Stable, lower-snake-case tag for the variant. Useful for renderers
    /// that print `k=v` lines.
    #[cfg(test)]
    pub fn tag(&self) -> &'static str {
        match self {
            Value::I64(_) => "i64",
            Value::U64(_) => "u64",
            Value::F64(_) => "f64",
            Value::Bool(_) => "bool",
            Value::Str(_) => "str",
            Value::StrSeq(_) => "str_seq",
            Value::Bytes(_) => "bytes",
            Value::Opaque(_) => "opaque",
        }
    }
}

pub fn opaque<T: Any>(value: &T) -> Value<'_> {
    Value::opaque(value)
}

// `From` impls let macros write `Value::from(expr)` without callers
// caring whether their value is i64, &str, String, bool, etc.
impl From<i64> for Value<'_> {
    fn from(v: i64) -> Self {
        Value::I64(v)
    }
}
impl From<i32> for Value<'_> {
    fn from(v: i32) -> Self {
        Value::I64(v as i64)
    }
}
impl From<u64> for Value<'_> {
    fn from(v: u64) -> Self {
        Value::U64(v)
    }
}
impl From<u32> for Value<'_> {
    fn from(v: u32) -> Self {
        Value::U64(v as u64)
    }
}
impl From<usize> for Value<'_> {
    fn from(v: usize) -> Self {
        Value::U64(v as u64)
    }
}
impl From<f64> for Value<'_> {
    fn from(v: f64) -> Self {
        Value::F64(v)
    }
}
impl From<bool> for Value<'_> {
    fn from(v: bool) -> Self {
        Value::Bool(v)
    }
}
impl<'a> From<&'a str> for Value<'a> {
    fn from(v: &'a str) -> Self {
        Value::Str(Cow::Borrowed(v))
    }
}
impl<'a> From<&'a String> for Value<'a> {
    fn from(v: &'a String) -> Self {
        Value::Str(Cow::Borrowed(v.as_str()))
    }
}
impl From<String> for Value<'_> {
    fn from(v: String) -> Self {
        Value::Str(Cow::Owned(v))
    }
}
impl<'a> From<Cow<'a, str>> for Value<'a> {
    fn from(v: Cow<'a, str>) -> Self {
        Value::Str(v)
    }
}
impl From<Vec<String>> for Value<'_> {
    fn from(v: Vec<String>) -> Self {
        Value::StrSeq(Arc::from(v))
    }
}
impl From<Arc<[u8]>> for Value<'_> {
    fn from(v: Arc<[u8]>) -> Self {
        Value::Bytes(v)
    }
}
impl From<Vec<u8>> for Value<'_> {
    fn from(v: Vec<u8>) -> Self {
        Value::Bytes(Arc::from(v))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
        assert_eq!(Value::from(vec!["a".to_string()]).tag(), "str_seq");
        assert_eq!(Value::Bytes(Arc::from(vec![])).tag(), "bytes");
    }

    #[test]
    fn string_sequence_from_vec_round_trips() {
        match Value::from(vec!["a".to_string(), "b".to_string()]) {
            Value::StrSeq(values) => assert_eq!(&*values, &["a".to_string(), "b".to_string()]),
            other => panic!("expected string sequence, got {:?}", other),
        }
    }

    #[test]
    fn opaque_round_trip_downcasts_during_event_lifetime() {
        let n = 42usize;
        let v = Value::opaque(&n);
        assert_eq!(v.tag(), "opaque");
        assert_eq!(v.downcast_ref::<usize>(), Some(&42usize));
        assert!(v.downcast_ref::<String>().is_none());
    }

    #[test]
    fn opaque_is_not_durable() {
        let n = 42usize;
        let v = Value::opaque(&n);
        assert!(v.to_owned_durable().is_none());
    }
}
