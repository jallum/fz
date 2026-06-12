//! Typed values carried in telemetry event measurements and metadata.
//!
//! `Value` is intentionally small: numeric primitives for measurements,
//! strings for identifiers, first-class slots for diagnostics and opaque byte
//! blobs, plus event-scoped opaque references for in-process handlers.

use std::any::{Any, type_name};
use std::borrow::Cow;
use std::fmt;
use std::sync::Arc;

type OpaqueDebugFn = fn(&dyn Any, &mut fmt::Formatter<'_>) -> fmt::Result;

#[derive(Clone, Copy)]
pub struct OpaqueRef<'a> {
    type_name: &'static str,
    value: &'a dyn Any,
    debug: Option<OpaqueDebugFn>,
}

impl<'a> OpaqueRef<'a> {
    pub fn new<T: Any>(value: &'a T) -> Self {
        Self {
            type_name: type_name::<T>(),
            value,
            debug: None,
        }
    }

    pub fn new_debug<T: Any + fmt::Debug>(value: &'a T) -> Self {
        Self {
            type_name: type_name::<T>(),
            value,
            debug: Some(debug_opaque::<T>),
        }
    }

    pub fn downcast_ref<T: Any>(self) -> Option<&'a T> {
        self.value.downcast_ref::<T>()
    }

    pub fn type_name(self) -> &'static str {
        self.type_name
    }

    pub fn debug_value(self) -> Option<OpaqueDebugValue<'a>> {
        self.debug.map(|_| OpaqueDebugValue(self))
    }
}

#[derive(Clone, Copy)]
pub struct OpaqueDebugValue<'a>(OpaqueRef<'a>);

impl fmt::Debug for OpaqueDebugValue<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (self.0.debug.expect("opaque debug wrapper requires a debug formatter"))(self.0.value, f)
    }
}

fn debug_opaque<T: Any + fmt::Debug>(value: &dyn Any, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let value = value
        .downcast_ref::<T>()
        .expect("opaque debug formatter should only run on the original value type");
    fmt::Debug::fmt(value, f)
}

impl fmt::Debug for OpaqueRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut debug = f.debug_struct("OpaqueRef");
        debug.field("type_name", &self.type_name);
        if let Some(value) = self.debug_value() {
            debug.field("value", &value).finish()
        } else {
            debug.finish_non_exhaustive()
        }
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

    pub fn opaque_debug<T: Any + fmt::Debug>(value: &'a T) -> Self {
        Value::Opaque(OpaqueRef::new_debug(value))
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

pub fn opaque_debug<T: Any + fmt::Debug>(value: &T) -> Value<'_> {
    Value::opaque_debug(value)
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
#[path = "value_test.rs"]
mod value_test;
