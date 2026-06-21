#[cfg(test)]
mod source_map;
mod span;

#[cfg(test)]
pub(crate) use source_map::SourceMap;
pub(crate) use span::{Id, Span, SpanOrigin};
