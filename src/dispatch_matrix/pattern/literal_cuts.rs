//! Where sibling literal fields are cut so the clauses that share a position
//! share the field they read there.
//!
//! A literal such as `"true"` is one unsigned big-endian integer field. Beside
//! it a clause with `"false"` reads five bytes from the same position: a
//! different field, so each clause reads and compares for itself. The rule that
//! gives them one field is a single one: **a literal field is cut at every
//! position where a sibling's field ends.** `"false"` becomes `"fals"` and
//! `"e"`; `"true"` and `"null"` already end there, so all three clauses ask the
//! same 32-bit field at bit 0 and differ only in the value they compare it with.
//!
//! "Sibling" is a field of another row's pattern for the same subject, at the
//! same static bit position. A position is static while every field before it
//! has a size the program text states.

use std::collections::BTreeSet;

use super::{PatternRow, PatternSubjectRef};
use crate::ast::{BitField, BitFieldSpec, BitType, Endian, Pattern, PatternBitSize, PatternField, Spanned};
use crate::fast_hash::HashMap;

/// The most bits one literal field holds: the value stays a non-negative `i64`.
const LITERAL_FIELD_BITS: u64 = 63;

type Field = PatternField;

/// The bit positions at which some row's integer field ends, per subject.
#[derive(Debug, Default)]
pub(super) struct LiteralCuts {
    ends: HashMap<PatternSubjectRef, BTreeSet<u64>>,
}

impl LiteralCuts {
    pub(super) fn of_rows<'a, TypeHandle: 'a>(rows: impl Iterator<Item = &'a PatternRow<TypeHandle>>) -> Self {
        let mut cuts = Self::default();
        for row in rows {
            for (ordinal, pattern) in row.patterns.iter().enumerate() {
                cuts.collect(&pattern.node, &PatternSubjectRef::Input(ordinal as u32));
            }
        }
        cuts
    }

    fn collect(&mut self, pattern: &Pattern, subject: &PatternSubjectRef) {
        match pattern {
            Pattern::Binary(bytes) => self.collect_fields(
                &crate::ast::binary_literal_fields(bytes, crate::source::Span::DUMMY),
                subject,
            ),
            Pattern::Bitstring(fields) => self.collect_fields(fields, subject),
            Pattern::Both(left, right) => {
                self.collect(&left.node, subject);
                self.collect(&right.node, subject);
            }
            Pattern::Tuple(fields) => {
                for (index, field) in fields.iter().enumerate() {
                    let tuple = Box::new(subject.clone());
                    self.collect(
                        &field.node,
                        &PatternSubjectRef::TupleField {
                            tuple,
                            index: index as u32,
                        },
                    );
                }
            }
            Pattern::Struct { fields, .. } => {
                for (name, field) in fields {
                    let record = Box::new(subject.clone());
                    self.collect(
                        &field.node,
                        &PatternSubjectRef::StructField {
                            record,
                            field: name.clone(),
                        },
                    );
                }
            }
            Pattern::List(elems, tail) => self.collect_list(elems, tail.as_deref(), subject),
            _ => {}
        }
    }

    fn collect_list(
        &mut self,
        elems: &[Spanned<Pattern>],
        tail: Option<&Spanned<Pattern>>,
        subject: &PatternSubjectRef,
    ) {
        let tail_subject = PatternSubjectRef::ListTail(Box::new(subject.clone()));
        match elems.split_first() {
            None => {
                if let Some(tail) = tail {
                    self.collect(&tail.node, subject);
                }
            }
            Some((head, rest)) => {
                self.collect(&head.node, &PatternSubjectRef::ListHead(Box::new(subject.clone())));
                self.collect_list(rest, tail, &tail_subject);
            }
        }
    }

    fn collect_fields(&mut self, fields: &[Field], subject: &PatternSubjectRef) {
        let ends = extents(fields)
            .into_iter()
            .zip(fields)
            .filter_map(|(extent, field)| extent.filter(|_| shares_reads(&field.spec)).map(|(_, end)| end));
        self.ends.entry(subject.clone()).or_default().extend(ends);
    }

    /// `fields` of a bitstring pattern on `subject`, each literal integer field
    /// cut at the positions siblings end.
    pub(super) fn cut(&self, subject: &PatternSubjectRef, fields: &[Field]) -> Vec<Field> {
        let ends = self.ends.get(subject);
        let mut cut = Vec::with_capacity(fields.len());
        for (field, extent) in fields.iter().zip(extents(fields)) {
            match (ends, extent, &field.value.node) {
                (Some(ends), Some((start, end)), Pattern::Int(value))
                    if shares_reads(&field.spec) && *value >= 0 && end - start <= LITERAL_FIELD_BITS =>
                {
                    cut_field(field, *value, start, end, ends, &mut cut)
                }
                _ => cut.push(field.clone()),
            }
        }
        cut
    }
}

/// Whether a field's read can be another field's: an unsigned big-endian
/// integer of stated size, which is what a literal is.
fn shares_reads(spec: &BitFieldSpec<PatternBitSize>) -> bool {
    spec.ty == BitType::Integer && spec.endian == Endian::Big && !spec.signed && spec.unit.is_none()
}

fn cut_field(field: &Field, value: i64, start: u64, end: u64, ends: &BTreeSet<u64>, out: &mut Vec<Field>) {
    let mut from = start;
    for to in ends.range(start + 1..end).copied().chain([end]) {
        let width = to - from;
        let piece = (value >> (end - to)) & ((1i64 << width) - 1);
        out.push(BitField {
            value: Spanned::new(Pattern::Int(piece), field.value.span),
            spec: BitFieldSpec {
                size: Some(PatternBitSize::Literal(width as u32)),
                ..field.spec.clone()
            },
        });
        from = to;
    }
}

/// Each field's `(start, end)` bit positions while they are static, `None`
/// from the first field whose size the program text does not state.
fn extents(fields: &[Field]) -> Vec<Option<(u64, u64)>> {
    let mut position = Some(0u64);
    fields
        .iter()
        .map(|field| {
            let start = position?;
            position = stated_bits(&field.spec).map(|bits| start + bits);
            position.map(|end| (start, end))
        })
        .collect()
}

fn stated_bits(spec: &BitFieldSpec<PatternBitSize>) -> Option<u64> {
    let unit = u64::from(spec.unit.unwrap_or(spec.ty.default_unit()));
    match (spec.ty, &spec.size) {
        (BitType::Integer | BitType::Binary, Some(PatternBitSize::Literal(size))) => Some(u64::from(*size) * unit),
        (BitType::Integer, None) => Some(8),
        (BitType::Float, None) => Some(64),
        _ => None,
    }
}
