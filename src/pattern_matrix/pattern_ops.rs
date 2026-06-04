use crate::ast::{BitField, BitSize, BitType, Endian, Pattern, Spanned};
use crate::diag::Span;
use crate::exec::matcher::{
    self as matcher, InputId, MatcherBinding, MatcherBitField, MatcherBitSize, MatcherBitType, MatcherConst,
    MatcherEndian, MatcherNode, MatcherTest, NodeId, PinnedId, SwitchKind, map_value_subject,
};
use crate::fz_ir::Var;

use std::collections::HashMap;

use super::collect::collect_one;
use super::{CompilePatternMatrix, PatternMatrixCompileError, Row, SubjectRef};

pub(crate) fn append_pattern_ops(
    pattern: &Pattern,
    subject: matcher::SubjectRef,
    pinned_by_name: &HashMap<String, PinnedId>,
    prepared_keys: &mut Vec<MatcherConst>,
    tests: &mut Vec<MatcherTest>,
    bindings: &mut Vec<MatcherBinding>,
) -> Result<(), PatternMatrixCompileError> {
    match pattern {
        Pattern::Wildcard => {}
        Pattern::Var(name) => bindings.push(MatcherBinding {
            name: name.clone(),
            source: subject,
            span: Span::DUMMY,
        }),
        Pattern::As(name, inner) => {
            bindings.push(MatcherBinding {
                name: name.clone(),
                source: subject.clone(),
                span: Span::DUMMY,
            });
            append_pattern_ops(&inner.node, subject, pinned_by_name, prepared_keys, tests, bindings)?;
        }
        Pattern::Pinned(name) => {
            let pinned = *pinned_by_name
                .get(name)
                .ok_or_else(|| PatternMatrixCompileError::UnknownPinned(name.clone()))?;
            tests.push(MatcherTest::EqPinned { subject, pinned });
        }
        Pattern::Int(n) => tests.push(MatcherTest::EqConst {
            subject,
            value: MatcherConst::Int(*n),
        }),
        Pattern::Float(n) => tests.push(MatcherTest::EqConst {
            subject,
            value: MatcherConst::FloatBits(n.to_bits()),
        }),
        Pattern::Binary(bytes) => tests.push(MatcherTest::EqConst {
            subject,
            value: MatcherConst::Utf8Binary(bytes.clone()),
        }),
        Pattern::Atom(name) => tests.push(MatcherTest::EqConst {
            subject,
            value: MatcherConst::AtomName(name.clone()),
        }),
        Pattern::Bool(b) => tests.push(MatcherTest::EqConst {
            subject,
            value: MatcherConst::Bool(*b),
        }),
        Pattern::Nil => tests.push(MatcherTest::EqConst {
            subject,
            value: MatcherConst::Nil,
        }),
        Pattern::Tuple(elems) => {
            tests.push(MatcherTest::TupleArity {
                subject: subject.clone(),
                arity: elems.len() as u32,
            });
            for (index, elem) in elems.iter().enumerate() {
                append_pattern_ops(
                    &elem.node,
                    matcher::SubjectRef::TupleField {
                        tuple: Box::new(subject.clone()),
                        index: index as u32,
                    },
                    pinned_by_name,
                    prepared_keys,
                    tests,
                    bindings,
                )?;
            }
        }
        Pattern::List(elems, tail) => append_list_pattern_ops(
            elems,
            tail.as_deref(),
            subject,
            pinned_by_name,
            prepared_keys,
            tests,
            bindings,
        )?,
        Pattern::Map(entries) => {
            append_map_pattern_ops(entries, subject, pinned_by_name, prepared_keys, tests, bindings)?
        }
        Pattern::Struct { fields, .. } => {
            for (_, value) in fields {
                append_pattern_ops(
                    &value.node,
                    subject.clone(),
                    pinned_by_name,
                    prepared_keys,
                    tests,
                    bindings,
                )?;
            }
        }
        Pattern::Bitstring(fields) => {
            append_bitstring_pattern_ops(fields, subject, pinned_by_name, prepared_keys, tests, bindings)?
        }
    }
    Ok(())
}

pub(crate) fn append_bitstring_pattern_ops(
    fields: &[BitField<Spanned<Pattern>>],
    subject: matcher::SubjectRef,
    pinned_by_name: &HashMap<String, PinnedId>,
    prepared_keys: &mut Vec<MatcherConst>,
    tests: &mut Vec<MatcherTest>,
    bindings: &mut Vec<MatcherBinding>,
) -> Result<(), PatternMatrixCompileError> {
    let matcher_fields = fields
        .iter()
        .map(|field| MatcherBitField {
            ty: matcher_bit_type(field.spec.ty),
            size: field.spec.size.as_ref().map(matcher_bit_size),
            endian: matcher_endian(field.spec.endian),
            signed: field.spec.signed,
            unit: field.spec.unit,
            direct_bindings: direct_bitfield_bindings(&field.value.node),
        })
        .collect();
    tests.push(MatcherTest::Bitstring {
        subject: subject.clone(),
        fields: matcher_fields,
    });
    for (index, field) in fields.iter().enumerate() {
        append_pattern_ops(
            &field.value.node,
            matcher::SubjectRef::BitstringField {
                bitstring: Box::new(subject.clone()),
                index: index as u32,
            },
            pinned_by_name,
            prepared_keys,
            tests,
            bindings,
        )?;
    }
    Ok(())
}

pub(crate) fn direct_bitfield_bindings(pattern: &Pattern) -> Vec<String> {
    match pattern {
        Pattern::Var(name) => vec![name.clone()],
        Pattern::As(name, inner) => {
            let mut out = vec![name.clone()];
            out.extend(direct_bitfield_bindings(&inner.node));
            out
        }
        _ => Vec::new(),
    }
}

pub(crate) fn matcher_bit_size(size: &BitSize) -> MatcherBitSize {
    match size {
        BitSize::Literal(n) => MatcherBitSize::Literal(*n),
        BitSize::Var(name) => MatcherBitSize::BindingName(name.clone()),
    }
}

pub(crate) fn matcher_bit_type(ty: BitType) -> MatcherBitType {
    match ty {
        BitType::Integer => MatcherBitType::Integer,
        BitType::Float => MatcherBitType::Float,
        BitType::Binary => MatcherBitType::Binary,
        BitType::Bits => MatcherBitType::Bits,
        BitType::Utf8 => MatcherBitType::Utf8,
        BitType::Utf16 => MatcherBitType::Utf16,
        BitType::Utf32 => MatcherBitType::Utf32,
    }
}

pub(crate) fn matcher_endian(endian: Endian) -> MatcherEndian {
    match endian {
        Endian::Big => MatcherEndian::Big,
        Endian::Little => MatcherEndian::Little,
        Endian::Native => MatcherEndian::Native,
    }
}

pub(crate) fn append_map_pattern_ops(
    entries: &[(Spanned<Pattern>, Spanned<Pattern>)],
    subject: matcher::SubjectRef,
    pinned_by_name: &HashMap<String, PinnedId>,
    prepared_keys: &mut Vec<MatcherConst>,
    tests: &mut Vec<MatcherTest>,
    bindings: &mut Vec<MatcherBinding>,
) -> Result<(), PatternMatrixCompileError> {
    tests.push(MatcherTest::MapKind {
        subject: subject.clone(),
    });
    for (key_pat, val_pat) in entries {
        let key = scalar_map_key_const(&key_pat.node, prepared_keys)?;
        tests.push(MatcherTest::MapHasKey {
            subject: subject.clone(),
            key: key.clone(),
        });
        append_pattern_ops(
            &val_pat.node,
            map_value_subject(&subject, &key),
            pinned_by_name,
            prepared_keys,
            tests,
            bindings,
        )?;
    }
    Ok(())
}

pub(crate) fn scalar_map_key_const(
    pattern: &Pattern,
    prepared_keys: &mut Vec<MatcherConst>,
) -> Result<MatcherConst, PatternMatrixCompileError> {
    match pattern {
        Pattern::Int(n) => Ok(MatcherConst::Int(*n)),
        Pattern::Float(n) => {
            let id = prepared_key_id(prepared_keys, MatcherConst::FloatBits(n.to_bits()));
            Ok(MatcherConst::PreparedKey(id))
        }
        Pattern::Binary(bytes) => {
            let id = prepared_key_id(prepared_keys, MatcherConst::Utf8Binary(bytes.clone()));
            Ok(MatcherConst::PreparedKey(id))
        }
        Pattern::Atom(name) => {
            let id = prepared_key_id(prepared_keys, MatcherConst::AtomName(name.clone()));
            Ok(MatcherConst::PreparedKey(id))
        }
        Pattern::Bool(b) => Ok(MatcherConst::Bool(*b)),
        Pattern::Nil => Ok(MatcherConst::Nil),
        _ => Err(PatternMatrixCompileError::UnsupportedMapKey),
    }
}

pub(crate) fn prepared_key_id(prepared_keys: &mut Vec<MatcherConst>, key: MatcherConst) -> u32 {
    if let Some(index) = prepared_keys.iter().position(|existing| existing == &key) {
        return index as u32;
    }
    let id = prepared_keys.len() as u32;
    prepared_keys.push(key);
    id
}

pub(crate) fn append_list_pattern_ops(
    elems: &[Spanned<Pattern>],
    tail: Option<&Spanned<Pattern>>,
    subject: matcher::SubjectRef,
    pinned_by_name: &HashMap<String, PinnedId>,
    prepared_keys: &mut Vec<MatcherConst>,
    tests: &mut Vec<MatcherTest>,
    bindings: &mut Vec<MatcherBinding>,
) -> Result<(), PatternMatrixCompileError> {
    if elems.is_empty() {
        match tail {
            Some(tail) => append_pattern_ops(&tail.node, subject, pinned_by_name, prepared_keys, tests, bindings),
            None => {
                tests.push(MatcherTest::EqConst {
                    subject,
                    value: MatcherConst::EmptyList,
                });
                Ok(())
            }
        }
    } else {
        tests.push(MatcherTest::ListCons {
            subject: subject.clone(),
        });
        append_pattern_ops(
            &elems[0].node,
            matcher::SubjectRef::ListHead(Box::new(subject.clone())),
            pinned_by_name,
            prepared_keys,
            tests,
            bindings,
        )?;
        let tail_subject = matcher::SubjectRef::ListTail(Box::new(subject));
        if elems.len() == 1 {
            match tail {
                Some(tail) => {
                    append_pattern_ops(&tail.node, tail_subject, pinned_by_name, prepared_keys, tests, bindings)
                }
                None => {
                    tests.push(MatcherTest::EqConst {
                        subject: tail_subject,
                        value: MatcherConst::EmptyList,
                    });
                    Ok(())
                }
            }
        } else {
            append_list_pattern_ops(
                &elems[1..],
                tail,
                tail_subject,
                pinned_by_name,
                prepared_keys,
                tests,
                bindings,
            )
        }
    }
}

pub(crate) fn push_matcher_node(nodes: &mut Vec<MatcherNode>, node: MatcherNode) -> NodeId {
    let id = NodeId(nodes.len() as u32);
    nodes.push(node);
    id
}

pub(crate) fn subject_to_matcher_ref(
    subject: &SubjectRef,
    input_by_var: &HashMap<Var, InputId>,
) -> Result<matcher::SubjectRef, PatternMatrixCompileError> {
    Ok(match subject {
        SubjectRef::Var(v) => matcher::SubjectRef::Input(
            *input_by_var
                .get(v)
                .ok_or(PatternMatrixCompileError::UnknownSubject(*v))?,
        ),
        SubjectRef::TupleField { tuple, index } => matcher::SubjectRef::TupleField {
            tuple: Box::new(subject_to_matcher_ref(tuple, input_by_var)?),
            index: *index,
        },
        SubjectRef::ListHead(list) => {
            matcher::SubjectRef::ListHead(Box::new(subject_to_matcher_ref(list, input_by_var)?))
        }
        SubjectRef::ListTail(list) => {
            matcher::SubjectRef::ListTail(Box::new(subject_to_matcher_ref(list, input_by_var)?))
        }
    })
}

pub(crate) fn is_wildlike(p: &Pattern) -> bool {
    matches!(p, Pattern::Wildcard | Pattern::Var(_)) || matches!(p, Pattern::As(_, inner) if is_wildlike(&inner.node))
}

pub(crate) fn pick_specialization_column(pattern_matrix: &CompilePatternMatrix) -> Option<usize> {
    // Leftmost column that has any non-wildlike pattern across rows.
    (0..pattern_matrix.subjects.len())
        .find(|&col| pattern_matrix.rows.iter().any(|r| !is_wildlike(&r.patterns[col].node)))
}

pub(crate) fn find_unspecializable_row(pattern_matrix: &CompilePatternMatrix, col: usize) -> Option<usize> {
    for (i, r) in pattern_matrix.rows.iter().enumerate() {
        // Look through As-patterns.
        let mut p = &r.patterns[col].node;
        while let Pattern::As(_, inner) = p {
            p = &inner.node;
        }
        // fz-puj.20 (H9 / E2) — Pinned patterns dispatch on a
        // runtime-resolved value rather than a constructor; there's no
        // SwitchKind for them. Route the row through PerRow so the
        // backend's per-row pattern walker handles the equality test
        // against `pinned[idx]`.
        if matches!(p, Pattern::Map(_) | Pattern::Bitstring(_) | Pattern::Pinned(_)) {
            return Some(i);
        }
    }
    None
}

pub(crate) fn row_can_reject(row: &Row) -> bool {
    row.guard.is_some() || !row.preconditions.is_empty()
}

pub(crate) fn record_removed_column_bindings(row: &mut Row, col: usize, subject: &SubjectRef) {
    let mut bindings = Vec::new();
    collect_one(&row.patterns[col].node, subject, &mut bindings);
    row.bindings.extend(bindings);
}

pub(crate) fn pick_kind_for_column(pattern_matrix: &CompilePatternMatrix, col: usize) -> SwitchKind {
    // Use the first row's non-wildlike pattern in this column.
    for r in &pattern_matrix.rows {
        let mut p = &r.patterns[col].node;
        while let Pattern::As(_, inner) = p {
            p = &inner.node;
        }
        match p {
            Pattern::Tuple(_) => return SwitchKind::TupleArity,
            Pattern::Atom(_) => return SwitchKind::Atom,
            Pattern::Int(_) => return SwitchKind::Int,
            Pattern::Float(_) => return SwitchKind::Float,
            Pattern::Bool(_) => return SwitchKind::Bool,
            Pattern::Nil => return SwitchKind::Nil,
            Pattern::Binary(_) => return SwitchKind::Binary,
            Pattern::List(_, _) => return SwitchKind::ListCons,
            _ => continue,
        }
    }
    // Should never reach: pick_specialization_column returned this col
    // because some row was non-wildlike. Fall back conservatively.
    SwitchKind::TupleArity
}

/// Strip As-wrappers off a column pattern. Bindings for removed columns are
/// recorded separately by `record_removed_column_bindings`.
pub(crate) fn peel_to_inner_with_bind(pat: &Spanned<Pattern>) -> (bool, Spanned<Pattern>) {
    let mut had = false;
    let mut cur = pat.clone();
    while let Pattern::As(_, inner) = &cur.node {
        had = true;
        let inner_box = inner.clone();
        cur = (*inner_box).clone();
    }
    (had, cur)
}
