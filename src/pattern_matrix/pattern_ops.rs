use crate::ast::{Pattern, Spanned};
use crate::exec::matcher::SwitchKind;
use crate::fz_ir::Var;

use super::collect::collect_one;
use super::{CompilePatternMatrix, PatternMatrixCompileError, Row, SubjectRef};

pub(crate) fn append_pattern_ops(
    pattern: &Pattern,
    subject: crate::exec::matcher::SubjectRef,
    pinned_by_name: &std::collections::HashMap<String, crate::exec::matcher::PinnedId>,
    prepared_keys: &mut Vec<crate::exec::matcher::MatcherConst>,
    tests: &mut Vec<crate::exec::matcher::MatcherTest>,
    bindings: &mut Vec<crate::exec::matcher::MatcherBinding>,
) -> Result<(), PatternMatrixCompileError> {
    match pattern {
        Pattern::Wildcard => {}
        Pattern::Var(name) => bindings.push(crate::exec::matcher::MatcherBinding {
            name: name.clone(),
            source: subject,
            span: crate::diag::Span::DUMMY,
        }),
        Pattern::As(name, inner) => {
            bindings.push(crate::exec::matcher::MatcherBinding {
                name: name.clone(),
                source: subject.clone(),
                span: crate::diag::Span::DUMMY,
            });
            append_pattern_ops(
                &inner.node,
                subject,
                pinned_by_name,
                prepared_keys,
                tests,
                bindings,
            )?;
        }
        Pattern::Pinned(name) => {
            let pinned = *pinned_by_name
                .get(name)
                .ok_or_else(|| PatternMatrixCompileError::UnknownPinned(name.clone()))?;
            tests.push(crate::exec::matcher::MatcherTest::EqPinned { subject, pinned });
        }
        Pattern::Int(n) => tests.push(crate::exec::matcher::MatcherTest::EqConst {
            subject,
            value: crate::exec::matcher::MatcherConst::Int(*n),
        }),
        Pattern::Float(n) => tests.push(crate::exec::matcher::MatcherTest::EqConst {
            subject,
            value: crate::exec::matcher::MatcherConst::FloatBits(n.to_bits()),
        }),
        Pattern::Binary(bytes) => tests.push(crate::exec::matcher::MatcherTest::EqConst {
            subject,
            value: crate::exec::matcher::MatcherConst::Utf8Binary(bytes.clone()),
        }),
        Pattern::Atom(name) => tests.push(crate::exec::matcher::MatcherTest::EqConst {
            subject,
            value: crate::exec::matcher::MatcherConst::AtomName(name.clone()),
        }),
        Pattern::Bool(b) => tests.push(crate::exec::matcher::MatcherTest::EqConst {
            subject,
            value: crate::exec::matcher::MatcherConst::Bool(*b),
        }),
        Pattern::Nil => tests.push(crate::exec::matcher::MatcherTest::EqConst {
            subject,
            value: crate::exec::matcher::MatcherConst::Nil,
        }),
        Pattern::Tuple(elems) => {
            tests.push(crate::exec::matcher::MatcherTest::TupleArity {
                subject: subject.clone(),
                arity: elems.len() as u32,
            });
            for (index, elem) in elems.iter().enumerate() {
                append_pattern_ops(
                    &elem.node,
                    crate::exec::matcher::SubjectRef::TupleField {
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
        Pattern::Map(entries) => append_map_pattern_ops(
            entries,
            subject,
            pinned_by_name,
            prepared_keys,
            tests,
            bindings,
        )?,
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
        Pattern::Bitstring(fields) => append_bitstring_pattern_ops(
            fields,
            subject,
            pinned_by_name,
            prepared_keys,
            tests,
            bindings,
        )?,
    }
    Ok(())
}

pub(crate) fn append_bitstring_pattern_ops(
    fields: &[crate::ast::BitField<Spanned<Pattern>>],
    subject: crate::exec::matcher::SubjectRef,
    pinned_by_name: &std::collections::HashMap<String, crate::exec::matcher::PinnedId>,
    prepared_keys: &mut Vec<crate::exec::matcher::MatcherConst>,
    tests: &mut Vec<crate::exec::matcher::MatcherTest>,
    bindings: &mut Vec<crate::exec::matcher::MatcherBinding>,
) -> Result<(), PatternMatrixCompileError> {
    let matcher_fields = fields
        .iter()
        .map(|field| crate::exec::matcher::MatcherBitField {
            ty: matcher_bit_type(field.spec.ty),
            size: field.spec.size.as_ref().map(matcher_bit_size),
            endian: matcher_endian(field.spec.endian),
            signed: field.spec.signed,
            unit: field.spec.unit,
            direct_bindings: direct_bitfield_bindings(&field.value.node),
        })
        .collect();
    tests.push(crate::exec::matcher::MatcherTest::Bitstring {
        subject: subject.clone(),
        fields: matcher_fields,
    });
    for (index, field) in fields.iter().enumerate() {
        append_pattern_ops(
            &field.value.node,
            crate::exec::matcher::SubjectRef::BitstringField {
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

pub(crate) fn matcher_bit_size(size: &crate::ast::BitSize) -> crate::exec::matcher::MatcherBitSize {
    match size {
        crate::ast::BitSize::Literal(n) => crate::exec::matcher::MatcherBitSize::Literal(*n),
        crate::ast::BitSize::Var(name) => {
            crate::exec::matcher::MatcherBitSize::BindingName(name.clone())
        }
    }
}

pub(crate) fn matcher_bit_type(ty: crate::ast::BitType) -> crate::exec::matcher::MatcherBitType {
    match ty {
        crate::ast::BitType::Integer => crate::exec::matcher::MatcherBitType::Integer,
        crate::ast::BitType::Float => crate::exec::matcher::MatcherBitType::Float,
        crate::ast::BitType::Binary => crate::exec::matcher::MatcherBitType::Binary,
        crate::ast::BitType::Bits => crate::exec::matcher::MatcherBitType::Bits,
        crate::ast::BitType::Utf8 => crate::exec::matcher::MatcherBitType::Utf8,
        crate::ast::BitType::Utf16 => crate::exec::matcher::MatcherBitType::Utf16,
        crate::ast::BitType::Utf32 => crate::exec::matcher::MatcherBitType::Utf32,
    }
}

pub(crate) fn matcher_endian(endian: crate::ast::Endian) -> crate::exec::matcher::MatcherEndian {
    match endian {
        crate::ast::Endian::Big => crate::exec::matcher::MatcherEndian::Big,
        crate::ast::Endian::Little => crate::exec::matcher::MatcherEndian::Little,
        crate::ast::Endian::Native => crate::exec::matcher::MatcherEndian::Native,
    }
}

pub(crate) fn append_map_pattern_ops(
    entries: &[(Spanned<Pattern>, Spanned<Pattern>)],
    subject: crate::exec::matcher::SubjectRef,
    pinned_by_name: &std::collections::HashMap<String, crate::exec::matcher::PinnedId>,
    prepared_keys: &mut Vec<crate::exec::matcher::MatcherConst>,
    tests: &mut Vec<crate::exec::matcher::MatcherTest>,
    bindings: &mut Vec<crate::exec::matcher::MatcherBinding>,
) -> Result<(), PatternMatrixCompileError> {
    tests.push(crate::exec::matcher::MatcherTest::MapKind {
        subject: subject.clone(),
    });
    for (key_pat, val_pat) in entries {
        let key = scalar_map_key_const(&key_pat.node, prepared_keys)?;
        tests.push(crate::exec::matcher::MatcherTest::MapHasKey {
            subject: subject.clone(),
            key: key.clone(),
        });
        append_pattern_ops(
            &val_pat.node,
            crate::exec::matcher::map_value_subject(&subject, &key),
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
    prepared_keys: &mut Vec<crate::exec::matcher::MatcherConst>,
) -> Result<crate::exec::matcher::MatcherConst, PatternMatrixCompileError> {
    match pattern {
        Pattern::Int(n) => Ok(crate::exec::matcher::MatcherConst::Int(*n)),
        Pattern::Float(n) => {
            let id = prepared_key_id(
                prepared_keys,
                crate::exec::matcher::MatcherConst::FloatBits(n.to_bits()),
            );
            Ok(crate::exec::matcher::MatcherConst::PreparedKey(id))
        }
        Pattern::Binary(bytes) => {
            let id = prepared_key_id(
                prepared_keys,
                crate::exec::matcher::MatcherConst::Utf8Binary(bytes.clone()),
            );
            Ok(crate::exec::matcher::MatcherConst::PreparedKey(id))
        }
        Pattern::Atom(name) => {
            let id = prepared_key_id(
                prepared_keys,
                crate::exec::matcher::MatcherConst::AtomName(name.clone()),
            );
            Ok(crate::exec::matcher::MatcherConst::PreparedKey(id))
        }
        Pattern::Bool(b) => Ok(crate::exec::matcher::MatcherConst::Bool(*b)),
        Pattern::Nil => Ok(crate::exec::matcher::MatcherConst::Nil),
        _ => Err(PatternMatrixCompileError::UnsupportedMapKey),
    }
}

pub(crate) fn prepared_key_id(
    prepared_keys: &mut Vec<crate::exec::matcher::MatcherConst>,
    key: crate::exec::matcher::MatcherConst,
) -> u32 {
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
    subject: crate::exec::matcher::SubjectRef,
    pinned_by_name: &std::collections::HashMap<String, crate::exec::matcher::PinnedId>,
    prepared_keys: &mut Vec<crate::exec::matcher::MatcherConst>,
    tests: &mut Vec<crate::exec::matcher::MatcherTest>,
    bindings: &mut Vec<crate::exec::matcher::MatcherBinding>,
) -> Result<(), PatternMatrixCompileError> {
    if elems.is_empty() {
        match tail {
            Some(tail) => append_pattern_ops(
                &tail.node,
                subject,
                pinned_by_name,
                prepared_keys,
                tests,
                bindings,
            ),
            None => {
                tests.push(crate::exec::matcher::MatcherTest::EqConst {
                    subject,
                    value: crate::exec::matcher::MatcherConst::EmptyList,
                });
                Ok(())
            }
        }
    } else {
        tests.push(crate::exec::matcher::MatcherTest::ListCons {
            subject: subject.clone(),
        });
        append_pattern_ops(
            &elems[0].node,
            crate::exec::matcher::SubjectRef::ListHead(Box::new(subject.clone())),
            pinned_by_name,
            prepared_keys,
            tests,
            bindings,
        )?;
        let tail_subject = crate::exec::matcher::SubjectRef::ListTail(Box::new(subject));
        if elems.len() == 1 {
            match tail {
                Some(tail) => append_pattern_ops(
                    &tail.node,
                    tail_subject,
                    pinned_by_name,
                    prepared_keys,
                    tests,
                    bindings,
                ),
                None => {
                    tests.push(crate::exec::matcher::MatcherTest::EqConst {
                        subject: tail_subject,
                        value: crate::exec::matcher::MatcherConst::EmptyList,
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

pub(crate) fn push_matcher_node(
    nodes: &mut Vec<crate::exec::matcher::MatcherNode>,
    node: crate::exec::matcher::MatcherNode,
) -> crate::exec::matcher::NodeId {
    let id = crate::exec::matcher::NodeId(nodes.len() as u32);
    nodes.push(node);
    id
}

pub(crate) fn subject_to_matcher_ref(
    subject: &SubjectRef,
    input_by_var: &std::collections::HashMap<Var, crate::exec::matcher::InputId>,
) -> Result<crate::exec::matcher::SubjectRef, PatternMatrixCompileError> {
    Ok(match subject {
        SubjectRef::Var(v) => crate::exec::matcher::SubjectRef::Input(
            *input_by_var
                .get(v)
                .ok_or(PatternMatrixCompileError::UnknownSubject(*v))?,
        ),
        SubjectRef::TupleField { tuple, index } => crate::exec::matcher::SubjectRef::TupleField {
            tuple: Box::new(subject_to_matcher_ref(tuple, input_by_var)?),
            index: *index,
        },
        SubjectRef::ListHead(list) => crate::exec::matcher::SubjectRef::ListHead(Box::new(
            subject_to_matcher_ref(list, input_by_var)?,
        )),
        SubjectRef::ListTail(list) => crate::exec::matcher::SubjectRef::ListTail(Box::new(
            subject_to_matcher_ref(list, input_by_var)?,
        )),
    })
}

pub(crate) fn is_wildlike(p: &Pattern) -> bool {
    matches!(p, Pattern::Wildcard | Pattern::Var(_))
        || matches!(p, Pattern::As(_, inner) if is_wildlike(&inner.node))
}

pub(crate) fn pick_specialization_column(pattern_matrix: &CompilePatternMatrix) -> Option<usize> {
    // Leftmost column that has any non-wildlike pattern across rows.
    (0..pattern_matrix.subjects.len()).find(|&col| {
        pattern_matrix
            .rows
            .iter()
            .any(|r| !is_wildlike(&r.patterns[col].node))
    })
}

pub(crate) fn find_unspecializable_row(
    pattern_matrix: &CompilePatternMatrix,
    col: usize,
) -> Option<usize> {
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
        if matches!(
            p,
            Pattern::Map(_) | Pattern::Bitstring(_) | Pattern::Pinned(_)
        ) {
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

pub(crate) fn pick_kind_for_column(
    pattern_matrix: &CompilePatternMatrix,
    col: usize,
) -> SwitchKind {
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
