//! The one emitter behind every native runtime type test.
//!
//! Two doors ask the same question of a value -- a lowered `RuntimeTypeTest`
//! prim in a compiled function body, and a receive plan's region test -- and
//! they used to ask it through two parallel copies of the same eight functions
//! (fz-kdt.134). Per-position tuple shapes would have doubled that duplication,
//! so the two copies are folded here and each door supplies only what is
//! genuinely its own: how it reads a value's tag, its fields, and its scalar
//! payloads.
//!
//! The shape of the answer is the axis table's
//! ([`crate::runtime_type_predicate::RuntimeTestAxis`]): a test is the OR of
//! its axes' flags, and [`emit_axis`] matches the table exhaustively, so an
//! axis added to the lattice stops both doors compiling until it is decided
//! here.

use std::collections::HashMap;

use cranelift_codegen::ir::{self, BlockArg, InstBuilder, condcodes::IntCC, types};
use cranelift_frontend::FunctionBuilder;
use fz_runtime::any_value::ValueKind;

use crate::finite_set::FiniteSet;
use crate::runtime_type_predicate::{ListShape, RuntimeTestAxis, RuntimeTypePredicate, lowering_tests_position};
use crate::types::ClosureTarget;

use super::CodegenError;

/// What a door already knows of a value's kind before any test runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum KindEvidence {
    /// A tagged any-value: the test must read the tag.
    Tagged,
    /// Held in an unboxed representation, which IS its kind.
    Unboxed(ValueKind),
    /// Held in a representation this door does not answer kind questions
    /// about. Every kind-guarded question about such a value answers no, which
    /// is what both emitters said before they were folded.
    Opaque,
}

/// What one door can read off a value.
///
/// Everything above this trait is the predicate's business and is written
/// once; everything in it is the door's, because only the door knows how its
/// values are held.
pub(super) trait RuntimeTestEmitter<'f> {
    /// The value form this door hands around.
    type Value: Copy;

    fn builder(&mut self) -> &mut FunctionBuilder<'f>;
    fn atom_names(&self) -> &[String];
    fn tuple_schema_ids(&self) -> &HashMap<usize, u32>;
    fn named_schema_ids(&self) -> &HashMap<String, u32>;

    fn kind_evidence(&self, value: Self::Value) -> KindEvidence;
    fn kind_flag(&mut self, value: Self::Value, kind: ValueKind) -> Result<ir::Value, CodegenError>;

    fn raw_int(&mut self, value: Self::Value) -> Result<ir::Value, CodegenError>;
    fn raw_float_bits(&mut self, value: Self::Value) -> Result<ir::Value, CodegenError>;
    fn raw_atom(&mut self, value: Self::Value) -> Result<ir::Value, CodegenError>;

    fn empty_list_flag(&mut self, value: Self::Value) -> Result<ir::Value, CodegenError>;
    fn cons_flag(&mut self, value: Self::Value) -> Result<ir::Value, CodegenError>;

    /// The value's schema id, widened to `I64`. Only asked under a STRUCT
    /// guard.
    fn schema_id(&mut self, value: Self::Value) -> Result<ir::Value, CodegenError>;
    /// Field `index` of a struct value. Only asked under a guard that has
    /// established the value's arity, so the read is in bounds.
    fn tuple_field(&mut self, value: Self::Value, index: usize) -> Result<Self::Value, CodegenError>;

    /// The code word a closure value carries. Only asked under a CLOSURE
    /// guard.
    fn closure_code(&mut self, value: Self::Value) -> Result<ir::Value, CodegenError>;
    /// The code addresses `targets` can have been minted through, or an error
    /// where this door cannot name a callable at all.
    fn callable_addresses(&mut self, targets: &FiniteSet<ClosureTarget>) -> Result<Vec<ir::Value>, CodegenError>;
}

/// Ask `predicate` of `value`: an `I8` flag, 1 where it is admitted.
pub(super) fn emit_runtime_type_test<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    value: E::Value,
    predicate: &RuntimeTypePredicate,
) -> Result<ir::Value, CodegenError> {
    let mut flag: Option<ir::Value> = None;
    // The three struct axes share one schema read, so whichever comes first
    // emits all three and the others fold into it.
    let mut structs_emitted = false;
    for axis in predicate.axes() {
        let is_struct_axis = matches!(
            axis,
            RuntimeTestAxis::Tuples | RuntimeTestAxis::NamedStructs | RuntimeTestAxis::OtherStructs
        );
        if is_struct_axis {
            if structs_emitted {
                continue;
            }
            structs_emitted = true;
        }
        let next = emit_axis(e, value, predicate, axis)?;
        flag = Some(match flag {
            None => next,
            Some(prev) => e.builder().ins().bor(prev, next),
        });
    }
    Ok(match flag {
        Some(flag) => flag,
        None => e.builder().ins().iconst(types::I8, 0),
    })
}

/// One axis' answer.
///
/// Exhaustive over the axis table on purpose: this match is what makes "every
/// axis the seat may treat as separation is decided by every lowering" true by
/// construction rather than by assertion (fz-kdt.119 item 6).
fn emit_axis<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    value: E::Value,
    predicate: &RuntimeTypePredicate,
    axis: RuntimeTestAxis,
) -> Result<ir::Value, CodegenError> {
    match axis {
        RuntimeTestAxis::Ints => {
            let ints = predicate.ints.clone();
            kind_guarded(e, value, ValueKind::INT, move |e, value| {
                let raw = e.raw_int(value)?;
                Ok(emit_i64_membership(e.builder(), raw, &ints))
            })
        }
        RuntimeTestAxis::Floats => {
            let floats = predicate.floats.clone();
            kind_guarded(e, value, ValueKind::FLOAT, move |e, value| {
                let bits = e.raw_float_bits(value)?;
                Ok(emit_u64_membership(e.builder(), bits, &floats))
            })
        }
        RuntimeTestAxis::Atoms => {
            let atom_ids = atom_id_membership(e, &predicate.atoms);
            kind_guarded(e, value, ValueKind::ATOM, move |e, value| {
                let raw = e.raw_atom(value)?;
                Ok(emit_i64_membership(e.builder(), raw, &atom_ids))
            })
        }
        RuntimeTestAxis::Lists => emit_list_axis(e, value, &predicate.lists),
        RuntimeTestAxis::Maps => e.kind_flag(value, ValueKind::MAP),
        RuntimeTestAxis::Binaries => e.kind_flag(value, ValueKind::BITSTRING),
        RuntimeTestAxis::Resources => e.kind_flag(value, ValueKind::RESOURCE),
        RuntimeTestAxis::Callables => emit_callable_axis(e, value, &predicate.callables),
        RuntimeTestAxis::Tuples | RuntimeTestAxis::NamedStructs | RuntimeTestAxis::OtherStructs => {
            emit_struct_axes(e, value, predicate)
        }
    }
}

/// Run `build` only where the value is of `kind`, and answer no elsewhere.
fn kind_guarded<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    value: E::Value,
    kind: ValueKind,
    build: impl FnOnce(&mut E, E::Value) -> Result<ir::Value, CodegenError>,
) -> Result<ir::Value, CodegenError> {
    match e.kind_evidence(value) {
        KindEvidence::Unboxed(known) if known == kind => return build(e, value),
        KindEvidence::Unboxed(_) | KindEvidence::Opaque => {
            return Ok(e.builder().ins().iconst(types::I8, 0));
        }
        KindEvidence::Tagged => {}
    }
    let is_kind = e.kind_flag(value, kind)?;
    guarded(e, is_kind, |e| build(e, value))
}

/// Emit `build` in a block reached only when `condition` holds, answering no
/// otherwise, and join the two answers.
fn guarded<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    condition: ir::Value,
    build: impl FnOnce(&mut E) -> Result<ir::Value, CodegenError>,
) -> Result<ir::Value, CodegenError> {
    let join = {
        let b = e.builder();
        let taken = b.create_block();
        let join = b.create_block();
        b.append_block_param(join, types::I8);
        let false8 = b.ins().iconst(types::I8, 0);
        b.ins().brif(condition, taken, &[], join, &[BlockArg::Value(false8)]);
        b.switch_to_block(taken);
        b.seal_block(taken);
        join
    };
    let answer = build(e)?;
    let b = e.builder();
    b.ins().jump(join, &[BlockArg::Value(answer)]);
    b.switch_to_block(join);
    b.seal_block(join);
    Ok(b.block_params(join)[0])
}

/// The atom axis in the runtime's own numbering.
fn atom_id_membership<'f, E: RuntimeTestEmitter<'f>>(e: &E, atoms: &FiniteSet<String>) -> FiniteSet<i64> {
    let name_to_id: HashMap<&str, u32> = e
        .atom_names()
        .iter()
        .enumerate()
        .map(|(index, name)| (name.as_str(), index as u32))
        .collect();
    FiniteSet {
        cofinite: atoms.cofinite,
        values: atoms
            .values
            .iter()
            .filter_map(|name| name_to_id.get(name.as_str()).copied().map(i64::from))
            .collect(),
    }
}

fn emit_list_axis<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    value: E::Value,
    lists: &FiniteSet<ListShape>,
) -> Result<ir::Value, CodegenError> {
    match (lists.contains(&ListShape::Empty), lists.contains(&ListShape::NonEmpty)) {
        (true, true) => e.kind_flag(value, ValueKind::LIST),
        (true, false) => e.empty_list_flag(value),
        (false, true) => e.cons_flag(value),
        (false, false) => Ok(e.builder().ins().iconst(types::I8, 0)),
    }
}

/// "Is this value one of THESE callables?"
///
/// A closure object's word at `+8` is the address of the callable boundary that
/// minted it, and a thin `MakeFnRef` singleton carries the same address, so one
/// comparison covers both shapes. Comparing addresses is what makes the check
/// O(1) and independent of captures: the boundary is chosen at mint time, and
/// the value remembers it.
fn emit_callable_axis<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    value: E::Value,
    callables: &FiniteSet<ClosureTarget>,
) -> Result<ir::Value, CodegenError> {
    if callables.is_any() {
        return e.kind_flag(value, ValueKind::CLOSURE);
    }
    let addresses = e.callable_addresses(callables)?;
    let cofinite = callables.cofinite;
    kind_guarded(e, value, ValueKind::CLOSURE, move |e, value| {
        let code = e.closure_code(value)?;
        let b = e.builder();
        let mut hit = b.ins().iconst(types::I8, 0);
        for address in addresses {
            let eq = b.ins().icmp(IntCC::Equal, code, address);
            hit = b.ins().bor(hit, eq);
        }
        Ok(if cofinite { b.ins().bxor_imm(hit, 1) } else { hit })
    })
}

/// The three struct axes, sharing one schema read.
fn emit_struct_axes<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    value: E::Value,
    predicate: &RuntimeTypePredicate,
) -> Result<ir::Value, CodegenError> {
    let arities = predicate.tuples.arities().clone();
    if predicate.allow_other_structs && arities.is_any() && predicate.named_structs.is_any() {
        return e.kind_flag(value, ValueKind::STRUCT);
    }
    let is_struct = e.kind_flag(value, ValueKind::STRUCT)?;
    guarded(e, is_struct, |e| {
        let schema = e.schema_id(value)?;
        let tuple_flag = emit_tuple_axis(e, value, predicate, schema)?;
        let named_flag = emit_named_struct_axis(e, schema, &predicate.named_structs);
        let other_flag = if predicate.allow_other_structs {
            let tuple_ids: Vec<u32> = e.tuple_schema_ids().values().copied().collect();
            let named_ids: Vec<u32> = e.named_schema_ids().values().copied().collect();
            let known_tuple = emit_any_schema_id_match(e.builder(), schema, tuple_ids);
            let known_named = emit_any_schema_id_match(e.builder(), schema, named_ids);
            let b = e.builder();
            let known_struct = b.ins().bor(known_tuple, known_named);
            b.ins().icmp_imm(IntCC::Equal, known_struct, 0)
        } else {
            e.builder().ins().iconst(types::I8, 0)
        };
        let b = e.builder();
        let tuple_or_named = b.ins().bor(tuple_flag, named_flag);
        Ok(b.ins().bor(tuple_or_named, other_flag))
    })
}

/// The tuple axis: an arity question, and -- where the projection could shape
/// the clauses -- each position's own question beneath it.
fn emit_tuple_axis<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    value: E::Value,
    predicate: &RuntimeTypePredicate,
    schema: ir::Value,
) -> Result<ir::Value, CodegenError> {
    let arities = predicate.tuples.arities().clone();
    if arities.is_none() {
        return Ok(e.builder().ins().iconst(types::I8, 0));
    }
    if !predicate.tuples.is_exact() {
        return Ok(emit_tuple_arity_membership(e, schema, &arities));
    }
    // An exact axis names a finite set of arities, one per shape, so shape
    // membership IS arity membership and the two are asked as one question.
    let mut arities_in_order: Vec<usize> = predicate.tuples.shapes().iter().map(Vec::len).collect();
    arities_in_order.sort_unstable();
    arities_in_order.dedup();
    let mut hit = e.builder().ins().iconst(types::I8, 0);
    for arity in arities_in_order {
        let Some(schema_id) = e.tuple_schema_ids().get(&arity).copied() else {
            // No schema was ever registered for this arity, so no value can
            // carry it: the shapes of this arity admit nothing.
            continue;
        };
        let is_arity = {
            let b = e.builder();
            let want = b.ins().iconst(types::I64, i64::from(schema_id));
            b.ins().icmp(IntCC::Equal, schema, want)
        };
        let shape_flag = guarded(e, is_arity, |e| emit_shapes_of_arity(e, value, predicate, arity))?;
        hit = e.builder().ins().bor(hit, shape_flag);
    }
    Ok(hit)
}

/// Whether some shape of `arity` matches the value's fields.
///
/// Reached only under a guard that has established the value IS a tuple of
/// this arity, which is what makes the field reads in bounds. The fields are
/// read once and shared across the shapes of the arity.
fn emit_shapes_of_arity<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    value: E::Value,
    predicate: &RuntimeTypePredicate,
    arity: usize,
) -> Result<ir::Value, CodegenError> {
    let mut fields: Vec<Option<E::Value>> = vec![None; arity];
    let mut hit = e.builder().ins().iconst(types::I8, 0);
    for shape in predicate.tuples.shapes().iter().filter(|shape| shape.len() == arity) {
        let mut matched: Option<ir::Value> = None;
        for (index, position) in shape.iter().enumerate() {
            if !lowering_tests_position(position) {
                continue;
            }
            let field = match fields[index] {
                Some(field) => field,
                None => {
                    let field = e.tuple_field(value, index)?;
                    fields[index] = Some(field);
                    field
                }
            };
            let flag = emit_runtime_type_test(e, field, position)?;
            matched = Some(match matched {
                None => flag,
                Some(prev) => e.builder().ins().band(prev, flag),
            });
        }
        // A shape every position of which is blind is the arity question and
        // nothing more, which the guard above already answered.
        let matched = matched.unwrap_or_else(|| e.builder().ins().iconst(types::I8, 1));
        hit = e.builder().ins().bor(hit, matched);
    }
    Ok(hit)
}

/// The arity-only reading: does the schema belong to an admitted arity, and is
/// it not one of the module's named structs?
fn emit_tuple_arity_membership<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    schema: ir::Value,
    arities: &FiniteSet<usize>,
) -> ir::Value {
    let named: Vec<u32> = e.named_schema_ids().values().copied().collect();
    let of_arities: Vec<u32> = arities
        .values
        .iter()
        .filter_map(|arity| e.tuple_schema_ids().get(arity).copied())
        .collect();
    if arities.is_any() {
        let known_named = emit_any_schema_id_match(e.builder(), schema, named);
        return e.builder().ins().icmp_imm(IntCC::Equal, known_named, 0);
    }
    if arities.cofinite {
        let known_named = emit_any_schema_id_match(e.builder(), schema, named);
        let excluded = emit_any_schema_id_match(e.builder(), schema, of_arities);
        let b = e.builder();
        let is_named = b.ins().icmp_imm(IntCC::NotEqual, known_named, 0);
        let excluded_ok = b.ins().icmp_imm(IntCC::Equal, excluded, 0);
        let not_named = b.ins().bxor_imm(is_named, 1);
        return b.ins().band(not_named, excluded_ok);
    }
    emit_any_schema_id_match(e.builder(), schema, of_arities)
}

fn emit_named_struct_axis<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    schema: ir::Value,
    names: &FiniteSet<String>,
) -> ir::Value {
    if names.is_none() {
        return e.builder().ins().iconst(types::I8, 0);
    }
    let all_named: Vec<u32> = e.named_schema_ids().values().copied().collect();
    if names.is_any() {
        return emit_any_schema_id_match(e.builder(), schema, all_named);
    }
    let relevant: Vec<u32> = names
        .values
        .iter()
        .filter_map(|name| e.named_schema_ids().get(name).copied())
        .collect();
    let matched = emit_any_schema_id_match(e.builder(), schema, relevant);
    if !names.cofinite {
        return matched;
    }
    let any_named = emit_any_schema_id_match(e.builder(), schema, all_named);
    let b = e.builder();
    let not_excluded = b.ins().icmp_imm(IntCC::Equal, matched, 0);
    b.ins().band(any_named, not_excluded)
}

pub(super) fn emit_any_schema_id_match(
    b: &mut FunctionBuilder<'_>,
    schema: ir::Value,
    ids: impl IntoIterator<Item = u32>,
) -> ir::Value {
    let mut matched = b.ins().iconst(types::I8, 0);
    for id in ids {
        let want = b.ins().iconst(types::I64, i64::from(id));
        let next = b.ins().icmp(IntCC::Equal, schema, want);
        matched = b.ins().bor(matched, next);
    }
    matched
}

/// Per-value membership check, shared by two callers: atom membership
/// (live in production, `values` routinely non-empty — atom ids are i64
/// here) and numeric (`ints`) membership, whose sole producer
/// (`Types::runtime_type_predicate`) always leaves `values` empty today —
/// numbers are a kind check, not a value-membership set, from that
/// pipeline. The numeric call site is dormant, not dead: it is the wiring
/// point for a deferred numeric-singleton-precision restoration to the
/// type lattice, and is kept for that reuse rather than pruned.
pub(super) fn emit_i64_membership(b: &mut FunctionBuilder<'_>, raw: ir::Value, values: &FiniteSet<i64>) -> ir::Value {
    if values.is_any() {
        return b.ins().iconst(types::I8, 1);
    }
    let mut eq_any = b.ins().iconst(types::I8, 0);
    for want in &values.values {
        let next = b.ins().icmp_imm(IntCC::Equal, raw, *want);
        eq_any = b.ins().bor(eq_any, next);
    }
    if values.cofinite {
        b.ins().icmp_imm(IntCC::Equal, eq_any, 0)
    } else {
        eq_any
    }
}

/// See [`emit_i64_membership`]: the `floats` counterpart, same dormant-wiring
/// status (`Types::runtime_type_predicate` always leaves `values` empty for
/// floats in production; no other caller populates it).
pub(super) fn emit_u64_membership(b: &mut FunctionBuilder<'_>, raw: ir::Value, values: &FiniteSet<u64>) -> ir::Value {
    if values.is_any() {
        return b.ins().iconst(types::I8, 1);
    }
    let mut eq_any = b.ins().iconst(types::I8, 0);
    for want in &values.values {
        let want = b.ins().iconst(types::I64, *want as i64);
        let next = b.ins().icmp(IntCC::Equal, raw, want);
        eq_any = b.ins().bor(eq_any, next);
    }
    if values.cofinite {
        b.ins().icmp_imm(IntCC::Equal, eq_any, 0)
    } else {
        eq_any
    }
}
