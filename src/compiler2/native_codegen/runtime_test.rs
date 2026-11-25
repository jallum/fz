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
//!
//! The OR is evaluated early and cheaply, as a branch: [`emit_runtime_type_branch`]
//! jumps to the caller's admit block from the first axis that admits and falls
//! to its reject block from the last that does not. An axis that costs one kind
//! comparison ([`is_kind_only`]) is asked first, so `is_map` of a map decides on
//! the kind alone and a value in a scalar lane is a plain jump. A caller that
//! wants the answer as a value takes [`emit_runtime_type_flag`], the same branch
//! with its two outcomes joined.
//!
//! The three struct axes share one schema read and divide the STRUCT values
//! between them. Which arities the other-structs axis takes is the predicate's
//! own answer -- exactly the ones the tuple axis does not name, through
//! [`crate::runtime_type_predicate::RuntimeTypePredicate::other_struct_arities`]
//! -- and the arity-only reading of both axes renders that set into schema
//! space through [`emit_arity_set_membership`]. An exact tuple axis instead
//! fuses the arity question with the per-arity shape guard, because a value's
//! arity chooses which shapes it can match. Reading the door's own registered schemas
//! instead would give a different answer, because a schema is registered for
//! every arity a test asks about AT EVERY DEPTH while naming is a top-level
//! reading.
//!
//! A map in the entries layout names a module where an atom is under its
//! `__struct__` key, and it is then a value of that struct's type. The maps
//! axis and the named-structs axis share that one read: the first admits the
//! maps naming no module, the second the maps naming an admitted one.
//!
//! A named struct and a tuple are both `ValueKind::STRUCT` at runtime. The
//! struct header's named bit says which, so "any named struct" and "no named
//! struct" are one test of the header word, and only a question about
//! particular names or arities compares schema ids. The named-struct and arity
//! readings stay separate functions. Folding them into one schema-id question
//! would lose the distinction
//! [`crate::runtime_type_predicate::RuntimeTypePredicate::tuple_positions`]
//! depends on: a named struct never answers a tuple's position questions.

use crate::fast_hash::HashMap;
use crate::fz_ir::ModuleAtoms;

use cranelift_codegen::ir::{self, BlockArg, InstBuilder, condcodes::IntCC, types};
use cranelift_frontend::FunctionBuilder;
use fz_runtime::any_value::ValueKind;
use fz_runtime::heap::NamedSchema;

use crate::finite_set::FiniteSet;
use crate::runtime_type_predicate::{
    CallableShapes, CaptureQuestions, ListShape, ListShapes, RuntimeTestAxis, RuntimeTypePredicate, TuplePositions,
};

use super::CodegenError;

/// What a door already knows of a value's kind before any test runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum KindEvidence {
    /// A tagged any-value: the test must read the tag.
    Tagged,
    /// Held in an unboxed representation, which IS its kind.
    Unboxed(ValueKind),
    /// A ref word whose kind was fixed when compiling: a static object. No
    /// tag is read, and a question about any other kind answers no.
    Static(ValueKind),
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
    fn atoms(&self) -> &ModuleAtoms;
    fn tuple_schema_ids(&self) -> &HashMap<usize, u32>;
    fn named_schema_ids(&self) -> &HashMap<fz_runtime::module_name::ModuleName, u32>;

    fn kind_evidence(&self, value: Self::Value) -> KindEvidence;
    fn kind_flag(&mut self, value: Self::Value, kind: ValueKind) -> Result<ir::Value, CodegenError>;
    /// Whether the value's kind is one of `kinds`, as an `I8` flag: the kind is
    /// read once and tested against a constant mask.
    fn kind_in(&mut self, value: Self::Value, kinds: &[ValueKind]) -> Result<ir::Value, CodegenError>;

    /// The bit length of a bitstring value. Only asked under a guard that has
    /// established the value IS a bitstring.
    fn bitstring_bit_len(&mut self, value: Self::Value) -> Result<ir::Value, CodegenError>;

    fn raw_int(&mut self, value: Self::Value) -> Result<ir::Value, CodegenError>;
    fn raw_float_bits(&mut self, value: Self::Value) -> Result<ir::Value, CodegenError>;
    fn raw_atom(&mut self, value: Self::Value) -> Result<ir::Value, CodegenError>;

    fn empty_list_flag(&mut self, value: Self::Value) -> Result<ir::Value, CodegenError>;
    fn cons_flag(&mut self, value: Self::Value) -> Result<ir::Value, CodegenError>;

    /// The value's schema id, widened to `I64`. Only asked under a STRUCT
    /// guard.
    fn schema_id(&mut self, value: Self::Value) -> Result<ir::Value, CodegenError>;
    /// Whether the struct is a named struct, as an `I8` flag. Only asked under
    /// a STRUCT guard.
    fn struct_is_named(&mut self, value: Self::Value) -> Result<ir::Value, CodegenError>;
    /// The `NamedSchema` word of the module a map names, widened to `I64`.
    /// Only asked under a MAP guard.
    fn map_named_schema(&mut self, value: Self::Value) -> Result<ir::Value, CodegenError>;
    /// Field `index` of a struct value. Only asked under a guard that has
    /// established the value's arity, so the read is in bounds.
    fn tuple_field(&mut self, value: Self::Value, index: usize) -> Result<Self::Value, CodegenError>;

    /// The first element of a cons cell. Only asked under a guard that has
    /// established the value IS a cons cell, so the read is in bounds.
    fn list_head(&mut self, value: Self::Value) -> Result<Self::Value, CodegenError>;

    /// The code word a closure value carries. Only asked under a CLOSURE
    /// guard.
    fn closure_code(&mut self, value: Self::Value) -> Result<ir::Value, CodegenError>;
    /// How many arguments a closure value takes, as an `I64`. Only asked
    /// under a CLOSURE guard.
    fn closure_arity(&mut self, value: Self::Value) -> Result<ir::Value, CodegenError>;
    /// The code address of every construction the test lists, with how it
    /// lists it -- the listed side; the emitter applies the cofinite
    /// complement itself. An error where this door cannot name a callable at
    /// all.
    fn callable_constructions(&mut self, callables: &CallableShapes) -> Result<Vec<ConstructionTest>, CodegenError>;
    /// Capture `index` of a closure value, as the value it holds whatever
    /// layout the construction stored it in. Only asked under a guard that has
    /// established the closure's construction, so the read is in bounds.
    fn closure_capture(&mut self, value: Self::Value, index: usize) -> Result<Self::Value, CodegenError>;
}

/// One construction a callable test lists, by its code address.
pub(super) struct ConstructionTest {
    pub(super) address: ir::Value,
    /// `None`: every closure of the construction is listed. `Some`: a closure
    /// is listed when its held values answer every question of some
    /// alternative.
    pub(super) by_captures: Option<Vec<CaptureQuestions>>,
}

/// `predicate` asked of `value` as an `I8` flag, for a caller that wants the
/// answer as a value. It is the branch form with its two outcomes joined.
pub(super) fn emit_runtime_type_flag<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    value: E::Value,
    predicate: &RuntimeTypePredicate,
) -> Result<ir::Value, CodegenError> {
    joined(e, |e, admit, reject| {
        emit_runtime_type_branch(e, value, predicate, admit, reject)
    })
}

/// The answer of a branching `build` as an `I8` flag: `build` ends the current
/// block by branching to the `admit` or `reject` block it is given, and the two
/// outcomes are joined into 1 and 0.
fn joined<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    build: impl FnOnce(&mut E, ir::Block, ir::Block) -> Result<(), CodegenError>,
) -> Result<ir::Value, CodegenError> {
    let (admit, reject, join) = {
        let b = e.builder();
        let join = b.create_block();
        b.append_block_param(join, types::I8);
        (b.create_block(), b.create_block(), join)
    };
    build(e, admit, reject)?;
    let b = e.builder();
    for (outcome, answer) in [(admit, 1), (reject, 0)] {
        b.switch_to_block(outcome);
        b.seal_block(outcome);
        let answer = b.ins().iconst(types::I8, answer);
        b.ins().jump(join, &[BlockArg::Value(answer)]);
    }
    b.switch_to_block(join);
    b.seal_block(join);
    Ok(b.block_params(join)[0])
}

/// Whether a value held unboxed in a scalar lane settles `predicate` without
/// a test: such a value is of one kind, so a predicate that admits all of that
/// kind or none of it has one answer. A caller that branches on the answer
/// then lowers only the successor that can be reached.
pub(super) fn settled_by_lane<'f, E: RuntimeTestEmitter<'f>>(
    e: &E,
    value: E::Value,
    predicate: &RuntimeTypePredicate,
) -> Option<bool> {
    match e.kind_evidence(value) {
        KindEvidence::Unboxed(kind) => predicate.settled_for_scalar_lane(kind),
        KindEvidence::Tagged | KindEvidence::Static(_) | KindEvidence::Opaque => None,
    }
}

/// Ask `predicate` of `value`, ending the current block by branching to
/// `admit` where the value is admitted and to `reject` where it is not.
///
/// Each axis that admits jumps straight to `admit`; the last to fail falls to
/// `reject`. A question the value's lane settles is a plain jump. Axes are
/// asked in turn, so the code of an axis runs only for a value the axes before
/// it did not admit.
pub(super) fn emit_runtime_type_branch<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    value: E::Value,
    predicate: &RuntimeTypePredicate,
    admit: ir::Block,
    reject: ir::Block,
) -> Result<(), CodegenError> {
    if let Some(admitted) = settled_by_lane(e, value, predicate) {
        e.builder().ins().jump(if admitted { admit } else { reject }, &[]);
        return Ok(());
    }
    let mut axes: Vec<RuntimeTestAxis> = predicate.axes().collect();
    axes.sort_by_key(|axis| !is_kind_only(*axis, predicate));
    let mut asked = SharedReads::default();
    for axis in axes {
        let next = e.builder().create_block();
        if emit_axis(e, value, predicate, axis, &mut asked, admit, next)? {
            let b = e.builder();
            b.switch_to_block(next);
            b.seal_block(next);
        }
    }
    e.builder().ins().jump(reject, &[]);
    Ok(())
}

/// Whether asking `axis` costs one comparison of the value's kind and reads
/// nothing else off it. Such axes are asked first, and an axis that reads the
/// value further is asked only of a value they have not admitted.
fn is_kind_only(axis: RuntimeTestAxis, predicate: &RuntimeTypePredicate) -> bool {
    match axis {
        RuntimeTestAxis::Resources | RuntimeTestAxis::Opaques => true,
        RuntimeTestAxis::Binaries => !predicate.bitstrings.asks_length(),
        RuntimeTestAxis::Maps => predicate.maps && predicate.named_structs.is_any(),
        RuntimeTestAxis::Ints
        | RuntimeTestAxis::Floats
        | RuntimeTestAxis::Atoms
        | RuntimeTestAxis::Lists
        | RuntimeTestAxis::Tuples
        | RuntimeTestAxis::NamedStructs
        | RuntimeTestAxis::OtherStructs
        | RuntimeTestAxis::Callables => false,
    }
}

/// The reads several axes share, each emitted once per test.
///
/// The three struct axes read one schema id off a struct. The maps axis and
/// the named-structs axis read one module off a map in the entries layout,
/// because such a map is a struct exactly when it names one.
#[derive(Default)]
struct SharedReads {
    structs: bool,
    entries_maps: bool,
}

impl SharedReads {
    /// Ask the struct axes unless an earlier axis already did.
    fn structs_once<'f, E: RuntimeTestEmitter<'f>>(
        &mut self,
        e: &mut E,
        value: E::Value,
        predicate: &RuntimeTypePredicate,
        admit: ir::Block,
        miss: ir::Block,
    ) -> Result<bool, CodegenError> {
        if std::mem::replace(&mut self.structs, true) {
            return Ok(false);
        }
        emit_struct_axes(e, value, predicate, admit, miss)?;
        Ok(true)
    }

    /// Ask the entries-layout map axes unless an earlier axis already did.
    fn entries_maps_once<'f, E: RuntimeTestEmitter<'f>>(
        &mut self,
        e: &mut E,
        value: E::Value,
        predicate: &RuntimeTypePredicate,
        admit: ir::Block,
        miss: ir::Block,
    ) -> Result<bool, CodegenError> {
        if std::mem::replace(&mut self.entries_maps, true) {
            return Ok(false);
        }
        emit_entries_map_axes(e, value, predicate, admit, miss)?;
        Ok(true)
    }
}

/// One axis' answer, as a branch: the current block ends by branching to
/// `admit` where the axis admits the value and to `miss` where it does not.
/// Whether it did: an axis whose question an earlier axis already answered
/// emits nothing and leaves the block open.
///
/// Exhaustive over the axis table on purpose: this match is what makes "every
/// axis the seat may treat as separation is decided by every lowering" true by
/// construction rather than by assertion (fz-kdt.119 item 6).
fn emit_axis<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    value: E::Value,
    predicate: &RuntimeTypePredicate,
    axis: RuntimeTestAxis,
    asked: &mut SharedReads,
    admit: ir::Block,
    miss: ir::Block,
) -> Result<bool, CodegenError> {
    let flag = match axis {
        RuntimeTestAxis::Ints => {
            let ints = predicate.ints.clone();
            kind_guarded(e, value, ValueKind::INT, admit, miss, move |e, value| {
                let raw = e.raw_int(value)?;
                Ok(emit_i64_membership(e.builder(), raw, &ints))
            })?;
            return Ok(true);
        }
        RuntimeTestAxis::Floats => {
            let floats = predicate.floats.clone();
            kind_guarded(e, value, ValueKind::FLOAT, admit, miss, move |e, value| {
                let bits = e.raw_float_bits(value)?;
                Ok(emit_u64_membership(e.builder(), bits, &floats))
            })?;
            return Ok(true);
        }
        RuntimeTestAxis::Atoms => {
            let atom_ids = atom_id_membership(e, &predicate.atoms);
            kind_guarded(e, value, ValueKind::ATOM, admit, miss, move |e, value| {
                let raw = e.raw_atom(value)?;
                Ok(emit_i64_membership(e.builder(), raw, &atom_ids))
            })?;
            return Ok(true);
        }
        RuntimeTestAxis::Lists => emit_list_axis(e, value, &predicate.lists)?,
        RuntimeTestAxis::Maps => return asked.entries_maps_once(e, value, predicate, admit, miss),
        RuntimeTestAxis::Binaries => {
            // Every representation a binary is held in, so a shared-buffer
            // binary answers the same as an inline one.
            let is_bitstring = e.kind_in(value, &ValueKind::BINARY_REPRS)?;
            let admitted = predicate.bitstrings;
            if !admitted.asks_length() {
                is_bitstring
            } else {
                let whole_bytes = admitted.whole_bytes;
                guarded_branch(e, is_bitstring, admit, miss, move |e| {
                    let bit_len = e.bitstring_bit_len(value)?;
                    let partial_bits = e.builder().ins().band_imm_u(bit_len, 7);
                    let cc = if whole_bytes { IntCC::Equal } else { IntCC::NotEqual };
                    Ok(e.builder().ins().icmp_imm_s(cc, partial_bits, 0))
                })?;
                return Ok(true);
            }
        }
        RuntimeTestAxis::Resources => e.kind_flag(value, ValueKind::RESOURCE)?,
        RuntimeTestAxis::Opaques => {
            let kinds: Vec<ValueKind> = [crate::types::BuiltinOpaque::Pid, crate::types::BuiltinOpaque::Ref]
                .into_iter()
                .filter(|opaque| predicate.opaques.contains(opaque))
                .map(|opaque| crate::runtime_type_predicate::kind_of_opaque(opaque).expect("a pid or reference kind"))
                .collect();
            if kinds.is_empty() {
                return Ok(false);
            }
            e.kind_in(value, &kinds)?
        }
        RuntimeTestAxis::Callables => {
            emit_callable_axis(e, value, &predicate.callables, admit, miss)?;
            return Ok(true);
        }
        RuntimeTestAxis::Tuples | RuntimeTestAxis::OtherStructs => {
            return asked.structs_once(e, value, predicate, admit, miss);
        }
        RuntimeTestAxis::NamedStructs => {
            let after_structs = e.builder().create_block();
            let structs = asked.structs_once(e, value, predicate, admit, after_structs)?;
            if structs {
                let b = e.builder();
                b.switch_to_block(after_structs);
                b.seal_block(after_structs);
            }
            let maps = asked.entries_maps_once(e, value, predicate, admit, miss)?;
            if structs && !maps {
                e.builder().ins().jump(miss, &[]);
            }
            return Ok(structs || maps);
        }
    };
    e.builder().ins().brif(flag, admit, &[], miss, &[]);
    Ok(true)
}

/// Run `build` only where the value is of `kind`, and branch on its flag; the
/// value of another kind goes to `miss`.
fn kind_guarded<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    value: E::Value,
    kind: ValueKind,
    admit: ir::Block,
    miss: ir::Block,
    build: impl FnOnce(&mut E, E::Value) -> Result<ir::Value, CodegenError>,
) -> Result<(), CodegenError> {
    match e.kind_evidence(value) {
        KindEvidence::Unboxed(known) | KindEvidence::Static(known) if known == kind => {
            let flag = build(e, value)?;
            e.builder().ins().brif(flag, admit, &[], miss, &[]);
            Ok(())
        }
        KindEvidence::Unboxed(_) | KindEvidence::Static(_) | KindEvidence::Opaque => {
            e.builder().ins().jump(miss, &[]);
            Ok(())
        }
        KindEvidence::Tagged => {
            let is_kind = e.kind_flag(value, kind)?;
            guarded_branch(e, is_kind, admit, miss, |e| build(e, value))
        }
    }
}

/// Emit `build` in a block reached only when `condition` holds, and branch on
/// its flag; where `condition` does not hold the value goes to `miss`.
fn guarded_branch<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    condition: ir::Value,
    admit: ir::Block,
    miss: ir::Block,
    build: impl FnOnce(&mut E) -> Result<ir::Value, CodegenError>,
) -> Result<(), CodegenError> {
    {
        let b = e.builder();
        let taken = b.create_block();
        b.ins().brif(condition, taken, &[], miss, &[]);
        b.switch_to_block(taken);
        b.seal_block(taken);
    }
    let flag = build(e)?;
    e.builder().ins().brif(flag, admit, &[], miss, &[]);
    Ok(())
}

/// The flag of `build`, asked only where `condition` holds and no elsewhere:
/// for a question nested inside another test's own flag.
fn guarded<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    condition: ir::Value,
    build: impl FnOnce(&mut E) -> Result<ir::Value, CodegenError>,
) -> Result<ir::Value, CodegenError> {
    joined(e, |e, admit, miss| guarded_branch(e, condition, admit, miss, build))
}

/// The atom axis in the runtime's own numbering.
fn atom_id_membership<'f, E: RuntimeTestEmitter<'f>>(e: &E, atoms: &FiniteSet<String>) -> FiniteSet<i64> {
    FiniteSet {
        cofinite: atoms.cofinite,
        values: atoms
            .values
            .iter()
            .map(|name| match e.atoms().id_of(name.as_str()) {
                Some(id) => i64::from(id),
                None => panic!("the atom table lacks :{name}, which a type test names"),
            })
            .collect(),
    }
}

/// The list axis: a shape question, and -- where the projection could name the
/// element type -- the first element's own question, asked INSIDE the cons
/// branch and nowhere else.
///
/// The head costs one load and one nested test, and a head-blind or `[]`-only
/// axis emits exactly the code it emitted before fz-kdt.107 step 3. The
/// disjunction over `heads` mirrors the interpreter's `matches_list_elements`
/// under `PositionScope::Lowered`: one head question per cons-admitting clause,
/// and a cons cell is admitted when any of them says so. The interpreter can
/// also ask that axis under `PositionScope::Full`, which walks every element --
/// what this emitter deliberately cannot afford, and what the
/// surface-membership tripwire measures the difference of.
fn emit_list_axis<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    value: E::Value,
    lists: &ListShapes,
) -> Result<ir::Value, CodegenError> {
    let shapes = lists.shapes();
    let (empty, non_empty) = (
        shapes.contains(&ListShape::Empty),
        shapes.contains(&ListShape::NonEmpty),
    );
    if !non_empty {
        return if empty {
            e.empty_list_flag(value)
        } else {
            Ok(e.builder().ins().iconst(types::I8, 0))
        };
    }
    if !lists.asks_the_head() {
        return if empty {
            e.kind_flag(value, ValueKind::LIST)
        } else {
            e.cons_flag(value)
        };
    }
    let heads = lists.heads().to_vec();
    let is_cons = e.cons_flag(value)?;
    let admitted = guarded(e, is_cons, move |e| {
        let head = e.list_head(value)?;
        let mut flag = e.builder().ins().iconst(types::I8, 0);
        for question in &heads {
            let next = emit_runtime_type_flag(e, head, question)?;
            flag = e.builder().ins().bor(flag, next);
        }
        Ok(flag)
    })?;
    if !empty {
        return Ok(admitted);
    }
    let is_empty = e.empty_list_flag(value)?;
    Ok(e.builder().ins().bor(is_empty, admitted))
}

/// "Is this value one of THESE constructions, taking one of THESE numbers of
/// arguments?"
///
/// A closure object's word at `+8` is the address of the callable boundary that
/// minted it, and a thin `MakeFnRef` static closure carries the same address, so one
/// comparison covers both shapes. A boundary is one function at one capture
/// layout, so WHICH boundaries a test lists is decided here at codegen from
/// each boundary's own construction shape, and the value pays one address
/// compare per listed boundary. A boundary whose annotation the test only
/// overlaps is listed by its captures: once the address matches, each captured
/// value is read -- its own kind byte makes the read independent of the layout
/// the construction stored -- and asked the test's question.
fn emit_callable_axis<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    value: E::Value,
    callables: &CallableShapes,
    admit: ir::Block,
    miss: ir::Block,
) -> Result<(), CodegenError> {
    if callables.is_any() {
        let flag = e.kind_flag(value, ValueKind::CLOSURE)?;
        e.builder().ins().brif(flag, admit, &[], miss, &[]);
        return Ok(());
    }
    let constructions = if callables.targets().is_any() {
        None
    } else {
        Some(e.callable_constructions(callables)?)
    };
    let cofinite = callables.targets().cofinite;
    kind_guarded(e, value, ValueKind::CLOSURE, admit, miss, move |e, value| {
        let of_arity = emit_closure_arity_flag(e, value, callables.arities())?;
        let Some(constructions) = constructions else {
            return Ok(of_arity);
        };
        let code = e.closure_code(value)?;
        let mut hit = e.builder().ins().iconst(types::I8, 0);
        for construction in constructions {
            let eq = e.builder().ins().icmp(IntCC::Equal, code, construction.address);
            let listed = match construction.by_captures {
                None => eq,
                Some(alternatives) => guarded(e, eq, move |e| emit_capture_alternatives(e, value, &alternatives))?,
            };
            hit = e.builder().ins().bor(hit, listed);
        }
        let b = e.builder();
        let named = if cofinite { b.ins().bxor_imm_u(hit, 1) } else { hit };
        Ok(b.ins().band(of_arity, named))
    })
}

/// Whether some alternative has every capture it names answer its question.
fn emit_capture_alternatives<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    closure: E::Value,
    alternatives: &[CaptureQuestions],
) -> Result<ir::Value, CodegenError> {
    let mut any = e.builder().ins().iconst(types::I8, 0);
    for questions in alternatives {
        let mut all = e.builder().ins().iconst(types::I8, 1);
        for (index, question) in questions {
            let capture = e.closure_capture(closure, *index)?;
            let flag = emit_runtime_type_flag(e, capture, question)?;
            all = e.builder().ins().band(all, flag);
        }
        any = e.builder().ins().bor(any, all);
    }
    Ok(any)
}

/// "Does this closure take one of THESE numbers of arguments?" The closure's
/// header holds the number, so the test reads it once and compares it with
/// each arity the set lists.
fn emit_closure_arity_flag<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    value: E::Value,
    arities: &FiniteSet<usize>,
) -> Result<ir::Value, CodegenError> {
    if arities.is_any() {
        return Ok(e.builder().ins().iconst(types::I8, 1));
    }
    let arity = e.closure_arity(value)?;
    let b = e.builder();
    let mut hit = b.ins().iconst(types::I8, 0);
    for listed in &arities.values {
        let eq = b.ins().icmp_imm_s(IntCC::Equal, arity, *listed as i64);
        hit = b.ins().bor(hit, eq);
    }
    Ok(if arities.cofinite {
        b.ins().bxor_imm_u(hit, 1)
    } else {
        hit
    })
}

/// The three struct axes, sharing one schema read.
fn emit_struct_axes<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    value: E::Value,
    predicate: &RuntimeTypePredicate,
    admit: ir::Block,
    miss: ir::Block,
) -> Result<(), CodegenError> {
    // Where the other-structs axis takes every arity and the named-structs axis
    // every name, the three axes between them admit every struct, so the kind
    // is the whole answer and no schema need be read.
    if predicate.other_struct_arities().is_any() && predicate.named_structs.is_any() {
        let flag = e.kind_flag(value, ValueKind::STRUCT)?;
        e.builder().ins().brif(flag, admit, &[], miss, &[]);
        return Ok(());
    }
    let is_struct = e.kind_flag(value, ValueKind::STRUCT)?;
    guarded_branch(e, is_struct, admit, miss, |e| {
        let mut reads = StructReads::of(value);
        let tuple_flag = emit_tuple_axis(e, value, predicate, &mut reads)?;
        let named_flag = emit_named_struct_axis(e, &predicate.named_structs, &mut reads)?;
        let other_flag = emit_arity_set_membership(e, &predicate.other_struct_arities(), &mut reads)?;
        let b = e.builder();
        let tuple_or_named = b.ins().bor(tuple_flag, named_flag);
        Ok(b.ins().bor(tuple_or_named, other_flag))
    })
}

/// What the struct axes read off a struct, each read emitted at most once per
/// test and only by an axis that asks it.
struct StructReads<V> {
    value: V,
    schema: Option<ir::Value>,
    named: Option<ir::Value>,
}

impl<V: Copy> StructReads<V> {
    fn of(value: V) -> Self {
        Self {
            value,
            schema: None,
            named: None,
        }
    }

    /// The schema id, widened to `I64`.
    fn schema<'f, E: RuntimeTestEmitter<'f, Value = V>>(&mut self, e: &mut E) -> Result<ir::Value, CodegenError> {
        if let Some(schema) = self.schema {
            return Ok(schema);
        }
        let schema = e.schema_id(self.value)?;
        self.schema = Some(schema);
        Ok(schema)
    }

    /// The `I8` flag that says the struct is a named struct.
    fn named<'f, E: RuntimeTestEmitter<'f, Value = V>>(&mut self, e: &mut E) -> Result<ir::Value, CodegenError> {
        if let Some(named) = self.named {
            return Ok(named);
        }
        let named = e.struct_is_named(self.value)?;
        self.named = Some(named);
        Ok(named)
    }
}

/// A map in the entries layout: the maps axis admits it where it names no
/// module, and the named-structs axis where the module it names is admitted.
fn emit_entries_map_axes<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    value: E::Value,
    predicate: &RuntimeTypePredicate,
    admit: ir::Block,
    miss: ir::Block,
) -> Result<(), CodegenError> {
    let (plain, names) = (predicate.maps, &predicate.named_structs);
    if plain && names.is_any() {
        let flag = e.kind_flag(value, ValueKind::MAP)?;
        e.builder().ins().brif(flag, admit, &[], miss, &[]);
        return Ok(());
    }
    if !plain && names.is_none() {
        e.builder().ins().jump(miss, &[]);
        return Ok(());
    }
    let listed: Vec<u32> = names
        .values
        .iter()
        .filter_map(|name| e.named_schema_ids().get(name).copied())
        .collect();
    let names_cofinite = names.cofinite;
    kind_guarded(e, value, ValueKind::MAP, admit, miss, move |e, value| {
        let named = e.map_named_schema(value)?;
        let b = e.builder();
        let names_none = b
            .ins()
            .icmp_imm_s(IntCC::Equal, named, i64::from(NamedSchema::NONE_WORD));
        let is_listed = emit_any_schema_id_match(b, named, listed);
        let module_admitted = if names_cofinite {
            let unlisted = b.ins().bxor_imm_u(is_listed, 1);
            let names_some = b.ins().bxor_imm_u(names_none, 1);
            b.ins().band(names_some, unlisted)
        } else {
            is_listed
        };
        Ok(if plain {
            b.ins().bor(names_none, module_admitted)
        } else {
            module_admitted
        })
    })
}

/// The tuple axis: an arity question, and -- where the projection could shape
/// the clauses -- each position's own question beneath it.
fn emit_tuple_axis<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    value: E::Value,
    predicate: &RuntimeTypePredicate,
    reads: &mut StructReads<E::Value>,
) -> Result<ir::Value, CodegenError> {
    let arities = predicate.tuples.arities();
    if arities.is_none() {
        return Ok(e.builder().ins().iconst(types::I8, 0));
    }
    if !predicate.tuples.is_exact() {
        return emit_arity_set_membership(e, arities, reads);
    }
    // An exact axis derives its arities from its shapes' lengths, so shape
    // membership IS arity membership and the two are asked as one question.
    let schema = reads.schema(e)?;
    let arities_in_order: Vec<usize> = arities.values.iter().copied().collect();
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
    let shapes = match predicate.tuple_positions(arity) {
        TuplePositions::Never => return Ok(e.builder().ins().iconst(types::I8, 0)),
        TuplePositions::Always => return Ok(e.builder().ins().iconst(types::I8, 1)),
        TuplePositions::AnyOf(shapes) => shapes,
    };
    let mut fields: Vec<Option<E::Value>> = vec![None; arity];
    let mut hit = e.builder().ins().iconst(types::I8, 0);
    for shape in shapes {
        let mut matched: Option<ir::Value> = None;
        for (index, position) in shape.iter().enumerate() {
            let field = match fields[index] {
                Some(field) => field,
                None => {
                    let field = e.tuple_field(value, index)?;
                    fields[index] = Some(field);
                    field
                }
            };
            let flag = emit_runtime_type_flag(e, field, position)?;
            matched = Some(match matched {
                None => flag,
                Some(prev) => e.builder().ins().band(prev, flag),
            });
        }
        // Only an arity-0 shape emits no position test; its question is the
        // arity check the guard above already answered.
        let matched = matched.unwrap_or_else(|| e.builder().ins().iconst(types::I8, 1));
        hit = e.builder().ins().bor(hit, matched);
    }
    Ok(hit)
}

/// Whether the schema is an UNNAMED struct whose arity `arities` admits.
///
/// One rendering of an arity set into schema space, for both struct axes that
/// have one: the tuple axis asks it of the arities it names, the other-structs
/// axis of the complement those leave behind. A tuple is a struct the module
/// never named, so a cofinite set is "not a named schema, and not one of the
/// excluded arities' schemas" while a finite one is exactly the schemas of the
/// arities it lists -- and an arity no schema was registered for names no
/// value, so it drops out of either reading rather than refusing to compile.
/// `RuntimeValueReader::unnamed_struct_of_arity` is the interpreter's twin.
///
/// Reached only under a STRUCT guard, which is what makes `schema` this value's
/// own schema id.
fn emit_arity_set_membership<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    arities: &FiniteSet<usize>,
    reads: &mut StructReads<E::Value>,
) -> Result<ir::Value, CodegenError> {
    let of_arities: Vec<u32> = arities
        .values
        .iter()
        .filter_map(|arity| e.tuple_schema_ids().get(arity).copied())
        .collect();
    if !arities.cofinite {
        if of_arities.is_empty() {
            return Ok(e.builder().ins().iconst(types::I8, 0));
        }
        let schema = reads.schema(e)?;
        return Ok(emit_any_schema_id_match(e.builder(), schema, of_arities));
    }
    let is_named = reads.named(e)?;
    let not_named = e.builder().ins().bxor_imm_u(is_named, 1);
    if arities.is_any() {
        return Ok(not_named);
    }
    let schema = reads.schema(e)?;
    let b = e.builder();
    let excluded = emit_any_schema_id_match(b, schema, of_arities);
    let excluded_ok = b.ins().icmp_imm_s(IntCC::Equal, excluded, 0);
    Ok(b.ins().band(not_named, excluded_ok))
}

/// Whether the struct is one of the named structs `names` admits. Every named
/// struct is one question of its header's named bit; particular names are
/// questions of its schema id.
fn emit_named_struct_axis<'f, E: RuntimeTestEmitter<'f>>(
    e: &mut E,
    names: &FiniteSet<fz_runtime::module_name::ModuleName>,
    reads: &mut StructReads<E::Value>,
) -> Result<ir::Value, CodegenError> {
    if names.is_none() {
        return Ok(e.builder().ins().iconst(types::I8, 0));
    }
    if names.is_any() {
        return reads.named(e);
    }
    let relevant: Vec<u32> = names
        .values
        .iter()
        .filter_map(|name| e.named_schema_ids().get(name).copied())
        .collect();
    let schema = reads.schema(e)?;
    let matched = emit_any_schema_id_match(e.builder(), schema, relevant);
    if !names.cofinite {
        return Ok(matched);
    }
    let is_named = reads.named(e)?;
    let b = e.builder();
    let not_excluded = b.ins().icmp_imm_s(IntCC::Equal, matched, 0);
    Ok(b.ins().band(is_named, not_excluded))
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
        let next = b.ins().icmp_imm_s(IntCC::Equal, raw, *want);
        eq_any = b.ins().bor(eq_any, next);
    }
    if values.cofinite {
        b.ins().icmp_imm_s(IntCC::Equal, eq_any, 0)
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
        b.ins().icmp_imm_s(IntCC::Equal, eq_any, 0)
    } else {
        eq_any
    }
}
