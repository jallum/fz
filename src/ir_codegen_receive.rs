//! fz-70q (B3) — selective-receive matcher fn codegen.
//!
//! Emits the leaf matcher fn for a `Term::ReceiveMatched`. The matcher
//! ABI matches `fz_runtime::park::MatcherFn` (see runtime/src/park.rs):
//!
//! ```text
//! extern "C" fn(msg: u64, pinned: *const u64, out: *mut u64) -> u32
//! ```
//!
//! - `msg`: candidate message (raw FzValue bits).
//! - `pinned`: pointer to `[u64; n_pinned]` with each `^name`'s value
//!   bits, in the order they appear in `Term::ReceiveMatched::pinned`.
//! - `out`: caller-supplied `[u64; bound_arity]` scratch buffer; the
//!   matcher writes the winning clause's bound-var values here.
//! - returns `0` on miss; `k > 0` is the 1-based clause index (caller
//!   indexes `clause_bodies[k-1]`).
//!
//! Semantic spec: `src/ir_interp.rs::try_match_pattern`.
//!
//! This file owns only the matcher fn body; the park-site that calls
//! into it (allocate `ParkRecord`, materialize closures, dispatch
//! `fz_receive_park_matched`) is fz-70q.3 work in `compile_block_terminator`.
//!
//! Until fz-70q.3 wires the park site, the matcher emitter has no
//! production caller — it is only exercised by the tests in this file.
//! `#[allow(dead_code)]` on the helpers is the staging marker; it
//! retracts the moment fz-70q.3's park-site lookup starts calling
//! `emit_matcher_body`.

#![allow(dead_code)]

use crate::ast::Pattern;
use crate::fz_ir::{Module, ReceiveClause, Var};
use crate::ir_codegen::{
    CodegenError, EMPTY_LIST_BITS, HEADER_SIZE, NIL_BITS, SLOT_BYTES, TAG_ATOM, TAG_INT, TAG_MASK,
    TAG_PTR, TRUE_BITS, emit_fn_body,
};
use crate::pattern_matrix::{
    BodyId, Decision, Matrix, Row, SubjectRef, SwitchKey, SwitchKind, compile as compile_matrix,
};
use cranelift_codegen::ir::{
    self, AbiParam, InstBuilder, MemFlags, Signature, condcodes::IntCC, types,
};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{FuncId, Linkage};
use std::collections::HashMap;

/// Cranelift signature for the matcher fn family. Matches
/// `fz_runtime::park::MatcherFn`.
pub(crate) fn matcher_signature() -> Signature {
    let mut sig = Signature::new(CallConv::SystemV);
    sig.params.push(AbiParam::new(types::I64)); // msg
    sig.params.push(AbiParam::new(types::I64)); // pinned_ptr
    sig.params.push(AbiParam::new(types::I64)); // out_ptr
    sig.returns.push(AbiParam::new(types::I32));
    sig
}

/// Declare a matcher fn in `module`. The caller is responsible for
/// pairing this with a single `emit_matcher_body` call before finalize.
pub(crate) fn declare_matcher<M: cranelift_module::Module>(
    module: &mut M,
    name: &str,
) -> Result<FuncId, CodegenError> {
    module
        .declare_function(name, Linkage::Local, &matcher_signature())
        .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))
}

/// Emit the body of a selective-receive matcher fn.
///
/// Walks each `clause` in source order. For clause `i`, branches into
/// a per-clause "try" block; on mismatch falls through to clause `i+1`;
/// on success returns `i+1` (1-based). Final fall-through returns 0.
///
/// `pinned` is the parent term's pinned list — its order is the matcher
/// ABI's `pinned[]` layout. Bound-var ordering is per-clause; the
/// winning clause writes to `out[0..clause.bound_names.len()]` in that
/// order, which matches the clause-body fn's parameter prefix.
pub(crate) fn emit_matcher_body<M: cranelift_module::Module>(
    module: &mut M,
    fbctx: &mut FunctionBuilderContext,
    matcher_id: FuncId,
    fz_module: &Module,
    tuple_schema_ids: &HashMap<usize, u32>,
    pinned: &[(String, crate::fz_ir::Var)],
    clauses: &[ReceiveClause],
) -> Result<(), CodegenError> {
    let pinned_indices: HashMap<&str, usize> = pinned
        .iter()
        .enumerate()
        .map(|(i, (name, _))| (name.as_str(), i))
        .collect();

    // fz-70q.2.2 — guard inlining lands in its own ticket. Until then,
    // any clause carrying a guard is rejected up front so the matcher
    // never silently accepts a partially-implemented clause.
    for (i, c) in clauses.iter().enumerate() {
        if c.guard.is_some() {
            return Err(CodegenError::new(format!(
                "matcher clause {} carries a guard; guard inlining lands in fz-70q.2.2",
                i
            )));
        }
    }

    let mut compile_err: Option<CodegenError> = None;
    emit_fn_body(module, fbctx, matcher_signature(), matcher_id, |_m, b| {
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let msg = b.block_params(entry)[0];
        let pinned_ptr = b.block_params(entry)[1];
        let out_ptr = b.block_params(entry)[2];

        // miss_block: shared fall-through used by every clause's
        // fail path AND by the final fallthrough from the last
        // clause. Returns 0 (the matcher-miss sentinel).
        let miss_block = b.create_block();

        // For each clause, create a fail block (== the next
        // clause's entry, or miss_block for the last clause).
        let mut fail_blocks: Vec<ir::Block> = Vec::with_capacity(clauses.len() + 1);
        for _ in 0..clauses.len() {
            fail_blocks.push(b.create_block());
        }
        // The last clause's "next" target is the miss block.
        fail_blocks.push(miss_block);

        // Each clause: switch to its entry, compile pattern with
        // fail_blocks[i+1] as the fail target, on success build a
        // return-i+1 instruction. Consecutive top-level tuple clauses
        // with the same arity share the tag/schema test before falling
        // through to per-clause field checks.
        let mut i = 0;
        while i < clauses.len() {
            if i == 0 {
                b.ins().jump(fail_blocks[0], &[]);
            }
            if let Some(arity) = top_tuple_arity(&clauses[i]) {
                let run_len = same_tuple_arity_run(clauses, i, arity);
                if run_len > 1 {
                    let try_block = fail_blocks[i];
                    let after_run = fail_blocks[i + run_len];
                    b.switch_to_block(try_block);
                    b.seal_block(try_block);
                    let run_body = b.create_block();
                    if let Err(e) = compile_tuple_shape(b, tuple_schema_ids, msg, arity, after_run)
                    {
                        compile_err = Some(e);
                        return;
                    }
                    b.ins().jump(run_body, &[]);
                    b.switch_to_block(run_body);
                    b.seal_block(run_body);

                    for j in i..(i + run_len) {
                        let fail_block = if j + 1 < i + run_len {
                            fail_blocks[j + 1]
                        } else {
                            after_run
                        };
                        if j > i {
                            let try_block = fail_blocks[j];
                            b.switch_to_block(try_block);
                            b.seal_block(try_block);
                        }
                        let c = &clauses[j];
                        let bound_indices: HashMap<&str, usize> = c
                            .bound_names
                            .iter()
                            .enumerate()
                            .map(|(idx, name)| (name.as_str(), idx))
                            .collect();

                        let ctx = PatternCtx {
                            fz_module,
                            tuple_schema_ids,
                            bound_indices: &bound_indices,
                            pinned_indices: &pinned_indices,
                            pinned_ptr,
                            out_ptr,
                        };
                        let Pattern::Tuple(elems) = &c.pattern.node else {
                            unreachable!("same_tuple_arity_run only includes tuple clauses")
                        };
                        if let Err(e) = compile_tuple_fields(b, &ctx, msg, elems, fail_block) {
                            compile_err = Some(e);
                            return;
                        }
                        let k = b.ins().iconst(types::I32, (j + 1) as i64);
                        b.ins().return_(&[k]);
                    }
                    i += run_len;
                    continue;
                }
            }

            let c = &clauses[i];
            let try_block = fail_blocks[i];
            let fail_block = fail_blocks[i + 1];
            b.switch_to_block(try_block);
            b.seal_block(try_block);

            let bound_indices: HashMap<&str, usize> = c
                .bound_names
                .iter()
                .enumerate()
                .map(|(idx, name)| (name.as_str(), idx))
                .collect();

            let ctx = PatternCtx {
                fz_module,
                tuple_schema_ids,
                bound_indices: &bound_indices,
                pinned_indices: &pinned_indices,
                pinned_ptr,
                out_ptr,
            };
            if let Err(e) = compile_pattern(b, &ctx, msg, &c.pattern.node, fail_block) {
                compile_err = Some(e);
                return;
            }
            // Pattern matched: return clause index + 1.
            let k = b.ins().iconst(types::I32, (i + 1) as i64);
            b.ins().return_(&[k]);
            i += 1;
        }

        // miss_block: every fail path lands here; return 0.
        b.switch_to_block(miss_block);
        b.seal_block(miss_block);
        let zero = b.ins().iconst(types::I32, 0);
        b.ins().return_(&[zero]);
    })
    .map_err(|e| CodegenError::new(format!("define matcher fn: {}", e)))?;
    if let Some(e) = compile_err {
        return Err(e);
    }
    Ok(())
}

/// fz-puj.20 (H9 / E2) — Decision-driven matcher body emitter.
///
/// Same ABI as `emit_matcher_body`, but the body is generated by walking
/// a `pattern_matrix::Decision` instead of cascading per-clause AST walks.
/// Switch nodes share constructor tests across all clauses with the same
/// top-level constructor (not just adjacent same-arity tuples like the
/// peephole). Pinned and Map/Bitstring patterns drop to PerRow, which
/// falls back to the existing per-row `compile_pattern` walker.
///
/// This emitter has no production caller yet — production wiring lands in
/// fz-puj.21 (AOT) and fz-puj.22 (interp). Tests exercise it end-to-end.
pub(crate) fn emit_matcher_body_from_decision<M: cranelift_module::Module>(
    module: &mut M,
    fbctx: &mut FunctionBuilderContext,
    matcher_id: FuncId,
    fz_module: &Module,
    tuple_schema_ids: &HashMap<usize, u32>,
    pinned: &[(String, Var)],
    clauses: &[ReceiveClause],
) -> Result<(), CodegenError> {
    // Guards aren't yet supported (fz-70q.2.2 / fz-puj.42). Reject up
    // front so we never silently accept a half-implemented clause.
    for (i, c) in clauses.iter().enumerate() {
        if c.guard.is_some() {
            return Err(CodegenError::new(format!(
                "matcher clause {} carries a guard; pure-guard support lands in fz-puj.42",
                i
            )));
        }
    }

    // Build N=1 Matrix; compile to Decision.
    let subject_var = Var(0);
    let matrix = Matrix {
        subjects: vec![subject_var],
        rows: clauses
            .iter()
            .enumerate()
            .map(|(i, c)| Row {
                patterns: vec![c.pattern.clone()],
                preconditions: Vec::new(),
                guard: None,
                body_id: i as BodyId,
            })
            .collect(),
    };
    let decision = compile_matrix(matrix);

    let pinned_indices: HashMap<String, usize> = pinned
        .iter()
        .enumerate()
        .map(|(i, (n, _))| (n.clone(), i))
        .collect();
    let bound_indices_per_clause: Vec<HashMap<String, usize>> = clauses
        .iter()
        .map(|c| {
            c.bound_names
                .iter()
                .enumerate()
                .map(|(i, n)| (n.clone(), i))
                .collect()
        })
        .collect();

    let mut compile_err: Option<CodegenError> = None;
    emit_fn_body(module, fbctx, matcher_signature(), matcher_id, |_m, b| {
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let msg = b.block_params(entry)[0];
        let pinned_ptr = b.block_params(entry)[1];
        let out_ptr = b.block_params(entry)[2];

        let miss_block = b.create_block();

        let mut root_values: HashMap<Var, ir::Value> = HashMap::new();
        root_values.insert(subject_var, msg);

        let ctx = DecisionCtx {
            fz_module,
            tuple_schema_ids,
            bound_indices_per_clause: &bound_indices_per_clause,
            pinned_indices: &pinned_indices,
            pinned_ptr,
            out_ptr,
            clauses,
            root_values: &root_values,
        };

        if let Err(e) = emit_decision(b, &ctx, &decision, miss_block) {
            compile_err = Some(e);
            return;
        }

        // Miss block — every Fail / fall-through lands here.
        b.switch_to_block(miss_block);
        b.seal_block(miss_block);
        let zero = b.ins().iconst(types::I32, 0);
        b.ins().return_(&[zero]);
    })
    .map_err(|e| CodegenError::new(format!("define matcher fn: {}", e)))?;

    if let Some(e) = compile_err {
        return Err(e);
    }
    Ok(())
}

struct DecisionCtx<'a> {
    fz_module: &'a Module,
    tuple_schema_ids: &'a HashMap<usize, u32>,
    /// per-clause body_id → bound_name → out_ptr slot index
    bound_indices_per_clause: &'a [HashMap<String, usize>],
    /// pinned name → pinned_ptr slot index (shared across clauses)
    pinned_indices: &'a HashMap<String, usize>,
    pinned_ptr: ir::Value,
    out_ptr: ir::Value,
    clauses: &'a [ReceiveClause],
    /// Root subject Var → ir::Value (i.e. Var(0) → `msg`). Subject refs
    /// for tuple fields project from the root recursively at use time.
    root_values: &'a HashMap<Var, ir::Value>,
}

/// Resolve a `SubjectRef` to a Cranelift value in the current block.
/// Always projects in the active block so dominance holds — no caching
/// across the Decision tree.
fn resolve_subject(
    b: &mut FunctionBuilder<'_>,
    ctx: &DecisionCtx,
    sref: &SubjectRef,
) -> Result<ir::Value, CodegenError> {
    match sref {
        SubjectRef::Var(v) => ctx
            .root_values
            .get(v)
            .copied()
            .ok_or_else(|| CodegenError::new(format!("unbound root subject Var({})", v.0))),
        SubjectRef::TupleField { tuple, index } => {
            let parent = resolve_subject(b, ctx, tuple)?;
            let off = HEADER_SIZE + (*index as i32) * SLOT_BYTES;
            Ok(b.ins().load(types::I64, MemFlags::trusted(), parent, off))
        }
        SubjectRef::ListHead(_) | SubjectRef::ListTail(_) => Err(CodegenError::new(
            "ListHead/ListTail subject not supported in receive matcher (fz-puj.40)",
        )),
    }
}

fn emit_decision(
    b: &mut FunctionBuilder<'_>,
    ctx: &DecisionCtx,
    d: &Decision,
    miss: ir::Block,
) -> Result<(), CodegenError> {
    match d {
        Decision::Fail => {
            b.ins().jump(miss, &[]);
            // Open a dead continuation so callers can keep emitting.
            let dead = b.create_block();
            b.switch_to_block(dead);
            b.seal_block(dead);
            Ok(())
        }
        Decision::Leaf {
            body_id, bindings, ..
        } => {
            // Write each bound value to out_ptr at the clause's slot index.
            let bound = &ctx.bound_indices_per_clause[*body_id as usize];
            for (name, sref) in bindings {
                let val = resolve_subject(b, ctx, sref)?;
                if let Some(&idx) = bound.get(name) {
                    b.ins().store(
                        MemFlags::trusted(),
                        val,
                        ctx.out_ptr,
                        (idx * SLOT_BYTES as usize) as i32,
                    );
                }
            }
            let k = b.ins().iconst(types::I32, (*body_id + 1) as i64);
            b.ins().return_(&[k]);
            // Dead continuation block so caller can keep emitting.
            let dead = b.create_block();
            b.switch_to_block(dead);
            b.seal_block(dead);
            Ok(())
        }
        Decision::Switch {
            subject,
            kind,
            cases,
            default,
        } => {
            let val = resolve_subject(b, ctx, subject)?;
            for (key, case_d) in cases {
                let match_b = b.create_block();
                let next_b = b.create_block();
                emit_switch_key_test(b, ctx, val, kind, key, match_b, next_b)?;
                b.switch_to_block(match_b);
                b.seal_block(match_b);
                emit_decision(b, ctx, case_d, miss)?;
                b.switch_to_block(next_b);
                b.seal_block(next_b);
            }
            emit_decision(b, ctx, default, miss)
        }
        Decision::PerRow {
            subjects,
            row,
            on_fail,
            ..
        } => {
            // Fall back to the AST-walking compile_pattern for every
            // column of the row. After tuple-arity specialization the
            // matrix may have several columns; each row.patterns[c] is
            // tested against subjects[c]. Any column miss → on_fail.
            let on_fail_block = b.create_block();
            let bound_indices: HashMap<&str, usize> = ctx.bound_indices_per_clause
                [row.body_id as usize]
                .iter()
                .map(|(n, &i)| (n.as_str(), i))
                .collect();
            let pinned_indices: HashMap<&str, usize> = ctx
                .pinned_indices
                .iter()
                .map(|(n, &i)| (n.as_str(), i))
                .collect();
            let pat_ctx = PatternCtx {
                fz_module: ctx.fz_module,
                tuple_schema_ids: ctx.tuple_schema_ids,
                bound_indices: &bound_indices,
                pinned_indices: &pinned_indices,
                pinned_ptr: ctx.pinned_ptr,
                out_ptr: ctx.out_ptr,
            };
            for (col_subject, col_pat) in subjects.iter().zip(&row.patterns) {
                let col_val = resolve_subject(b, ctx, col_subject)?;
                compile_pattern(b, &pat_ctx, col_val, &col_pat.node, on_fail_block)?;
            }
            // All columns matched: return clause index + 1.
            let k = b.ins().iconst(types::I32, (row.body_id + 1) as i64);
            b.ins().return_(&[k]);
            // on_fail path → next decision.
            b.switch_to_block(on_fail_block);
            b.seal_block(on_fail_block);
            emit_decision(b, ctx, on_fail, miss)
        }
    }
}

fn emit_switch_key_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &DecisionCtx,
    val: ir::Value,
    kind: &SwitchKind,
    key: &SwitchKey,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    match (kind, key) {
        (SwitchKind::Atom, SwitchKey::AtomName(name)) => {
            let Some(id) = ctx
                .fz_module
                .atom_names
                .iter()
                .position(|n| n == name)
                .map(|i| i as u32)
            else {
                // Unregistered atom — no fz value can match.
                b.ins().jump(next_b, &[]);
                return Ok(());
            };
            let tagged = ((id as u64) << 3) | (TAG_ATOM as u64);
            let want = b.ins().iconst(types::I64, tagged as i64);
            let cmp = b.ins().icmp(IntCC::Equal, val, want);
            b.ins().brif(cmp, match_b, &[], next_b, &[]);
            Ok(())
        }
        (SwitchKind::Int, SwitchKey::Int(n)) => {
            let tagged = ((*n as u64) << 3) | (TAG_INT as u64);
            let want = b.ins().iconst(types::I64, tagged as i64);
            let cmp = b.ins().icmp(IntCC::Equal, val, want);
            b.ins().brif(cmp, match_b, &[], next_b, &[]);
            Ok(())
        }
        (SwitchKind::Bool, SwitchKey::Bool(true)) => {
            let want = b.ins().iconst(types::I64, TRUE_BITS);
            let cmp = b.ins().icmp(IntCC::Equal, val, want);
            b.ins().brif(cmp, match_b, &[], next_b, &[]);
            Ok(())
        }
        (SwitchKind::Bool, SwitchKey::Bool(false)) => {
            let want = b
                .ins()
                .iconst(types::I64, fz_runtime::fz_value::FALSE_BITS as i64);
            let cmp = b.ins().icmp(IntCC::Equal, val, want);
            b.ins().brif(cmp, match_b, &[], next_b, &[]);
            Ok(())
        }
        (SwitchKind::Nil, SwitchKey::Nil) => {
            let want = b.ins().iconst(types::I64, NIL_BITS);
            let cmp = b.ins().icmp(IntCC::Equal, val, want);
            b.ins().brif(cmp, match_b, &[], next_b, &[]);
            Ok(())
        }
        (SwitchKind::TupleArity, SwitchKey::Arity(arity)) => {
            emit_tuple_arity_test(b, ctx, val, *arity as usize, match_b, next_b)
        }
        _ => Err(CodegenError::new(format!(
            "Decision Switch kind/key combination not yet supported in receive matcher: {:?} / {:?}",
            kind, key
        ))),
    }
}

/// Chain of equality / load checks that verifies `val` is a tuple of
/// the given arity. Branches to `match_b` on success, `next_b` on any
/// mismatch. Mirrors `compile_tuple_shape` but parameterised on match
/// vs miss target blocks.
fn emit_tuple_arity_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &DecisionCtx,
    val: ir::Value,
    arity: usize,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    let expected_schema_id = *ctx.tuple_schema_ids.get(&arity).ok_or_else(|| {
        CodegenError::new(format!(
            "matcher tuple arity {} not pre-registered (compile() walk missed it?)",
            arity
        ))
    })?;

    // tag == TAG_PTR
    let tag = b.ins().band_imm(val, TAG_MASK);
    let zero_tag = b.ins().iconst(types::I64, TAG_PTR);
    let c0 = b.create_block();
    let cmp0 = b.ins().icmp(IntCC::Equal, tag, zero_tag);
    b.ins().brif(cmp0, c0, &[], next_b, &[]);
    b.switch_to_block(c0);
    b.seal_block(c0);

    // val != EMPTY_LIST_BITS
    let empty = b.ins().iconst(types::I64, EMPTY_LIST_BITS);
    let c1 = b.create_block();
    let cmp1 = b.ins().icmp(IntCC::NotEqual, val, empty);
    b.ins().brif(cmp1, c1, &[], next_b, &[]);
    b.switch_to_block(c1);
    b.seal_block(c1);

    // val != 0
    let null = b.ins().iconst(types::I64, 0);
    let c2 = b.create_block();
    let cmp2 = b.ins().icmp(IntCC::NotEqual, val, null);
    b.ins().brif(cmp2, c2, &[], next_b, &[]);
    b.switch_to_block(c2);
    b.seal_block(c2);

    // kind == 0 (tuple)
    let kind = b.ins().load(types::I16, MemFlags::trusted(), val, 0);
    let kind_want = b.ins().iconst(types::I16, 0);
    let c3 = b.create_block();
    let cmp3 = b.ins().icmp(IntCC::Equal, kind, kind_want);
    b.ins().brif(cmp3, c3, &[], next_b, &[]);
    b.switch_to_block(c3);
    b.seal_block(c3);

    // schema == expected_schema_id
    let schema = b.ins().load(types::I32, MemFlags::trusted(), val, 8);
    let schema_want = b.ins().iconst(types::I32, expected_schema_id as i64);
    let cmp4 = b.ins().icmp(IntCC::Equal, schema, schema_want);
    b.ins().brif(cmp4, match_b, &[], next_b, &[]);
    Ok(())
}

/// Per-matcher state threaded through `compile_pattern`. Borrowed for
/// the duration of one clause compilation.
struct PatternCtx<'a> {
    fz_module: &'a Module,
    tuple_schema_ids: &'a HashMap<usize, u32>,
    /// Bound name → out_ptr slot index (per-clause).
    bound_indices: &'a HashMap<&'a str, usize>,
    /// Pinned name → pinned_ptr slot index (shared across clauses).
    pinned_indices: &'a HashMap<&'a str, usize>,
    pinned_ptr: ir::Value,
    out_ptr: ir::Value,
}

fn top_tuple_arity(c: &ReceiveClause) -> Option<usize> {
    match &c.pattern.node {
        Pattern::Tuple(elems) => Some(elems.len()),
        _ => None,
    }
}

fn same_tuple_arity_run(clauses: &[ReceiveClause], start: usize, arity: usize) -> usize {
    clauses[start..]
        .iter()
        .take_while(|c| top_tuple_arity(c) == Some(arity))
        .count()
}

/// Compile one pattern node into the active block. On mismatch, jumps
/// to `fail`; on match, falls through. Recurses for compound patterns.
fn compile_pattern(
    b: &mut FunctionBuilder<'_>,
    ctx: &PatternCtx<'_>,
    val: ir::Value,
    pat: &Pattern,
    fail: ir::Block,
) -> Result<(), CodegenError> {
    match pat {
        Pattern::Wildcard => Ok(()),
        Pattern::Var(name) => {
            write_bound(b, ctx, name, val)?;
            Ok(())
        }
        Pattern::As(name, inner) => {
            write_bound(b, ctx, name, val)?;
            compile_pattern(b, ctx, val, &inner.node, fail)
        }
        Pattern::Pinned(name) => {
            let &idx = ctx.pinned_indices.get(name.as_str()).ok_or_else(|| {
                CodegenError::new(format!("pinned ^{} not in matcher's pinned table", name))
            })?;
            let want = b.ins().load(
                types::I64,
                MemFlags::trusted(),
                ctx.pinned_ptr,
                (idx * SLOT_BYTES as usize) as i32,
            );
            brif_neq(b, val, want, fail);
            Ok(())
        }
        Pattern::Int(n) => {
            let tagged = ((*n as u64) << 3) | (TAG_INT as u64);
            let want = b.ins().iconst(types::I64, tagged as i64);
            brif_neq(b, val, want, fail);
            Ok(())
        }
        Pattern::Bool(true) => {
            let want = b.ins().iconst(types::I64, TRUE_BITS);
            brif_neq(b, val, want, fail);
            Ok(())
        }
        Pattern::Bool(false) => {
            // fz-yan.1 — `false` is the atom with reserved id 2.
            let want = b
                .ins()
                .iconst(types::I64, fz_runtime::fz_value::FALSE_BITS as i64);
            brif_neq(b, val, want, fail);
            Ok(())
        }
        Pattern::Nil => {
            let want = b.ins().iconst(types::I64, NIL_BITS);
            brif_neq(b, val, want, fail);
            Ok(())
        }
        Pattern::Atom(name) => {
            // Unregistered atom name → no fz value can ever match.
            // Emit unconditional branch to fail.
            let Some(id) = ctx
                .fz_module
                .atom_names
                .iter()
                .position(|n| n == name)
                .map(|i| i as u32)
            else {
                b.ins().jump(fail, &[]);
                // Open an unreachable continuation block so callers can
                // still emit subsequent code without verifier errors.
                let dead = b.create_block();
                b.switch_to_block(dead);
                b.seal_block(dead);
                return Ok(());
            };
            let tagged = ((id as u64) << 3) | (TAG_ATOM as u64);
            let want = b.ins().iconst(types::I64, tagged as i64);
            brif_neq(b, val, want, fail);
            Ok(())
        }
        Pattern::Tuple(elems) => {
            compile_tuple_shape(b, ctx.tuple_schema_ids, val, elems.len(), fail)?;
            compile_tuple_fields(b, ctx, val, elems, fail)
        }
        // List, Map, Bitstring, Float, Str: same as interp — matcher
        // always misses. Parity with src/ir_interp.rs::try_match_pattern.
        Pattern::List(_, _)
        | Pattern::Map(_)
        | Pattern::Bitstring(_)
        | Pattern::Float(_)
        | Pattern::Binary(_) => {
            b.ins().jump(fail, &[]);
            let dead = b.create_block();
            b.switch_to_block(dead);
            b.seal_block(dead);
            Ok(())
        }
    }
}

fn compile_tuple_shape(
    b: &mut FunctionBuilder<'_>,
    tuple_schema_ids: &HashMap<usize, u32>,
    val: ir::Value,
    arity: usize,
    fail: ir::Block,
) -> Result<(), CodegenError> {
    let expected_schema_id = *tuple_schema_ids.get(&arity).ok_or_else(|| {
        CodegenError::new(format!(
            "matcher tuple arity {} not pre-registered (compile() walk missed it?)",
            arity
        ))
    })?;

    let tag = b.ins().band_imm(val, TAG_MASK);
    let zero_tag = b.ins().iconst(types::I64, TAG_PTR);
    brif_neq(b, tag, zero_tag, fail);
    let empty = b.ins().iconst(types::I64, EMPTY_LIST_BITS);
    brif_eq(b, val, empty, fail);
    let null = b.ins().iconst(types::I64, 0);
    brif_eq(b, val, null, fail);
    let kind = b.ins().load(types::I16, MemFlags::trusted(), val, 0);
    let kind_want = b.ins().iconst(types::I16, 0);
    brif_neq_typed(b, kind, kind_want, fail, types::I16);
    let schema = b.ins().load(types::I32, MemFlags::trusted(), val, 8);
    let schema_want = b.ins().iconst(types::I32, expected_schema_id as i64);
    brif_neq_typed(b, schema, schema_want, fail, types::I32);
    Ok(())
}

fn compile_tuple_fields(
    b: &mut FunctionBuilder<'_>,
    ctx: &PatternCtx<'_>,
    val: ir::Value,
    elems: &[crate::ast::Spanned<Pattern>],
    fail: ir::Block,
) -> Result<(), CodegenError> {
    for (i, e) in elems.iter().enumerate() {
        let off = HEADER_SIZE + (i as i32) * SLOT_BYTES;
        let field = b.ins().load(types::I64, MemFlags::trusted(), val, off);
        compile_pattern(b, ctx, field, &e.node, fail)?;
    }
    Ok(())
}

fn write_bound(
    b: &mut FunctionBuilder<'_>,
    ctx: &PatternCtx<'_>,
    name: &str,
    val: ir::Value,
) -> Result<(), CodegenError> {
    let &idx = ctx.bound_indices.get(name).ok_or_else(|| {
        CodegenError::new(format!(
            "bound `{}` not in clause's bound_names table",
            name
        ))
    })?;
    b.ins().store(
        MemFlags::trusted(),
        val,
        ctx.out_ptr,
        (idx * SLOT_BYTES as usize) as i32,
    );
    Ok(())
}

/// Branch to `fail` if `lhs != rhs` (i64). Continues in a fresh
/// fall-through block so caller can keep emitting linearly.
fn brif_neq(b: &mut FunctionBuilder<'_>, lhs: ir::Value, rhs: ir::Value, fail: ir::Block) {
    let cmp = b.ins().icmp(IntCC::NotEqual, lhs, rhs);
    let cont = b.create_block();
    b.ins().brif(cmp, fail, &[], cont, &[]);
    b.switch_to_block(cont);
    b.seal_block(cont);
}

fn brif_eq(b: &mut FunctionBuilder<'_>, lhs: ir::Value, rhs: ir::Value, fail: ir::Block) {
    let cmp = b.ins().icmp(IntCC::Equal, lhs, rhs);
    let cont = b.create_block();
    b.ins().brif(cmp, fail, &[], cont, &[]);
    b.switch_to_block(cont);
    b.seal_block(cont);
}

fn brif_neq_typed(
    b: &mut FunctionBuilder<'_>,
    lhs: ir::Value,
    rhs: ir::Value,
    fail: ir::Block,
    _ty: ir::Type,
) {
    let cmp = b.ins().icmp(IntCC::NotEqual, lhs, rhs);
    let cont = b.create_block();
    b.ins().brif(cmp, fail, &[], cont, &[]);
    b.switch_to_block(cont);
    b.seal_block(cont);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Pattern as AstPattern, Spanned};
    use crate::diag::Span;
    use crate::fz_ir::{FnId, ReceiveClause, Var};
    use cranelift_codegen::settings::{self, Configurable};
    use cranelift_jit::{JITBuilder, JITModule};

    fn make_jit() -> (JITModule, FunctionBuilderContext) {
        let isa_builder = cranelift_native::builder().expect("native isa");
        let mut flag_builder = settings::builder();
        flag_builder.set("opt_level", "none").unwrap();
        flag_builder.set("is_pic", "false").unwrap();
        let isa = isa_builder
            .finish(settings::Flags::new(flag_builder))
            .expect("isa finish");
        let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        let jmod = JITModule::new(builder);
        (jmod, FunctionBuilderContext::new())
    }

    type MatcherAbi = extern "C" fn(u64, *const u64, *mut u64) -> u32;

    fn empty_module() -> Module {
        let mut m = Module::default();
        // Reserved atom IDs (fz-yan.1): nil=0, true=1, false=2.
        m.atom_names.push("nil".into());
        m.atom_names.push("true".into());
        m.atom_names.push("false".into());
        m
    }

    fn sp<T>(node: T) -> Spanned<T> {
        Spanned::dummy(node)
    }

    fn clause_with(pattern: AstPattern, bound_names: Vec<String>) -> ReceiveClause {
        ReceiveClause {
            pattern: sp(pattern),
            bound_names,
            guard: None,
            body: FnId(0),
            span: Span::DUMMY,
        }
    }

    fn finalize_and_get(mut jmod: JITModule, fid: FuncId) -> MatcherAbi {
        jmod.finalize_definitions().expect("finalize");
        let addr = jmod.get_finalized_function(fid);
        // Leak the JIT module so the code stays mapped for the test's
        // direct fn-pointer call. Tests run in their own process.
        Box::leak(Box::new(jmod));
        unsafe { std::mem::transmute(addr) }
    }

    /// Wildcard pattern: matcher returns 1 for any input.
    #[test]
    fn matcher_wildcard_matches_anything() {
        let (mut jmod, mut fbctx) = make_jit();
        let m = empty_module();
        let tuple_ids = HashMap::new();
        let pinned: Vec<(String, Var)> = Vec::new();
        let clauses = vec![clause_with(AstPattern::Wildcard, vec![])];
        let fid = declare_matcher(&mut jmod, "matcher_wildcard").unwrap();
        emit_matcher_body(
            &mut jmod, &mut fbctx, fid, &m, &tuple_ids, &pinned, &clauses,
        )
        .unwrap();
        let f = finalize_and_get(jmod, fid);
        let mut out = [0u64; 0];
        let pin: [u64; 0] = [];
        assert_eq!(f(0xdead_beef, pin.as_ptr(), out.as_mut_ptr()), 1);
        assert_eq!(f(0, pin.as_ptr(), out.as_mut_ptr()), 1);
    }

    /// `Pattern::Int(42)`: hit returns 1 only for tagged 42.
    #[test]
    fn matcher_int_literal_hits_only_exact_tagged_value() {
        let (mut jmod, mut fbctx) = make_jit();
        let m = empty_module();
        let tuple_ids = HashMap::new();
        let pinned: Vec<(String, Var)> = Vec::new();
        let clauses = vec![clause_with(AstPattern::Int(42), vec![])];
        let fid = declare_matcher(&mut jmod, "matcher_int_42").unwrap();
        emit_matcher_body(
            &mut jmod, &mut fbctx, fid, &m, &tuple_ids, &pinned, &clauses,
        )
        .unwrap();
        let f = finalize_and_get(jmod, fid);
        let pin: [u64; 0] = [];
        let mut out = [0u64; 0];
        let tagged_42: u64 = (42u64 << 3) | (TAG_INT as u64);
        let tagged_41: u64 = (41u64 << 3) | (TAG_INT as u64);
        assert_eq!(f(tagged_42, pin.as_ptr(), out.as_mut_ptr()), 1);
        assert_eq!(f(tagged_41, pin.as_ptr(), out.as_mut_ptr()), 0);
        assert_eq!(f(0, pin.as_ptr(), out.as_mut_ptr()), 0);
    }

    /// `Pattern::Var(name)`: any input matches, value written to out[0].
    #[test]
    fn matcher_var_pattern_writes_input_to_out_slot_zero() {
        let (mut jmod, mut fbctx) = make_jit();
        let m = empty_module();
        let tuple_ids = HashMap::new();
        let pinned: Vec<(String, Var)> = Vec::new();
        let clauses = vec![clause_with(AstPattern::Var("x".into()), vec!["x".into()])];
        let fid = declare_matcher(&mut jmod, "matcher_var_x").unwrap();
        emit_matcher_body(
            &mut jmod, &mut fbctx, fid, &m, &tuple_ids, &pinned, &clauses,
        )
        .unwrap();
        let f = finalize_and_get(jmod, fid);
        let pin: [u64; 0] = [];
        let mut out = [0u64; 1];
        let v: u64 = 0xc0ffee;
        assert_eq!(f(v, pin.as_ptr(), out.as_mut_ptr()), 1);
        assert_eq!(out[0], v);
    }

    /// Pinned: matches only when the input matches `pinned[0]`.
    #[test]
    fn matcher_pinned_pattern_compares_against_pinned_slot() {
        let (mut jmod, mut fbctx) = make_jit();
        let m = empty_module();
        let tuple_ids = HashMap::new();
        let pinned = vec![("p".to_string(), Var(0))];
        let clauses = vec![clause_with(AstPattern::Pinned("p".into()), vec![])];
        let fid = declare_matcher(&mut jmod, "matcher_pinned_p").unwrap();
        emit_matcher_body(
            &mut jmod, &mut fbctx, fid, &m, &tuple_ids, &pinned, &clauses,
        )
        .unwrap();
        let f = finalize_and_get(jmod, fid);
        let mut out = [0u64; 0];
        let pin = [0x1234_5678u64];
        assert_eq!(f(0x1234_5678, pin.as_ptr(), out.as_mut_ptr()), 1);
        assert_eq!(f(0x1234_0000, pin.as_ptr(), out.as_mut_ptr()), 0);
    }

    /// Atom: registered atom hits when bits match; unregistered name
    /// emits an always-fail arm (no fz value can match).
    #[test]
    fn matcher_atom_pattern_uses_registered_atom_id() {
        let (mut jmod, mut fbctx) = make_jit();
        let mut m = empty_module();
        m.atom_names.push("k_a".into()); // id 3
        let tuple_ids = HashMap::new();
        let pinned: Vec<(String, Var)> = Vec::new();
        let clauses = vec![clause_with(AstPattern::Atom("k_a".into()), vec![])];
        let fid = declare_matcher(&mut jmod, "matcher_atom_k_a").unwrap();
        emit_matcher_body(
            &mut jmod, &mut fbctx, fid, &m, &tuple_ids, &pinned, &clauses,
        )
        .unwrap();
        let f = finalize_and_get(jmod, fid);
        let pin: [u64; 0] = [];
        let mut out = [0u64; 0];
        let tagged_k_a: u64 = (3u64 << 3) | (TAG_ATOM as u64);
        let tagged_other: u64 = (99u64 << 3) | (TAG_ATOM as u64);
        assert_eq!(f(tagged_k_a, pin.as_ptr(), out.as_mut_ptr()), 1);
        assert_eq!(f(tagged_other, pin.as_ptr(), out.as_mut_ptr()), 0);
    }

    /// Multi-clause: first-matching wins; later clauses don't run.
    #[test]
    fn matcher_first_matching_clause_wins() {
        let (mut jmod, mut fbctx) = make_jit();
        let m = empty_module();
        let tuple_ids = HashMap::new();
        let pinned: Vec<(String, Var)> = Vec::new();
        let clauses = vec![
            clause_with(AstPattern::Int(1), vec![]),
            clause_with(AstPattern::Int(2), vec![]),
            clause_with(AstPattern::Wildcard, vec![]),
        ];
        let fid = declare_matcher(&mut jmod, "matcher_multi").unwrap();
        emit_matcher_body(
            &mut jmod, &mut fbctx, fid, &m, &tuple_ids, &pinned, &clauses,
        )
        .unwrap();
        let f = finalize_and_get(jmod, fid);
        let pin: [u64; 0] = [];
        let mut out = [0u64; 0];
        let t1: u64 = (1u64 << 3) | (TAG_INT as u64);
        let t2: u64 = (2u64 << 3) | (TAG_INT as u64);
        let t99: u64 = (99u64 << 3) | (TAG_INT as u64);
        assert_eq!(f(t1, pin.as_ptr(), out.as_mut_ptr()), 1);
        assert_eq!(f(t2, pin.as_ptr(), out.as_mut_ptr()), 2);
        assert_eq!(f(t99, pin.as_ptr(), out.as_mut_ptr()), 3);
    }

    /// Tuple `{:reply, ^ref, v}`: schema check + atom + pinned + var
    /// — the shape that the fz-recv fixture's clause exercises.
    #[test]
    fn matcher_tuple_with_atom_pinned_var_matches_arrived_message() {
        use fz_runtime::fz_value::{HeapHeader, HeapKind};

        let (mut jmod, mut fbctx) = make_jit();
        let mut m = empty_module();
        m.atom_names.push("reply".into()); // id 3

        let mut tuple_ids = HashMap::new();
        tuple_ids.insert(3, 7u32); // arity 3 → schema id 7 (test-local)

        let pinned = vec![("ref".to_string(), Var(0))];
        let pat = AstPattern::Tuple(vec![
            sp(AstPattern::Atom("reply".into())),
            sp(AstPattern::Pinned("ref".into())),
            sp(AstPattern::Var("v".into())),
        ]);
        let clauses = vec![clause_with(pat, vec!["v".into()])];
        let fid = declare_matcher(&mut jmod, "matcher_tuple_reply").unwrap();
        emit_matcher_body(
            &mut jmod, &mut fbctx, fid, &m, &tuple_ids, &pinned, &clauses,
        )
        .unwrap();
        let f = finalize_and_get(jmod, fid);

        // Build a heap-shaped tuple: HeapHeader (16 bytes) + 3 FzValue slots.
        // 5 u64 slots = 40 bytes, 16-byte aligned via Box<[u64; 8]>.
        let mut buf: Box<[u64; 8]> = Box::new([0u64; 8]);
        let base = buf.as_mut_ptr() as *mut u8;
        // SAFETY: buf is owned for the duration of the test; we hand
        // the JIT'd matcher a pointer that's valid for read-only access.
        unsafe {
            let header = HeapHeader {
                kind: HeapKind::Struct as u16,
                flags: 0,
                size_bytes: 16 + 24,
                schema_id: 7,
                _reserved: 0,
            };
            std::ptr::write(base as *mut HeapHeader, header);
            // Fields: :reply atom (id 3), pinned value 0xaa, payload 0xbb.
            let reply_bits: u64 = (3u64 << 3) | (TAG_ATOM as u64);
            let pin_bits: u64 = 0xaa;
            let payload_bits: u64 = 0xbb;
            std::ptr::write(base.add(16) as *mut u64, reply_bits);
            std::ptr::write(base.add(24) as *mut u64, pin_bits);
            std::ptr::write(base.add(32) as *mut u64, payload_bits);
        }

        let pin = [0xaau64];
        let mut out = [0u64; 1];
        let val = base as u64; // TAG_PTR = 0; pointer is 16-byte aligned.
        assert_eq!(f(val, pin.as_ptr(), out.as_mut_ptr()), 1);
        assert_eq!(out[0], 0xbb);

        // Pinned mismatch: same tuple but pinned[0] != msg.field[1].
        let pin_other = [0xffu64];
        let mut out2 = [0u64; 1];
        assert_eq!(f(val, pin_other.as_ptr(), out2.as_mut_ptr()), 0);
    }

    /// Guards aren't supported in this ticket; explicit error keeps the
    /// boundary visible (no silent acceptance).
    #[test]
    fn matcher_rejects_clauses_with_guards() {
        let (mut jmod, mut fbctx) = make_jit();
        let m = empty_module();
        let tuple_ids = HashMap::new();
        let pinned: Vec<(String, Var)> = Vec::new();
        let mut c = clause_with(AstPattern::Wildcard, vec![]);
        c.guard = Some(FnId(99));
        let clauses = vec![c];
        let fid = declare_matcher(&mut jmod, "matcher_with_guard").unwrap();
        let err = emit_matcher_body(
            &mut jmod, &mut fbctx, fid, &m, &tuple_ids, &pinned, &clauses,
        )
        .unwrap_err();
        assert!(
            err.to_string()
                .contains("guard inlining lands in fz-70q.2.2"),
            "error message points at the guard ticket: {}",
            err
        );
    }

    // -----------------------------------------------------------------
    // fz-puj.20 (H9 / E2) — Decision-driven matcher emitter tests.
    //
    // Behavioral parity with `emit_matcher_body` for the H9 subset:
    // wildcard / var / as / pinned / atom / int / bool / nil / tuple.
    // -----------------------------------------------------------------

    fn build_decision_matcher(
        jmod: &mut JITModule,
        fbctx: &mut FunctionBuilderContext,
        fz_module: &Module,
        tuple_schemas: &HashMap<usize, u32>,
        pinned: &[(String, Var)],
        clauses: &[ReceiveClause],
        name: &str,
    ) -> MatcherAbi {
        let fid = declare_matcher(jmod, name).expect("declare matcher");
        emit_matcher_body_from_decision(
            jmod,
            fbctx,
            fid,
            fz_module,
            tuple_schemas,
            pinned,
            clauses,
        )
        .expect("emit decision matcher");
        finalize_and_get(std::mem::replace(jmod, make_jit().0), fid)
    }

    #[test]
    fn decision_matcher_wildcard_matches_anything() {
        let (mut jmod, mut fbctx) = make_jit();
        let m = empty_module();
        let tuple_ids = HashMap::new();
        let pinned: Vec<(String, Var)> = Vec::new();
        let clauses = vec![clause_with(AstPattern::Wildcard, vec![])];
        let f = build_decision_matcher(
            &mut jmod,
            &mut fbctx,
            &m,
            &tuple_ids,
            &pinned,
            &clauses,
            "dm_wildcard",
        );
        let pin: [u64; 0] = [];
        let mut out = [0u64; 0];
        assert_eq!(f(0xdead_beef, pin.as_ptr(), out.as_mut_ptr()), 1);
        assert_eq!(f(0, pin.as_ptr(), out.as_mut_ptr()), 1);
    }

    #[test]
    fn decision_matcher_int_literal_hits_only_exact_tagged_value() {
        let (mut jmod, mut fbctx) = make_jit();
        let m = empty_module();
        let tuple_ids = HashMap::new();
        let pinned: Vec<(String, Var)> = Vec::new();
        let clauses = vec![clause_with(AstPattern::Int(42), vec![])];
        let f = build_decision_matcher(
            &mut jmod, &mut fbctx, &m, &tuple_ids, &pinned, &clauses, "dm_int42",
        );
        let pin: [u64; 0] = [];
        let mut out = [0u64; 0];
        let tagged_42 = ((42u64) << 3) | (TAG_INT as u64);
        let tagged_41 = ((41u64) << 3) | (TAG_INT as u64);
        assert_eq!(f(tagged_42, pin.as_ptr(), out.as_mut_ptr()), 1);
        assert_eq!(f(tagged_41, pin.as_ptr(), out.as_mut_ptr()), 0);
    }

    #[test]
    fn decision_matcher_var_writes_input_to_out_slot_zero() {
        let (mut jmod, mut fbctx) = make_jit();
        let m = empty_module();
        let tuple_ids = HashMap::new();
        let pinned: Vec<(String, Var)> = Vec::new();
        let clauses = vec![clause_with(AstPattern::Var("x".into()), vec!["x".into()])];
        let f = build_decision_matcher(
            &mut jmod, &mut fbctx, &m, &tuple_ids, &pinned, &clauses, "dm_var",
        );
        let pin: [u64; 0] = [];
        let mut out = [0u64; 1];
        let msg = ((7u64) << 3) | (TAG_INT as u64);
        assert_eq!(f(msg, pin.as_ptr(), out.as_mut_ptr()), 1);
        assert_eq!(out[0], msg);
    }

    #[test]
    fn decision_matcher_pinned_pattern_compares_against_pinned_slot() {
        let (mut jmod, mut fbctx) = make_jit();
        let m = empty_module();
        let tuple_ids = HashMap::new();
        let pinned = vec![("p".to_string(), Var(0))];
        let clauses = vec![clause_with(AstPattern::Pinned("p".into()), vec![])];
        let f = build_decision_matcher(
            &mut jmod,
            &mut fbctx,
            &m,
            &tuple_ids,
            &pinned,
            &clauses,
            "dm_pinned",
        );
        let want = ((9u64) << 3) | (TAG_INT as u64);
        let pin = [want];
        let mut out = [0u64; 0];
        assert_eq!(f(want, pin.as_ptr(), out.as_mut_ptr()), 1);
        let other = ((10u64) << 3) | (TAG_INT as u64);
        assert_eq!(f(other, pin.as_ptr(), out.as_mut_ptr()), 0);
    }

    #[test]
    fn decision_matcher_atom_pattern_uses_registered_atom_id() {
        let (mut jmod, mut fbctx) = make_jit();
        let mut m = empty_module();
        m.atom_names.push("ping".into()); // id 3
        let tuple_ids = HashMap::new();
        let pinned: Vec<(String, Var)> = Vec::new();
        let clauses = vec![clause_with(AstPattern::Atom("ping".into()), vec![])];
        let f = build_decision_matcher(
            &mut jmod, &mut fbctx, &m, &tuple_ids, &pinned, &clauses, "dm_atom",
        );
        let pin: [u64; 0] = [];
        let mut out = [0u64; 0];
        let ping_bits = ((3u64) << 3) | (TAG_ATOM as u64);
        assert_eq!(f(ping_bits, pin.as_ptr(), out.as_mut_ptr()), 1);
        let other_bits = ((99u64) << 3) | (TAG_ATOM as u64);
        assert_eq!(f(other_bits, pin.as_ptr(), out.as_mut_ptr()), 0);
    }

    #[test]
    fn decision_matcher_first_matching_clause_wins() {
        let (mut jmod, mut fbctx) = make_jit();
        let mut m = empty_module();
        m.atom_names.push("a".into()); // id 3
        m.atom_names.push("b".into()); // id 4
        let tuple_ids = HashMap::new();
        let pinned: Vec<(String, Var)> = Vec::new();
        let clauses = vec![
            clause_with(AstPattern::Atom("a".into()), vec![]),
            clause_with(AstPattern::Atom("b".into()), vec![]),
            clause_with(AstPattern::Wildcard, vec![]),
        ];
        let f = build_decision_matcher(
            &mut jmod,
            &mut fbctx,
            &m,
            &tuple_ids,
            &pinned,
            &clauses,
            "dm_first_match",
        );
        let pin: [u64; 0] = [];
        let mut out = [0u64; 0];
        let a_bits = ((3u64) << 3) | (TAG_ATOM as u64);
        let b_bits = ((4u64) << 3) | (TAG_ATOM as u64);
        let other = ((5u64) << 3) | (TAG_ATOM as u64);
        assert_eq!(f(a_bits, pin.as_ptr(), out.as_mut_ptr()), 1);
        assert_eq!(f(b_bits, pin.as_ptr(), out.as_mut_ptr()), 2);
        assert_eq!(f(other, pin.as_ptr(), out.as_mut_ptr()), 3);
    }

    #[test]
    fn decision_matcher_rejects_clauses_with_guards() {
        let (mut jmod, mut fbctx) = make_jit();
        let m = empty_module();
        let tuple_ids = HashMap::new();
        let pinned: Vec<(String, Var)> = Vec::new();
        let mut c = clause_with(AstPattern::Wildcard, vec![]);
        c.guard = Some(FnId(99));
        let clauses = vec![c];
        let fid = declare_matcher(&mut jmod, "dm_guarded").unwrap();
        let err = emit_matcher_body_from_decision(
            &mut jmod, &mut fbctx, fid, &m, &tuple_ids, &pinned, &clauses,
        )
        .unwrap_err();
        assert!(
            err.to_string().contains("fz-puj.42"),
            "error message points at pure-guard ticket: {}",
            err
        );
    }
}
