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
use crate::fz_ir::{Module, ReceiveClause};
use crate::ir_codegen::{
    CodegenError, EMPTY_LIST_BITS, HEADER_SIZE, NIL_BITS, SLOT_BYTES, TAG_ATOM, TAG_INT, TAG_MASK,
    TAG_PTR, TRUE_BITS, emit_fn_body,
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
        // return-i+1 instruction.
        for (i, c) in clauses.iter().enumerate() {
            if i == 0 {
                b.ins().jump(fail_blocks[0], &[]);
            }
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
            let arity = elems.len();
            let expected_schema_id = *ctx.tuple_schema_ids.get(&arity).ok_or_else(|| {
                CodegenError::new(format!(
                    "matcher tuple arity {} not pre-registered (compile() walk missed it?)",
                    arity
                ))
            })?;

            // 1. Tag check: low 3 bits == TAG_PTR (0).
            let tag = b.ins().band_imm(val, TAG_MASK);
            let zero_tag = b.ins().iconst(types::I64, TAG_PTR);
            brif_neq(b, tag, zero_tag, fail);
            // 2. Reject empty-list sentinel (`[]` is TAG_PTR but not a tuple)
            //    and the null pointer (defensive — heap allocator never
            //    returns 0 but bit-compare keeps the matcher leaf-pure).
            let empty = b.ins().iconst(types::I64, EMPTY_LIST_BITS);
            brif_eq(b, val, empty, fail);
            let null = b.ins().iconst(types::I64, 0);
            brif_eq(b, val, null, fail);
            // 3. HeapHeader.kind (u16 at +0) == HeapKind::Struct (0).
            //    Load as i16 and compare against 0.
            let kind = b.ins().load(types::I16, MemFlags::trusted(), val, 0);
            let kind_want = b.ins().iconst(types::I16, 0);
            brif_neq_typed(b, kind, kind_want, fail, types::I16);
            // 4. HeapHeader.schema_id (u32 at +8) == expected.
            let schema = b.ins().load(types::I32, MemFlags::trusted(), val, 8);
            let schema_want = b.ins().iconst(types::I32, expected_schema_id as i64);
            brif_neq_typed(b, schema, schema_want, fail, types::I32);
            // 5. Recurse into each field at +HEADER_SIZE + i*SLOT_BYTES.
            for (i, e) in elems.iter().enumerate() {
                let off = HEADER_SIZE + (i as i32) * SLOT_BYTES;
                let field = b.ins().load(types::I64, MemFlags::trusted(), val, off);
                compile_pattern(b, ctx, field, &e.node, fail)?;
            }
            Ok(())
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
}
