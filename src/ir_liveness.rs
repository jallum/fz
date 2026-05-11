//! fz-IR liveness analysis -> per-fn frame schemas.
//!
//! In CPS form (after .11.16/.11.17 lowering), every non-tail call has been
//! split out so that any value computed *before* the call but needed *after*
//! is threaded through the continuation's `captured` list. So the captured
//! lists already encode "live across this call". Liveness here just unions
//! those across all of a fn's outgoing call sites and emits a Frame schema:
//!
//!     [continuation_ptr, live_var_0, live_var_1, ...]   (each FzValue, 8 bytes)
//!
//! Vars used only between adjacent stmts within a block need no frame slot —
//! Cranelift will register-allocate them. Tail-call-only fns (no Term::Call
//! or Term::CallClosure terminators) get a frame schema with just the
//! continuation pointer.

#![allow(dead_code)]

use crate::fz_ir::{FnIr, Module, Term, Var};
use crate::heap::{FieldDescriptor, FieldKind, Schema};
use std::collections::HashSet;

/// Compute and assign a frame schema for every fn in `module`. Each fn's
/// `frame_schema_id` is updated to point into `module.schemas`.
pub fn analyze_module(module: &mut Module) {
    let n = module.fns.len();
    for i in 0..n {
        let live = collect_live_across_calls(&module.fns[i]);
        let schema = build_schema(&module.fns[i].name, &live);
        let id = module.schemas.len() as u32;
        module.schemas.push(schema);
        module.fns[i].frame_schema_id = id;
    }
}

/// Vars carried via any `Call`/`CallClosure` continuation in this fn, in
/// first-encountered order, deduplicated.
pub fn collect_live_across_calls(f: &FnIr) -> Vec<Var> {
    let mut seen: HashSet<Var> = HashSet::new();
    let mut out: Vec<Var> = Vec::new();
    for blk in &f.blocks {
        match &blk.terminator {
            Term::Call { continuation, .. } | Term::CallClosure { continuation, .. } => {
                for v in &continuation.captured {
                    if seen.insert(*v) {
                        out.push(*v);
                    }
                }
            }
            _ => {}
        }
    }
    out
}

fn build_schema(name: &str, live: &[Var]) -> Schema {
    // Slot 0: continuation pointer. Slots 1..N: each live FzValue.
    let n_fields = 1 + live.len();
    let mut fields = Vec::with_capacity(n_fields);
    for i in 0..n_fields {
        fields.push(FieldDescriptor {
            offset: (i * 8) as u32,
            kind: FieldKind::FzValue,
        });
    }
    Schema {
        name: format!("Frame_{}", name),
        size: (n_fields * 8) as u32,
        fields,
    }
}

/// Byte offset of `v` within `f`'s frame (after liveness has been assigned),
/// or `None` if `v` is not a frame slot. Continuation pointer lives at
/// offset 0; live FzValue slots start at offset 8.
pub fn frame_offset_of_var(f: &FnIr, v: Var) -> Option<u32> {
    let live = collect_live_across_calls(f);
    let idx = live.iter().position(|x| *x == v)?;
    Some(((idx + 1) * 8) as u32)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir_lower::lower_program;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    fn lower_and_analyze(src: &str) -> Module {
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let mut m = lower_program(&prog).expect("lower");
        analyze_module(&mut m);
        m
    }

    #[test]
    fn simple_fn_has_only_continuation_slot() {
        let m = lower_and_analyze("fn f(x), do: x");
        let f_ir = m.fn_by_name("f").unwrap();
        let s = &m.schemas[f_ir.frame_schema_id as usize];
        assert_eq!(s.fields.len(), 1, "expected only cont ptr slot");
        assert_eq!(s.size, 8);
        assert_eq!(s.fields[0].offset, 0);
    }

    #[test]
    fn tail_call_only_fn_has_no_frame_growth() {
        let m = lower_and_analyze(r#"
fn caller(x), do: callee(x)
fn callee(y), do: y
"#);
        let caller_ir = m.fn_by_name("caller").unwrap();
        let s = &m.schemas[caller_ir.frame_schema_id as usize];
        assert_eq!(s.fields.len(), 1, "tail-only caller frame should be cont ptr only");
    }

    #[test]
    fn non_tail_call_records_live_var_in_frame() {
        let m = lower_and_analyze(r#"
fn caller(x), do: callee(x) + 1
fn callee(y), do: y
"#);
        let caller_ir = m.fn_by_name("caller").unwrap();
        let s = &m.schemas[caller_ir.frame_schema_id as usize];
        assert!(s.fields.len() >= 2, "expected captured var in caller frame, got {} fields", s.fields.len());
        assert_eq!(s.size as usize, s.fields.len() * 8);
        for (i, fd) in s.fields.iter().enumerate() {
            assert_eq!(fd.offset, (i * 8) as u32);
            assert_eq!(fd.kind, FieldKind::FzValue);
        }
    }

    #[test]
    fn recursive_fn_records_live_locals_in_frame() {
        let m = lower_and_analyze(r#"
fn fact(0), do: 1
fn fact(n), do: n * fact(n - 1)
"#);
        let f_ir = m.fn_by_name("fact").unwrap();
        let s = &m.schemas[f_ir.frame_schema_id as usize];
        assert!(s.fields.len() >= 2, "fact frame should hold n across the recursive call");
    }

    #[test]
    fn every_fn_in_module_gets_a_schema() {
        let m = lower_and_analyze("fn f(x), do: x\nfn g(), do: 1");
        for fn_ir in &m.fns {
            assert!((fn_ir.frame_schema_id as usize) < m.schemas.len());
        }
        assert_eq!(m.schemas.len(), m.fns.len());
    }

    #[test]
    fn frame_offset_of_var_returns_slot_offset() {
        let m = lower_and_analyze(r#"
fn caller(x), do: callee(x) + 1
fn callee(y), do: y
"#);
        let caller_ir = m.fn_by_name("caller").unwrap();
        let live = collect_live_across_calls(caller_ir);
        assert!(!live.is_empty());
        let off = frame_offset_of_var(caller_ir, live[0]).unwrap();
        assert_eq!(off, 8);
    }
}
