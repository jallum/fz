//! Split from src/ir_codegen.rs (fz-ame.7). Mechanical move only.

#![allow(unused_imports)]

use super::*;
use crate::fz_ir::{BinOp, Const, FnId, Module, Prim, Stmt, Term, UnOp};
use cranelift_codegen::Context;
use cranelift_codegen::ir::{
    self, AbiParam, BlockArg, InstBuilder, MemFlags, Signature,
    condcodes::{FloatCC, IntCC},
    types,
};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module as ClModule};
use fz_runtime::heap::{FieldDescriptor, FieldKind, Schema};
use std::collections::HashMap;
use std::sync::Arc;

pub(crate) fn cranelift_body_stats(func: &ir::Function) -> (usize, usize) {
    let block_count = func.layout.blocks().count();
    let instruction_count = func
        .layout
        .blocks()
        .map(|block| func.layout.block_insts(block).count())
        .sum();
    (block_count, instruction_count)
}

/// fz-ul4.32.1 — Build the per-fn header block that precedes annotated
/// CLIF. Two lines: planner's param/return types and codegen's ArgReprs.
/// Disagreement between the two reveals where seam coercion lands.
pub(crate) fn build_planner_header<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::RenderTypes,
>(
    t: &mut T,
    f: &crate::fz_ir::FnIr,
    ft: &crate::ir_planner::SpecPlan,
    spec_key: &[crate::types::Ty],
    demand: &crate::ir_planner::fn_types::ReturnDemand,
    effective_return: &crate::types::Ty,
    param_reprs: &[ArgRepr],
    return_repr: ArgRepr,
) -> String {
    use std::fmt::Write as _;
    let entry_params = &f.block(f.entry).params;
    let planner_params: Vec<String> = entry_params
        .iter()
        .map(|v| {
            ft.vars
                .get(v)
                .map_or_else(|| "?".to_string(), |d| t.display(d))
        })
        .collect();
    // fz-i82.2 — `@spec` reports the same effective return that drives
    // `@abi` and the cont's slot-0 keying (`module_types.effective_returns`).
    // Halt-only specs converge to `none` in the LFP; show `_` for those
    // (matches the previous "no Term::Return found" rendering).
    let none = t.none();
    let return_str = if t.is_subtype(effective_return, &none) {
        "_".to_string()
    } else {
        t.display(effective_return)
    };
    let codegen_repr = |r: &ArgRepr| -> &'static str {
        match r {
            ArgRepr::ValueRef => "ValueRef",
            ArgRepr::RawInt => "RawInt",
            ArgRepr::RawF64 => "RawF64",
            ArgRepr::Condition => "Condition",
        }
    };
    let codegen_params: Vec<String> = param_reprs
        .iter()
        .map(|r| codegen_repr(r).to_string())
        .collect();
    let key_params: Vec<String> = spec_key.iter().map(|key| t.display(key)).collect();
    let mut out = String::new();
    let _ = writeln!(
        out,
        ";   @spec   {}({}) -> {}",
        f.name,
        planner_params.join(", "),
        return_str
    );
    let _ = writeln!(out, ";   @key    [{}]", key_params.join(", "));
    let _ = writeln!(
        out,
        ";   @demand {}",
        crate::ir_planner::fn_types::display_return_demand(&*t, demand)
    );
    let _ = writeln!(
        out,
        ";   @abi    ({}) -> {}",
        codegen_params.join(", "),
        codegen_repr(&return_repr)
    );
    out
}

/// fz-ul4.32.1 — Annotate raw Cranelift IR text with IR-level types.
///
/// Inputs:
///   - `raw`: the text from `ctx.func.display()`.
///   - `value_tys`: Value.as_u32() → planner Ty for fz-Var-bound values.
///   - `header`: pre-built header lines (planner params/return, codegen
///     param_reprs/return_repr). Already starts with `; `.
///
/// Output: header lines + annotated CLIF. Per-`vN = ...` definitions get
/// an inline `; vN :: <ty>` comment appended; pure intermediates with
/// no fz Var binding are left alone. The `block0(...)` line annotates
/// each block-param with its type inline.
pub(crate) fn annotate_clif_dump(
    raw: &str,
    value_tys: &HashMap<u32, crate::types::Ty>,
    func_names: &HashMap<u32, String>,
    header: &str,
) -> String {
    use std::fmt::Write as _;
    let mut out = String::new();
    out.push_str(header);
    if !header.ends_with('\n') {
        out.push('\n');
    }
    for line in raw.lines() {
        let resolved = resolve_user_func_refs(line, func_names);
        let trimmed = resolved.trim_start();
        // Block header: `blockN(v0: ty, v1: ty, ...):`
        if trimmed.starts_with("block") && trimmed.contains('(') && trimmed.ends_with(':') {
            let _ = writeln!(out, "{}", annotate_block_header(&resolved, value_tys));
            continue;
        }
        // Value definition: `    vN = <op> ...`
        if let Some(rest) = trimmed.strip_prefix('v')
            && let Some((id_str, _)) = rest.split_once(' ')
            && let Ok(id) = id_str.parse::<u32>()
            // Confirm it's actually `vN =` (not `vN+16` in a load).
            && rest.split_once(' ').map(|x| x.1.starts_with('=')).unwrap_or(false)
            && let Some(ty) = value_tys.get(&id)
        {
            let _ = writeln!(
                out,
                "{}    ;; v{} :: {}",
                resolved.trim_end(),
                id,
                crate::concrete_types::ty_display(ty)
            );
            continue;
        }
        let _ = writeln!(out, "{}", resolved);
    }
    out
}

// fz-323 — snapshot every declared function's linkage name keyed by FuncId.
// Used by the CLIF dumper to swap `u0:N` numeric refs for `@<name>` symbolic
// refs that are stable across additions of unrelated runtime helpers.
pub(crate) fn snapshot_func_names(
    decls: &cranelift_module::ModuleDeclarations,
) -> HashMap<u32, String> {
    decls
        .get_functions()
        .map(|(id, d)| (id.as_u32(), d.linkage_name(id).into_owned()))
        .collect()
}

// fz-323 — rewrite Cranelift's `u0:N` external-name tokens to `@<linkage_name>`.
// The number N is a `cranelift_module::FuncId` assigned in module-declaration
// order, so adding any new helper upstream shifts every later N and creates
// trivial churn in CLIF dumps. The linkage name was passed to
// `declare_function` and is source-derived (`fz_fn_17`, `fz_resume`, …), so
// it survives unrelated growth in the module.
pub(crate) fn resolve_user_func_refs(line: &str, func_names: &HashMap<u32, String>) -> String {
    if !line.contains("u0:") {
        return line.to_string();
    }
    let bytes = line.as_bytes();
    let mut out = String::with_capacity(line.len());
    let mut i = 0;
    let mut copy_from = 0;
    while i + 3 < bytes.len() {
        let at_boundary = i == 0 || {
            let p = bytes[i - 1];
            !(p.is_ascii_alphanumeric() || p == b'_')
        };
        if at_boundary && &bytes[i..i + 3] == b"u0:" && bytes[i + 3].is_ascii_digit() {
            let mut j = i + 3;
            while j < bytes.len() && bytes[j].is_ascii_digit() {
                j += 1;
            }
            let n: u32 = line[i + 3..j].parse().expect("u0:<digits> already matched");
            if let Some(name) = func_names.get(&n) {
                out.push_str(&line[copy_from..i]);
                out.push('@');
                out.push_str(name);
                i = j;
                copy_from = j;
                continue;
            }
            i = j;
            continue;
        }
        i += 1;
    }
    out.push_str(&line[copy_from..]);
    out
}

/// Inline-annotate the `(vN: ty, ...)` portion of a block header with the
/// IR type of each param. Skips params whose value-id is absent from
/// `value_tys`.
pub(crate) fn annotate_block_header(
    line: &str,
    value_tys: &HashMap<u32, crate::types::Ty>,
) -> String {
    // Append a trailing `; vN :: ty, vM :: ty` comment AFTER the
    // existing line, leaving the original CLIF text intact.
    let Some(open) = line.find('(') else {
        return line.to_string();
    };
    let Some(close) = line.rfind(')') else {
        return line.to_string();
    };
    if close <= open + 1 {
        return line.to_string();
    }
    let inner = &line[open + 1..close];
    let mut notes: Vec<String> = Vec::new();
    for p in inner.split(',') {
        let p_trim = p.trim();
        if let Some(rest) = p_trim.strip_prefix('v')
            && let Some((id_str, _ty)) = rest.split_once(':')
            && let Ok(id) = id_str.trim().parse::<u32>()
            && let Some(ty) = value_tys.get(&id)
        {
            notes.push(format!(
                "v{} :: {}",
                id,
                crate::concrete_types::ty_display(ty)
            ));
        }
    }
    if notes.is_empty() {
        line.to_string()
    } else {
        format!("{}    ;; {}", line.trim_end(), notes.join(", "))
    }
}

// Halt: receives a one-word result from the JIT and stores the
// debug-friendly i64 on the current Process's halt_value. Halt is a
// debugging seam; this preserves raw scalar halt values for existing tests
// while not constraining heap-typed semantics later.
//
// The second arg is the per-fn ABI's `ctx: *mut u8` (= *mut Process). For
// the migration we ignore it in favor of current_process() — they point at
// the same Process, but using current_process() keeps the access pattern
// uniform with every other fz_* fn.
// fz_halt moved to ir_runtime.rs (.23.4.13).
