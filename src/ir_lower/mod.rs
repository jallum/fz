//! AST -> fz-IR translator (core).
//!
//! Scope (per fz-ul4.11.16):
//! - Expr: literals, Var, BinOp, UnOp, Block, If, Match, List, Tuple, Call,
//!   Lambda. Multi-clause fn dispatch.
//! - Patterns: Wildcard, Var, literals, Tuple, List, As.
//! - Out of scope (returns LowerError::Unsupported): Case, Cond, With, Map,
//!   MapUpdate, Index, Bitstring expr/pattern, Map patterns, Quote/
//!   Unquote at IR translation. These land in fz-ul4.11.17.
//!
//! CPS-split: every non-tail Call closes the current fn with Term::Call and
//! starts a fresh continuation FnIr. The continuation's entry block params
//! are [result_var, ...captured_vars]. Lowering emits capture candidates from
//! the visible locals at the split point; `ir_capture_norm` makes that ABI
//! canonical before the module leaves lowering. Tail-position calls use
//! Term::TailCall.
//!
//! ## Unique-cont invariant (fz-uwq.1)
//!
//! "Fresh continuation per call site" is load-bearing, not just convenient.
//! Every `Cont.fn_id` referenced by a `Term::Call` / `Term::CallClosure`
//! must be unique across the whole module — no two
//! call-shaped terminators may share a continuation fn. Continuation
//! provenance, activation facts, and planned call edges all rely on each
//! continuation naming one return edge. `debug_assert_unique_conts` at the
//! end of `lower_program_full` pins the invariant down so a regression
//! in this file (or a future corner case) panics in debug rather than
//! corrupting downstream passes.

#[cfg(test)]
use crate::ast::MatchClause;
use crate::ast::{Attribute, Expr, FnDef, Item, Program, Spanned};
use crate::compiler::source::Span;
#[cfg(test)]
use crate::diag::{codes, emit_through};
#[cfg(test)]
use crate::dispatch_matrix::pattern::PatternBodyId;
use crate::dispatch_matrix::pattern::PatternSubjectRef;
#[cfg(test)]
use crate::exec::runtime::{DbgCapture, Runtime};
use crate::frontend::protocols::{
    PROTOCOL_ELEM_VAR, ProtocolImplFact, impl_target_type, impl_target_type_with_element,
};
use crate::frontend::resolve::flatten_modules;
#[cfg(test)]
use crate::fz_ir::{BinOp, BranchOrigin, Const, DeadBranch, ExternMarshal, FnBuilder, ModuleBuilder};
use crate::fz_ir::{
    BlockId, ContinuationProvenance, ContinuationProvenanceKind, ExternDecl, ExternId, ExternTy, FnCategory, FnId,
    FnIr, Module, Prim, SourceInfo, Stmt, Term, Var,
};
use crate::ir_capture_norm::normalize_continuation_captures;
#[cfg(test)]
use crate::ir_codegen::compile_planned;
#[cfg(test)]
use crate::ir_planner::{collect_diagnostics, plan_module_with_role};
use crate::modules::identity::ModuleName;
use crate::modules::runtime_library::{
    core_prelude_module_sources, interface, prelude_source, root_type_env_from_attrs,
};
use crate::parser::Parser;
use crate::parser::lexer::Lexer;
use crate::specs::{
    StructuralCorrespondenceGroup, StructuralOccurrence, StructuralPathStep, spec_set_correspondence_groups,
};
use crate::telemetry::Telemetry;
#[cfg(test)]
use crate::telemetry::{Capture, ConfiguredTelemetry, Value};
#[cfg(test)]
use crate::test_support::linked_runtime_graph;
use crate::type_expr::{ModuleTypeEnv, resolve_spec_decl_generic, resolve_spec_decls};
use crate::types::{Ty, TypeVarId, Types, check_brand_mint_visibility};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::mem::take;
use std::rc::Rc;

mod atom_table;
mod brand_erase;
#[cfg(test)]
mod brand_erase_test;
mod cond;
mod cps;
mod ctx;
mod error;
mod expr;
mod extern_table;
mod lambda;
mod param_guards;
mod pattern_dispatch;
mod receive;

// `LowerError` is the module's only public type: it is the coarse error in the
// public `lower_program` result. Everything else below is internal — these
// `use` aliases exist so sibling submodules share helpers through `super::*`,
// not as a crate-visible surface.
pub use error::LowerError;

use atom_table::AtomTable;
use brand_erase::erase_brands;
use cond::{lower_if, lower_multi_clause};
use cps::{
    ContFn, OwnedConsCapture, cont_call_args, cps_split_call, cps_split_call_closure, cps_split_external_call,
    finalize_arm, mint_cont_fn, switch_to_cont_fn,
};
use ctx::LowerCtx;
use expr::{bind_param_topname, lower_expr, lower_fn, lower_pattern_bind};
use extern_table::ExternTable;
pub(crate) use extern_table::{
    explicit_extern_wire_hint, extern_semantic_contract, extern_symbol_from_name, extern_ty_from_name,
};
use lambda::{collect_pattern_bound_names, collect_pattern_pinned_names, lower_lambda};
use param_guards::emit_param_type_guards;
use pattern_dispatch::{
    MatchedBinding, collect_dispatch_pinned_names_recursive, lower_guard_helper_call_to_dispatch,
    lower_source_patterns_to_current_fn, materialize_prepared_dispatch_key,
};
#[cfg(test)]
use receive::build_receive_pattern_rows;
use receive::lower_receive;

pub(crate) const REPL_ENTRY_PREFIX: &str = "__repl_eval_";

/// Return the prelude as a flat `Program` whose `module_type_envs[""]`,
/// `opaque_inners`, and `brand_inners` include compiler-known runtime
/// types plus any root declarations still present in `runtime.fz`.
fn parse_runtime_prelude<T: Types<Ty = Ty>>(
    t: &mut T,
    tel: &dyn Telemetry,
) -> (Program, HashMap<(String, usize), String>) {
    let runtime_fz = prelude_source();
    let (items, attrs) = parse_runtime_source_items(runtime_fz, "runtime.fz", tel);
    let root_types = root_type_env_from_attrs(t, &attrs);
    let prelude_imports = collect_runtime_prelude_imports(&items, tel);
    let mut items = items;
    for (name, source) in core_prelude_module_sources() {
        let (mut module_items, _module_attrs) = parse_runtime_source_items(source, name, tel);
        items.append(&mut module_items);
    }
    let staged = Program {
        attrs: Vec::new(),
        items,
        module_interfaces: Default::default(),
        external_module_interfaces: Default::default(),
        module_docs: Default::default(),
        module_type_envs: Default::default(),
        protocol_registry: Default::default(),
        opaque_inners: Default::default(),
        brand_inners: Default::default(),
        structs: Default::default(),
        struct_field_types: Default::default(),
    };
    let mut flat = flatten_modules(t, staged, tel).expect("runtime.fz module flatten error (bug in built-in prelude)");
    // Merge compiler-known runtime types and any root declarations into the
    // flattened prelude program.
    flat.module_type_envs
        .entry(String::new())
        .or_default()
        .extend_env(root_types.env);
    flat.opaque_inners.extend(root_types.opaque_inners);
    flat.brand_inners.extend(root_types.brand_inners);
    (flat, prelude_imports)
}

fn parse_runtime_source_items(src: &str, label: &str, tel: &dyn Telemetry) -> (Vec<Rc<Item>>, Vec<Attribute>) {
    let toks = Lexer::with_source_name(src, runtime_source_name(label))
        .tokenize(tel)
        .unwrap_or_else(|_| panic!("{label} lex error (bug in built-in prelude)"));
    Parser::new(toks)
        .parse_prelude()
        .unwrap_or_else(|_| panic!("{label} parse error (bug in built-in prelude)"))
}

fn runtime_source_name(label: &str) -> String {
    if label.ends_with(".fz") {
        format!("runtime:{label}")
    } else {
        format!("runtime:{label}.fz")
    }
}

fn collect_runtime_prelude_imports(items: &[Rc<Item>], tel: &dyn Telemetry) -> HashMap<(String, usize), String> {
    let mut out = HashMap::new();
    for item in items {
        match item.as_ref() {
            Item::Import {
                path,
                only,
                except,
                span,
            } => collect_runtime_prelude_import(&mut out, path, only.as_deref(), except.as_deref(), *span, tel),
            Item::Alias { .. } => {}
            _ => {}
        }
    }
    out
}

fn struct_opaque_inners<T: Types<Ty = Ty>>(
    t: &mut T,
    structs: &BTreeMap<ModuleName, Vec<String>>,
    struct_field_types: &BTreeMap<ModuleName, Vec<(String, Ty)>>,
) -> HashMap<String, Ty> {
    let mut out = HashMap::new();
    for (module, order) in structs {
        let Some(fields) = struct_field_types.get(module) else {
            continue;
        };
        let by_name = fields
            .iter()
            .map(|(name, ty)| (name.as_str(), ty.clone()))
            .collect::<HashMap<_, _>>();
        let ordered = order
            .iter()
            .map(|field| {
                by_name
                    .get(field.as_str())
                    .cloned()
                    .unwrap_or_else(|| panic!("struct field type invariant violated: `{}` lacks `{}`", module, field))
            })
            .collect::<Vec<_>>();
        out.insert(format!("impl-target::{}", module.last_segment()), t.tuple(&ordered));
    }
    out
}

fn collect_runtime_prelude_import(
    out: &mut HashMap<(String, usize), String>,
    module: &ModuleName,
    only: Option<&[(String, usize)]>,
    except: Option<&[(String, usize)]>,
    span: Span,
    tel: &dyn Telemetry,
) {
    let interface = interface(module, tel)
        .unwrap_or_else(|| panic!("runtime.fz imports unknown built-in runtime module `{}`", module));
    let mut exports = interface
        .exports
        .iter()
        .map(|export| (export.name.clone(), export.arity))
        .collect::<Vec<_>>();
    if let Some(only) = only {
        for requested in only {
            assert!(
                exports.contains(requested),
                "runtime.fz imports missing `{}/{}` from `{}`",
                requested.0,
                requested.1,
                module
            );
        }
        exports = only.to_vec();
    }
    if let Some(except) = except {
        exports.retain(|export| !except.contains(export));
    }
    for (name, arity) in exports {
        let previous = out.insert((name.clone(), arity), format!("{}.{}", module, name));
        assert!(
            previous.is_none(),
            "runtime.fz import for `{}/{}` conflicts at {:?}",
            name,
            arity,
            span
        );
    }
}

pub(crate) fn compute_current_function_correspondence(
    module: &mut Module,
    provenance: &HashMap<FnId, ContinuationProvenance>,
) {
    fn groups_to_sets(groups: &[StructuralCorrespondenceGroup]) -> Vec<BTreeSet<StructuralOccurrence>> {
        groups
            .iter()
            .map(|group| group.occurrences.iter().cloned().collect())
            .collect()
    }

    fn normalize_sets(mut sets: Vec<BTreeSet<StructuralOccurrence>>) -> Vec<BTreeSet<StructuralOccurrence>> {
        sets.retain(|set| set.len() > 1);
        let mut changed = true;
        while changed {
            changed = false;
            let mut i = 0;
            while i < sets.len() {
                let mut j = i + 1;
                while j < sets.len() {
                    if !sets[i].is_disjoint(&sets[j]) {
                        let right = sets.remove(j);
                        sets[i].extend(right);
                        changed = true;
                    } else {
                        j += 1;
                    }
                }
                i += 1;
            }
        }
        sets.sort();
        sets
    }

    fn sets_to_groups(sets: Vec<BTreeSet<StructuralOccurrence>>) -> Vec<StructuralCorrespondenceGroup> {
        normalize_sets(sets)
            .into_iter()
            .enumerate()
            .map(|(idx, occurrences)| StructuralCorrespondenceGroup {
                var: TypeVarId(idx as u32),
                occurrences: occurrences.into_iter().collect(),
            })
            .collect()
    }

    fn continuation_capture_param_index(provenance: &ContinuationProvenance, var: Var) -> Option<usize> {
        provenance
            .captured
            .iter()
            .position(|captured| *captured == var)
            .map(|slot| slot + provenance.capture_param_offset)
    }

    fn rebase_caller_groups(
        provenance: &ContinuationProvenance,
        caller_params: &[Var],
        groups: &[StructuralCorrespondenceGroup],
        rebase_callback_occurrences: bool,
    ) -> Vec<BTreeSet<StructuralOccurrence>> {
        groups
            .iter()
            .filter_map(|group| {
                let mut out = BTreeSet::new();
                for occ in &group.occurrences {
                    match occ {
                        StructuralOccurrence::Param { param_index, path } => {
                            let caller_var = caller_params.get(*param_index).copied()?;
                            let cont_param = continuation_capture_param_index(provenance, caller_var)?;
                            out.insert(StructuralOccurrence::Param {
                                param_index: cont_param,
                                path: path.clone(),
                            });
                        }
                        StructuralOccurrence::CallbackArg { param_index, .. }
                        | StructuralOccurrence::CallbackResult { param_index, .. }
                            if rebase_callback_occurrences =>
                        {
                            let caller_var = caller_params.get(*param_index).copied()?;
                            let cont_param = continuation_capture_param_index(provenance, caller_var)?;
                            out.insert(StructuralOccurrence::Param {
                                param_index: cont_param,
                                path: vec![],
                            });
                        }
                        StructuralOccurrence::CallbackArg { .. } | StructuralOccurrence::CallbackResult { .. } => {}
                        StructuralOccurrence::Result { path } => {
                            out.insert(StructuralOccurrence::Result { path: path.clone() });
                        }
                    }
                }
                (out.len() > 1).then_some(out)
            })
            .collect()
    }

    fn project_direct_callee_groups(
        provenance: &ContinuationProvenance,
        caller_fn: &FnIr,
        args: &[Var],
        groups: &[StructuralCorrespondenceGroup],
    ) -> Vec<BTreeSet<StructuralOccurrence>> {
        fn project_path_through_var(
            f: &FnIr,
            var: Var,
            path: &[StructuralPathStep],
        ) -> Vec<(Var, Vec<StructuralPathStep>)> {
            let prim = f.blocks.iter().find_map(|block| {
                block.stmts.iter().find_map(|stmt| match stmt {
                    Stmt::Let(bound, prim) if *bound == var => Some(prim),
                    _ => None,
                })
            });
            match prim {
                Some(Prim::MakeTuple(args)) => {
                    let Some(StructuralPathStep::TupleElem(index)) = path.first() else {
                        return Vec::new();
                    };
                    args.get(*index)
                        .map(|value| (*value, path[1..].to_vec()))
                        .into_iter()
                        .collect()
                }
                Some(Prim::MakeStruct { fields, .. }) => {
                    let Some(StructuralPathStep::StructField(name)) = path.first() else {
                        return Vec::new();
                    };
                    fields
                        .iter()
                        .find(|(field, _)| field == name)
                        .map(|(_, value)| (*value, path[1..].to_vec()))
                        .into_iter()
                        .collect()
                }
                Some(Prim::MakeList(elems, _)) => {
                    let Some(StructuralPathStep::ListElem) = path.first() else {
                        return Vec::new();
                    };
                    elems
                        .first()
                        .map(|value| (*value, path[1..].to_vec()))
                        .into_iter()
                        .collect()
                }
                Some(Prim::TupleField(base, index)) => {
                    let mut projected = vec![StructuralPathStep::TupleElem(*index as usize)];
                    projected.extend_from_slice(path);
                    vec![(*base, projected)]
                }
                Some(Prim::StructField(base, name)) => {
                    let mut projected = vec![StructuralPathStep::StructField(name.clone())];
                    projected.extend_from_slice(path);
                    vec![(*base, projected)]
                }
                Some(Prim::ListHead(base)) => {
                    let mut projected = vec![StructuralPathStep::ListElem];
                    projected.extend_from_slice(path);
                    vec![(*base, projected)]
                }
                Some(Prim::ListTail(base)) => vec![(*base, path.to_vec())],
                _ => vec![(var, path.to_vec())],
            }
        }

        groups
            .iter()
            .filter_map(|group| {
                let mut out = BTreeSet::new();
                for occ in &group.occurrences {
                    match occ {
                        StructuralOccurrence::Param { param_index, path } => {
                            let arg = args.get(*param_index).copied()?;
                            for (projected_var, projected_path) in project_path_through_var(caller_fn, arg, path) {
                                let Some(cont_param) = continuation_capture_param_index(provenance, projected_var)
                                else {
                                    continue;
                                };
                                out.insert(StructuralOccurrence::Param {
                                    param_index: cont_param,
                                    path: projected_path,
                                });
                            }
                        }
                        StructuralOccurrence::CallbackArg { param_index, .. }
                        | StructuralOccurrence::CallbackResult { param_index, .. } => {
                            let arg = args.get(*param_index).copied()?;
                            let cont_param = continuation_capture_param_index(provenance, arg)?;
                            out.insert(StructuralOccurrence::Param {
                                param_index: cont_param,
                                path: vec![],
                            });
                        }
                        StructuralOccurrence::Result { path } => {
                            out.insert(StructuralOccurrence::Param {
                                param_index: 0,
                                path: path.clone(),
                            });
                        }
                    }
                }
                (out.len() > 1).then_some(out)
            })
            .collect()
    }

    fn project_closure_call_groups(
        provenance: &ContinuationProvenance,
        caller_params: &[Var],
        closure: Var,
        args: &[Var],
        groups: &[StructuralCorrespondenceGroup],
    ) -> Vec<BTreeSet<StructuralOccurrence>> {
        let Some(caller_closure_param) = caller_params.iter().position(|param| *param == closure) else {
            return Vec::new();
        };
        groups
            .iter()
            .filter_map(|group| {
                let mut out = BTreeSet::new();
                for occ in &group.occurrences {
                    match occ {
                        StructuralOccurrence::Param { param_index, path } => {
                            let caller_var = caller_params.get(*param_index).copied()?;
                            let cont_param = continuation_capture_param_index(provenance, caller_var)?;
                            out.insert(StructuralOccurrence::Param {
                                param_index: cont_param,
                                path: path.clone(),
                            });
                        }
                        StructuralOccurrence::Result { path } => {
                            out.insert(StructuralOccurrence::Result { path: path.clone() });
                        }
                        StructuralOccurrence::CallbackArg {
                            param_index,
                            arg_index,
                            path,
                        } if *param_index == caller_closure_param => {
                            let arg = args.get(*arg_index).copied()?;
                            let cont_param = continuation_capture_param_index(provenance, arg)?;
                            out.insert(StructuralOccurrence::Param {
                                param_index: cont_param,
                                path: path.clone(),
                            });
                        }
                        StructuralOccurrence::CallbackResult { param_index, path }
                            if *param_index == caller_closure_param =>
                        {
                            out.insert(StructuralOccurrence::Param {
                                param_index: 0,
                                path: path.clone(),
                            });
                        }
                        _ => {}
                    }
                }
                (out.len() > 1).then_some(out)
            })
            .collect()
    }

    fn project_path_through_dispatch_subject(
        path: &[StructuralPathStep],
        subject: &PatternSubjectRef,
    ) -> Option<Vec<StructuralPathStep>> {
        fn strip_after_union_prefix(
            path: &[StructuralPathStep],
            want: StructuralPathStep,
        ) -> Option<Vec<StructuralPathStep>> {
            let mut i = 0;
            while matches!(path.get(i), Some(StructuralPathStep::UnionMember(_))) {
                i += 1;
            }
            (path.get(i) == Some(&want)).then(|| path[(i + 1)..].to_vec())
        }

        match subject {
            PatternSubjectRef::Input(_) => Some(path.to_vec()),
            PatternSubjectRef::TupleField { tuple, index } => {
                let inner = project_path_through_dispatch_subject(path, tuple)?;
                strip_after_union_prefix(&inner, StructuralPathStep::TupleElem(*index as usize))
            }
            PatternSubjectRef::ListHead(list) => {
                let inner = project_path_through_dispatch_subject(path, list)?;
                strip_after_union_prefix(&inner, StructuralPathStep::ListElem)
            }
            PatternSubjectRef::ListTail(list) => project_path_through_dispatch_subject(path, list),
            PatternSubjectRef::MapValue { .. } | PatternSubjectRef::BitstringField { .. } => None,
        }
    }

    fn project_dispatch_binding_groups(
        provenance: &ContinuationProvenance,
        bindings: &[(Var, PatternSubjectRef)],
        groups: &[StructuralCorrespondenceGroup],
    ) -> Vec<BTreeSet<StructuralOccurrence>> {
        fn binding_input_id(source: &PatternSubjectRef) -> Option<u32> {
            match source {
                PatternSubjectRef::Input(input_id) => Some(*input_id),
                PatternSubjectRef::TupleField { tuple, .. }
                | PatternSubjectRef::ListHead(tuple)
                | PatternSubjectRef::ListTail(tuple) => binding_input_id(tuple),
                PatternSubjectRef::MapValue { .. } | PatternSubjectRef::BitstringField { .. } => None,
            }
        }

        groups
            .iter()
            .filter_map(|group| {
                let mut out = BTreeSet::new();
                for occ in &group.occurrences {
                    match occ {
                        StructuralOccurrence::Param { param_index, path } => {
                            for (binding_var, source) in bindings {
                                let Some(input_id) = binding_input_id(source) else {
                                    continue;
                                };
                                if *param_index != input_id as usize {
                                    continue;
                                }
                                let Some(cont_param) = continuation_capture_param_index(provenance, *binding_var)
                                else {
                                    continue;
                                };
                                let Some(projected_path) = project_path_through_dispatch_subject(path, source) else {
                                    continue;
                                };
                                out.insert(StructuralOccurrence::Param {
                                    param_index: cont_param,
                                    path: projected_path,
                                });
                            }
                        }
                        StructuralOccurrence::Result { path } => {
                            out.insert(StructuralOccurrence::Result { path: path.clone() });
                        }
                        StructuralOccurrence::CallbackArg { .. } | StructuralOccurrence::CallbackResult { .. } => {}
                    }
                }
                (out.len() > 1).then_some(out)
            })
            .collect()
    }

    let mut changed = true;
    while changed {
        changed = false;
        for (&continuation, provenance) in provenance {
            let caller = module.fn_by_id(provenance.caller);
            let caller_params = caller.block(caller.entry).params.clone();
            let caller_groups = module
                .function_correspondence
                .get(&provenance.caller)
                .cloned()
                .unwrap_or_default();

            let mut sets = groups_to_sets(
                module
                    .function_correspondence
                    .get(&continuation)
                    .cloned()
                    .unwrap_or_default()
                    .as_slice(),
            );

            match &provenance.kind {
                ContinuationProvenanceKind::DirectCall { callee, args } => {
                    sets.extend(rebase_caller_groups(provenance, &caller_params, &caller_groups, true));
                    let callee_groups = module.function_correspondence.get(callee).cloned().unwrap_or_default();
                    sets.extend(project_direct_callee_groups(provenance, caller, args, &callee_groups));
                }
                ContinuationProvenanceKind::ClosureCall { closure, args } => {
                    sets.extend(rebase_caller_groups(provenance, &caller_params, &caller_groups, false));
                    sets.extend(project_closure_call_groups(
                        provenance,
                        &caller_params,
                        *closure,
                        args,
                        &caller_groups,
                    ));
                }
                ContinuationProvenanceKind::DispatchBody { bindings } => {
                    sets.extend(rebase_caller_groups(provenance, &caller_params, &caller_groups, true));
                    sets.extend(project_dispatch_binding_groups(provenance, bindings, &caller_groups));
                }
            }

            let new_groups = sets_to_groups(sets);
            let entry = module.function_correspondence.entry(continuation).or_default();
            if *entry != new_groups {
                *entry = new_groups;
                changed = true;
            }
        }
    }
}

/// Lower a resolved `Program` to its fz-IR `Module`.
///
/// The single public entry. Telemetry is threaded unconditionally so tests and
/// operators observe the same lowering surface. The atom table built during
/// lowering is folded into `module.atom_names`, so the `Module` is the complete
/// result — there is no second return value.
pub fn lower_program<T: Types<Ty = Ty>>(t: &mut T, prog: &Program, tel: &dyn Telemetry) -> Result<Module, LowerError> {
    let mut ctx = LowerCtx::new();
    ctx.struct_schemas.extend(
        prog.structs
            .iter()
            .map(|(name, fields)| (name.dotted(), fields.clone())),
    );
    ctx.register_external_interfaces(&prog.external_module_interfaces);
    ctx.register_protocol_registry(&prog.protocol_registry);
    ctx.register_interface_protocols(&prog.external_module_interfaces);

    // Prepend the built-in runtime prelude. `runtime.fz` contributes root
    // type aliases and imports; core prelude module sources (currently
    // Kernel) contribute the implementations those imports expose.
    let (prelude, prelude_imports) = parse_runtime_prelude(t, tel);
    ctx.prelude_imports = prelude_imports;
    ctx.struct_schemas.extend(
        prelude
            .structs
            .iter()
            .map(|(name, fields)| (name.dotted(), fields.clone())),
    );
    ctx.register_protocol_registry(&prelude.protocol_registry);
    ctx.register_external_interfaces(&prelude.external_module_interfaces);
    let prelude_type_env = prelude.module_type_envs.get("").cloned().unwrap_or_default();
    ctx.prelude_type_env = prelude_type_env.clone();
    // Build the combined type env: prelude aliases + all user-module aliases.
    let mut combined = prelude_type_env;
    for module_env in prog.module_type_envs.values() {
        combined.extend_env(module_env.clone());
    }
    ctx.combined_type_env = combined;
    let runtime_item_count = prelude.items.len();
    let all_items: Vec<Rc<Item>> = prelude
        .items
        .iter()
        .cloned()
        .chain(prog.items.iter().cloned())
        .collect();

    // Snapshot user FnDefs (non-extern, non-prelude) by (name, arity) for
    // guard helpers. Receive guards lower helper calls through DispatchMatrix
    // dispatch; non-receive dispatch still uses the AST fallback until
    // the general matcher fallback is removed.
    for item in all_items.iter().skip(runtime_item_count) {
        if let Item::Fn(fn_def) = item.as_ref()
            && fn_def.extern_abi.is_none()
        {
            let arity = fn_def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
            ctx.fn_defs_by_arity
                .entry((fn_def.name.clone(), arity))
                .or_insert_with(|| fn_def.clone());
        }
    }

    // Registration pass: assign ExternIds and FnIds in a single sweep.
    // Prelude items come first; recording prelude_fn_id_cutoff after them
    // lets build_source_info ignore prelude var spans (both halves restart
    // Var numbering at 0, so user spans must not be overwritten).
    for item in all_items.iter().take(runtime_item_count) {
        if let Item::Fn(fn_def) = item.as_ref() {
            if fn_def.extern_abi.is_some() {
                let eid = ExternId(ctx.next_extern);
                ctx.next_extern += 1;
                let signature = lower_extern_signature(t, fn_def, &ctx.prelude_type_env)?;
                ctx.extern_decls.push(ExternDecl {
                    id: eid,
                    fz_name: fn_def.name.clone(),
                    symbol: extern_symbol_from_name(&fn_def.name).to_string(),
                    params: signature.params,
                    variadic: fn_def.variadic,
                    ret: signature.ret,
                    ret_descr: signature.return_ty,
                    semantic_contract: signature.semantic_contract,
                });
                ctx.externs.insert(fn_def.name.clone(), eid);
            } else {
                let arity = fn_def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
                let id = ctx.mb.fresh_fn_id();
                ctx.fns.insert((fn_def.name.clone(), arity), id);
            }
        }
    }
    // fz-qbg.2 — Lower prelude bodies *before* registering user FnIds.
    // Prelude lowering may mint continuation fns (multi-clause prelude
    // fns like `print` now route each clause through a
    // body cont fn). Doing user registration AFTER prelude body lowering
    // keeps user FnIds contiguous and all >= prelude_fn_id_cutoff —
    // so `build_source_info` correctly excludes every prelude-origin
    // FnId (source plus minted conts) from the user var-meta table.
    for item in all_items.iter().take(runtime_item_count) {
        if let Item::Fn(fn_def) = item.as_ref()
            && fn_def.extern_abi.is_none()
        {
            lower_fn(&mut ctx, t, fn_def, FnCategory::Prelude)?;
        }
    }
    ctx.prelude_fn_id_cutoff = ctx.mb.next_fn_id();

    for item in all_items.iter().skip(runtime_item_count) {
        match item.as_ref() {
            Item::Fn(fn_def) => {
                if fn_def.extern_abi.is_some() {
                    let eid = ExternId(ctx.next_extern);
                    ctx.next_extern += 1;
                    let signature = lower_extern_signature(t, fn_def, &ctx.prelude_type_env)?;
                    ctx.extern_decls.push(ExternDecl {
                        id: eid,
                        fz_name: fn_def.name.clone(),
                        symbol: extern_symbol_from_name(&fn_def.name).to_string(),
                        params: signature.params,
                        variadic: fn_def.variadic,
                        ret: signature.ret,
                        ret_descr: signature.return_ty,
                        semantic_contract: signature.semantic_contract,
                    });
                    ctx.externs.insert(fn_def.name.clone(), eid);
                } else {
                    let arity = fn_def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
                    let id = ctx.mb.fresh_fn_id();
                    ctx.fns.insert((fn_def.name.clone(), arity), id);
                    // fz-jg5.12 (RED.9): a user fn with an @spec is a
                    // reduction boundary — the spec is a signed contract.
                    if fn_def.attrs.iter().any(|a| matches!(a, Attribute::Spec(_))) {
                        ctx.boundary_fns.insert(id);
                    }
                }
            }
            Item::Module(m) => {
                return Err(LowerError::Unsupported {
                    span: m.span,
                    what: "Item::Module should be flattened by resolve before lowering".into(),
                });
            }
            Item::Protocol(p) => {
                return Err(LowerError::Unsupported {
                    span: p.span,
                    what: "protocol declarations are not lowered before protocol resolution".into(),
                });
            }
            Item::ProtocolImpl(i) => {
                return Err(LowerError::Unsupported {
                    span: i.span,
                    what: "protocol implementations are not lowered before protocol resolution".into(),
                });
            }
            Item::Struct(_) => {}
            Item::Alias { span, .. } | Item::Import { span, .. } => {
                return Err(LowerError::Unsupported {
                    span: *span,
                    what: "alias/import should be consumed by resolve before lowering".into(),
                });
            }
            Item::MacroCall { name, span, .. } => {
                return Err(LowerError::PostExpansionNode {
                    span: *span,
                    what: format!("MacroCall({})", name),
                });
            }
        }
    }

    // Second pass: lower user fn bodies. (Prelude bodies were already
    // lowered above, before user FnId registration — see the fz-qbg.2
    // note for why.)
    for item in all_items.iter().skip(runtime_item_count) {
        if let Item::Fn(fn_def) = item.as_ref()
            && fn_def.extern_abi.is_none()
        {
            lower_fn(&mut ctx, t, fn_def, user_fn_category(fn_def))?;
        }
    }

    // Take the module out first; `ctx.mb` is moved but `ctx` itself is
    // still usable for source-info collection.
    let mb = take(&mut ctx.mb);
    let mut module = mb.build();
    module.protocol_registry = prog.protocol_registry.clone();
    module
        .protocol_registry
        .protocols
        .extend(prelude.protocol_registry.protocols.clone());
    module
        .protocol_registry
        .impls
        .extend(prelude.protocol_registry.impls.clone());
    module
        .protocol_registry
        .extend_interfaces(&prog.external_module_interfaces);
    module.source = build_source_info(&module, &ctx);
    module.atom_names = ctx.atoms.names();
    module.externs = take(&mut ctx.extern_decls);
    for (i, e) in module.externs.iter().enumerate() {
        module.extern_idx.insert(e.id, i);
    }
    module.boundary_fns = take(&mut ctx.boundary_fns);
    let empty_env = ModuleTypeEnv::new();
    for item in &all_items {
        let Item::Fn(fn_def) = item.as_ref() else {
            continue;
        };
        let specs = fn_def
            .attrs
            .iter()
            .filter_map(|a| match a {
                Attribute::Spec(spec) => Some(spec),
                _ => None,
            })
            .collect::<Vec<_>>();
        if specs.is_empty() {
            continue;
        }
        let arity = fn_def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
        let Some(&fid) = ctx.fns.get(&(fn_def.name.clone(), arity)) else {
            continue;
        };
        let module_path = fn_def
            .name
            .rfind('.')
            .map(|i| fn_def.name[..i].to_string())
            .unwrap_or_default();
        let env = if fid.0 < ctx.prelude_fn_id_cutoff {
            prelude.module_type_envs.get("").unwrap_or(&empty_env)
        } else {
            prog.module_type_envs
                .get(&module_path)
                .unwrap_or(&ctx.combined_type_env)
        };
        if let Ok(resolved) = resolve_spec_decls(t, specs, env) {
            module
                .function_correspondence
                .insert(fid, spec_set_correspondence_groups(&resolved));
            module.declared_specs.insert(fid, resolved);
        }
    }
    install_inherited_protocol_callback_specs(
        t,
        &mut module,
        &ctx.fns,
        &prog.module_type_envs,
        &prelude.module_type_envs,
        &ctx.combined_type_env,
    );
    let continuation_provenance = ctx.continuation_provenance;
    module.continuation_provenance = continuation_provenance.clone();
    compute_current_function_correspondence(&mut module, &continuation_provenance);
    // fz-swt.8 — carry the resolver's opaque-inner-type map onto the
    // Module so the planner can resolve `handle.value` accesses to T.
    // Runtime built-in inners (utf8 brand, pid/ref opaques, ...) live in the
    // flat-prelude Program, merged here alongside user inners.
    module.opaque_inners = prog.opaque_inners.clone();
    module.opaque_inners.extend(prelude.opaque_inners.clone());
    module
        .opaque_inners
        .extend(struct_opaque_inners(t, &prog.structs, &prog.struct_field_types));
    module
        .opaque_inners
        .extend(struct_opaque_inners(t, &prelude.structs, &prelude.struct_field_types));
    module.brand_inners = prog.brand_inners.clone();
    module.brand_inners.extend(prelude.brand_inners.clone());
    module.struct_schemas = ctx.struct_schemas.clone();
    // fz-02r.4 — annotate TailCall back-edges from the structural SCC.
    annotate_back_edges(&mut module, &ctx.fn_spans)?;
    // fz-axu.24 (M3) — brand-mint visibility. Must run before erasure
    // because erasure drops the Brand prims this pass needs to see.
    // Built-in brands (utf8, ...) have no module owner and pass
    // trivially; the gate fires when user-declared brands acquire a
    // mint syntax and a foreign module tries to use it.
    check_brand_visibility(t, &module, &ctx.stmt_spans, &ctx.fn_spans)?;
    // fz-axu.23 (M2) — brand erasure is the final lowering phase. The
    // Module returned from lower_program has the invariant: no
    // Prim::Brand survives in any FnIr. Downstream passes (planner,
    // reducer, codegen, interp, DCE) can treat that as a precondition,
    // and their Brand match arms become `unreachable!()` rather than
    // silent identity-fallbacks.
    erase_brands(&mut module);
    normalize_continuation_captures(&mut module, tel);
    // fz-uwq.1 — verify the unique-cont invariant the post-type pipeline
    // depends on. See `debug_assert_unique_conts` for the contract.
    debug_assert_unique_conts(&module);
    Ok(module)
}

fn install_inherited_protocol_callback_specs<T: Types<Ty = Ty>>(
    t: &mut T,
    module: &mut Module,
    fns: &HashMap<(String, usize), FnId>,
    prog_type_envs: &HashMap<String, ModuleTypeEnv>,
    prelude_type_envs: &HashMap<String, ModuleTypeEnv>,
    combined_type_env: &ModuleTypeEnv,
) {
    let impls = module.protocol_registry.impls.values().cloned().collect::<Vec<_>>();
    for implementation in impls {
        let Some(protocol) = module
            .protocol_registry
            .protocols
            .get(&implementation.protocol)
            .cloned()
        else {
            continue;
        };
        for callback in protocol.callbacks {
            if callback.specs.is_empty() {
                continue;
            }
            let key = (callback.name.clone(), callback.arity);
            let Some(export) = implementation.callbacks.get(&key) else {
                continue;
            };
            let fn_name = format!("{}.{}", export.module, export.name);
            let Some(&fid) = fns.get(&(fn_name, export.arity)) else {
                continue;
            };
            if module.declared_specs.contains_key(&fid) {
                continue;
            }
            let env =
                inherited_protocol_spec_env(t, &implementation, prog_type_envs, prelude_type_envs, combined_type_env);
            if let Ok(resolved) = resolve_spec_decls(t, callback.specs.iter(), &env) {
                module
                    .function_correspondence
                    .insert(fid, spec_set_correspondence_groups(&resolved));
                module.declared_specs.insert(fid, resolved);
            }
        }
    }
}

fn inherited_protocol_spec_env<T: Types<Ty = Ty>>(
    t: &mut T,
    implementation: &ProtocolImplFact,
    prog_type_envs: &HashMap<String, ModuleTypeEnv>,
    prelude_type_envs: &HashMap<String, ModuleTypeEnv>,
    combined_type_env: &ModuleTypeEnv,
) -> ModuleTypeEnv {
    let mut env = prog_type_envs
        .get(&implementation.protocol.dotted())
        .or_else(|| prelude_type_envs.get(&implementation.protocol.dotted()))
        .cloned()
        .unwrap_or_else(|| combined_type_env.clone());
    let target_ty = impl_target_type(t, &implementation.target);
    let element = t.type_var(PROTOCOL_ELEM_VAR);
    let target_template = impl_target_type_with_element(t, &implementation.target, element);
    env.insert("t".to_string(), target_ty.clone());
    env.insert(format!("{}.t", implementation.protocol), target_ty);
    env.insert_protocol_domain("t".to_string(), target_template.clone());
    env.insert_protocol_domain(format!("{}.t", implementation.protocol), target_template);
    env
}

pub(crate) fn repl_output_frame_names(input_frame: &[String], expr: &Spanned<Expr>) -> Vec<String> {
    let mut out = input_frame.to_vec();
    let mut new_names = Vec::new();
    if let Expr::Match(pattern, _) = &expr.node {
        lambda::collect_pattern_bound_names(&pattern.node, &mut new_names);
    }
    new_names.sort();
    new_names.dedup();
    for name in new_names {
        if !out.contains(&name) {
            out.push(name);
        }
    }
    out
}

fn user_fn_category(fn_def: &FnDef) -> FnCategory {
    if fn_def.name.starts_with(REPL_ENTRY_PREFIX) {
        FnCategory::ReplEntry
    } else {
        FnCategory::User
    }
}

/// fz-uwq.1 — verify the **unique-cont invariant**: every `Cont.fn_id`
/// referenced by a `Term::Call` / `Term::CallClosure`
/// appears as the continuation of **exactly one** such terminator across
/// the whole module.
///
/// ## Why this is load-bearing
///
/// Continuation provenance, activation facts, and planned call edges use
/// continuation `FnId`s as edge identities. Sharing one continuation fn across
/// two call-shaped terminators would merge two distinct return edges and make
/// the data model incoherent.
///
/// The lowerer guarantees uniqueness structurally: `lower_expr` and
/// friends mint a **fresh** continuation FnIr for each non-tail call
/// they CPS-split. No path in `ir_lower` produces two terminators that
/// share the same `Cont.fn_id`. This assertion pins the structural
/// guarantee down so a future change to the lowerer (or a corner case
/// not yet exercised) cannot silently break the downstream pipeline.
///
/// See `.agent/docs/dispatch-as-planner-output.md` (Worry 1) for the stress-test
/// that named this invariant.
///
/// Debug-build only — the check is O(blocks) but redundant in release
/// when the lowerer is correct. If it ever fires in debug, the lowerer
/// is wrong (or a new corner case needs the invariant documented away).
/// fz-axu.24 (M3) — brand-mint visibility pass. Walks every Prim::Brand
/// stmt in every fn and applies `check_brand_mint_visibility`, using
/// the containing fn's name to derive the using_module (everything
/// before the final `.` in the qualified fn name; "" for top-level
/// fns). Built-in brands like `utf8` carry no `::` qualifier and pass
/// trivially.
///
/// Runs between annotate_back_edges and erase_brands — must see Brand
/// prims, which erase_brands removes.
fn check_brand_visibility<T: Types>(
    _t: &mut T,
    module: &Module,
    stmt_spans: &HashMap<(FnId, BlockId), Vec<Span>>,
    fn_spans: &HashMap<FnId, Span>,
) -> Result<(), LowerError> {
    for f in &module.fns {
        let using_module = f.name.rfind('.').map(|i| &f.name[..i]).unwrap_or("");
        for block in &f.blocks {
            let spans = stmt_spans.get(&(f.id, block.id));
            for (i, stmt) in block.stmts.iter().enumerate() {
                let Stmt::Let(_, prim) = stmt;
                if let Prim::Brand(_, brand_tag) = prim
                    && let Err(e) = check_brand_mint_visibility(brand_tag, using_module)
                {
                    let span = spans
                        .and_then(|v| v.get(i).copied())
                        .or_else(|| fn_spans.get(&f.id).copied())
                        .unwrap_or(Span::DUMMY);
                    return Err(LowerError::BrandMintVisibility {
                        span,
                        brand: e.opaque,
                        owner_module: e.owner_module,
                        using_module: e.using_module,
                    });
                }
            }
        }
    }
    Ok(())
}

fn debug_assert_unique_conts(module: &Module) {
    if !cfg!(debug_assertions) {
        return;
    }
    let mut seen: HashMap<FnId, (FnId, BlockId)> = HashMap::new();
    for f in &module.fns {
        for b in &f.blocks {
            let cont_fn = match &b.terminator {
                Term::Call { continuation, .. } | Term::CallClosure { continuation, .. } => continuation.fn_id,
                _ => continue,
            };
            if let Some(prev) = seen.insert(cont_fn, (f.id, b.id)) {
                panic!(
                    "fz-uwq.1 invariant violated: cont fn {:?} referenced by two terminators: \
                     {:?}:{:?} and {:?}:{:?}. The lowerer must mint a fresh continuation \
                     FnIr per call site; sharing merges distinct return edges.",
                    cont_fn, prev.0, prev.1, f.id, b.id
                );
            }
        }
    }
}

pub(crate) struct LoweredExternSignature<Ty> {
    pub params: Vec<ExternTy>,
    pub ret: ExternTy,
    pub return_ty: Ty,
    pub semantic_contract: crate::type_expr::ResolvedSpecDecl<Ty>,
}

/// Resolve one extern declaration into semantic upper bounds plus ABI lanes.
///
/// Semantics come from the normalized extern contract surface:
/// `cstring -> binary` and `unit -> nil`. Wire lanes keep the explicit extern
/// marshal hints, then fall back to the resolved semantic upper bound with
/// constrained vars instantiated to their declared bounds.
pub(crate) fn lower_extern_signature<T: Types>(
    t: &mut T,
    fn_def: &FnDef,
    type_env: &ModuleTypeEnv<T::Ty>,
) -> Result<LoweredExternSignature<T::Ty>, LowerError> {
    let contract = extern_semantic_contract(fn_def).ok_or_else(|| LowerError::Unsupported {
        span: fn_def.name_span,
        what: format!("`{}` is not an extern declaration", fn_def.name),
    })?;
    let resolved = resolve_spec_decl_generic(t, &contract, type_env).map_err(|error| LowerError::Unsupported {
        span: error.span,
        what: format!("could not resolve extern contract for `{}`: {}", fn_def.name, error.msg),
    })?;
    let crate::type_expr::ResolvedSpecDecl {
        params: semantic_params,
        result: semantic_result,
        constraints,
    } = resolved;
    let params = fn_def
        .extern_param_tokens
        .iter()
        .zip(semantic_params.iter())
        .map(|(body, ty)| lower_extern_wire_ty(t, body, ty, &constraints))
        .collect();
    let return_upper_bound = if constraints.is_empty() {
        semantic_result.clone()
    } else {
        t.instantiate(&semantic_result, &constraints)
    };
    let ret = lower_extern_wire_ty(t, &fn_def.extern_ret_tokens, &return_upper_bound, &constraints);
    Ok(LoweredExternSignature {
        params,
        ret,
        return_ty: semantic_result.clone(),
        semantic_contract: crate::type_expr::ResolvedSpecDecl {
            params: semantic_params,
            result: semantic_result,
            constraints,
        },
    })
}

/// Derive a coarse C-ABI wire type from a semantic Ty.
///
/// Explicit marshal hints should already have been handled before this point.
/// The fallback uses the semantic upper bound: raw integer lanes cover both
/// `integer` and `cpointer`; float-only types get F64; nil-only → Unit;
/// never → Never. Everything else stays as a tagged value.
pub(crate) fn ty_to_extern_ty<T: Types>(t: &mut T, d: &T::Ty) -> ExternTy {
    if t.is_empty(d) {
        return ExternTy::Never;
    }
    if t.is_nil(d) {
        return ExternTy::Unit;
    }
    if t.is_floating(d) {
        return ExternTy::F64;
    }
    let int = t.int();
    let cpointer = t.cpointer();
    let raw_word = t.union(int, cpointer);
    if t.is_subtype(d, &raw_word) {
        return ExternTy::I64;
    }
    ExternTy::Any
}

fn lower_extern_wire_ty<T: Types>(
    t: &mut T,
    body: &crate::ast::TypeExprBody,
    semantic_ty: &T::Ty,
    constraints: &HashMap<TypeVarId, T::Ty>,
) -> ExternTy {
    if let Some(hint) = explicit_extern_wire_hint(body) {
        return hint;
    }
    let upper_bound = if constraints.is_empty() {
        semantic_ty.clone()
    } else {
        t.instantiate(semantic_ty, constraints)
    };
    ty_to_extern_ty(t, &upper_bound)
}

pub(super) fn concrete_any_tuple<T: Types<Ty = Ty>>(t: &mut T, arity: usize) -> Ty {
    let elems: Vec<Ty> = (0..arity).map(|_| t.any()).collect();
    t.tuple(&elems)
}

pub(super) fn concrete_any_map<T: Types<Ty = Ty>>(t: &mut T) -> Ty {
    t.map_top()
}

/// Post-lowering pass: compute the SCC of the fn-level call graph and set
/// `is_back_edge` on every `Term::TailCall` whose callee is in the same SCC
/// as the caller (i.e., the call is on a loop back-edge).
fn annotate_back_edges(module: &mut Module, _fn_spans: &HashMap<FnId, Span>) -> Result<(), LowerError> {
    // Build call graph: FnId → set of FnIds it tail-calls.
    let mut graph: HashMap<FnId, HashSet<FnId>> = HashMap::new();
    for f in &module.fns {
        let entry = graph.entry(f.id).or_default();
        for block in &f.blocks {
            if let Term::TailCall { callee, .. } = &block.terminator {
                entry.insert(*callee);
            }
        }
    }

    // Tarjan SCC on the call graph.
    let scc_of = {
        let mut index_counter = 0usize;
        let mut stack: Vec<FnId> = Vec::new();
        let mut on_stack: HashSet<FnId> = HashSet::new();
        let mut index: HashMap<FnId, usize> = HashMap::new();
        let mut lowlink: HashMap<FnId, usize> = HashMap::new();
        let mut scc_of: HashMap<FnId, usize> = HashMap::new();
        let mut scc_count = 0usize;
        let all_fns: Vec<FnId> = module.fns.iter().map(|f| f.id).collect();

        fn strongconnect(
            v: FnId,
            graph: &HashMap<FnId, HashSet<FnId>>,
            index_counter: &mut usize,
            stack: &mut Vec<FnId>,
            on_stack: &mut HashSet<FnId>,
            index: &mut HashMap<FnId, usize>,
            lowlink: &mut HashMap<FnId, usize>,
            scc_of: &mut HashMap<FnId, usize>,
            scc_count: &mut usize,
        ) {
            let v_index = *index_counter;
            index.insert(v, v_index);
            lowlink.insert(v, v_index);
            *index_counter += 1;
            stack.push(v);
            on_stack.insert(v);

            if let Some(neighbors) = graph.get(&v) {
                let neighbors: Vec<FnId> = neighbors.iter().copied().collect();
                for w in neighbors {
                    if !index.contains_key(&w) {
                        strongconnect(
                            w,
                            graph,
                            index_counter,
                            stack,
                            on_stack,
                            index,
                            lowlink,
                            scc_of,
                            scc_count,
                        );
                        let w_ll = lowlink[&w];
                        let v_ll = lowlink.get_mut(&v).unwrap();
                        if w_ll < *v_ll {
                            *v_ll = w_ll;
                        }
                    } else if on_stack.contains(&w) {
                        let w_idx = index[&w];
                        let v_ll = lowlink.get_mut(&v).unwrap();
                        if w_idx < *v_ll {
                            *v_ll = w_idx;
                        }
                    }
                }
            }

            if lowlink[&v] == index[&v] {
                let scc_id = *scc_count;
                *scc_count += 1;
                loop {
                    let w = stack.pop().unwrap();
                    on_stack.remove(&w);
                    scc_of.insert(w, scc_id);
                    if w == v {
                        break;
                    }
                }
            }
        }

        for fid in &all_fns {
            if !index.contains_key(fid) {
                strongconnect(
                    *fid,
                    &graph,
                    &mut index_counter,
                    &mut stack,
                    &mut on_stack,
                    &mut index,
                    &mut lowlink,
                    &mut scc_of,
                    &mut scc_count,
                );
            }
        }
        scc_of
    };

    for f in &mut module.fns {
        let caller_scc = scc_of.get(&f.id).copied().unwrap_or(usize::MAX);
        for block in &mut f.blocks {
            if let Term::TailCall {
                ident: _,
                callee,
                is_back_edge,
                ..
            } = &mut block.terminator
            {
                let callee_scc = scc_of.get(callee).copied().unwrap_or(usize::MAX);
                if callee_scc == caller_scc {
                    *is_back_edge = true;
                }
            }
        }
    }
    Ok(())
}

/// Collect the per-fn metadata accumulated on `ctx` into `Module.source`.
/// Var spans/names indexed by Var.0; per-block stmt/term spans flow through
/// unchanged; per-fn spans indexed by FnId.0.
fn build_source_info(module: &Module, ctx: &LowerCtx) -> SourceInfo {
    let max_fn_id = module.fns.iter().map(|f| f.id.0).max().unwrap_or(0);
    let mut fn_span = vec![Span::DUMMY; (max_fn_id as usize) + 1];
    for (fid, sp) in &ctx.fn_spans {
        let idx = fid.0 as usize;
        if idx < fn_span.len() {
            fn_span[idx] = *sp;
        }
    }
    // Var spans/names: pick the maximum Var across user-program fns only.
    // Each fn's Vars restart at 0, so we maintain one global table indexed
    // by Var.0. Prelude fns (FnId < prelude_fn_id_cutoff) are excluded:
    // their spans are byte offsets into runtime.fz, not the user source,
    // and would overwrite user-program entries that share the same Var.0.
    let cutoff = ctx.prelude_fn_id_cutoff;
    let max_var = ctx
        .var_meta
        .keys()
        .filter(|(fid, _)| fid.0 >= cutoff)
        .map(|(_, v)| v.0)
        .max()
        .unwrap_or(0);
    let n = (max_var as usize) + 1;
    let mut var_span = vec![Span::DUMMY; n];
    let mut var_name = vec![String::new(); n];
    for ((fid, v), (sp, name)) in &ctx.var_meta {
        if fid.0 < cutoff {
            continue; // skip prelude fn metadata
        }
        let idx = v.0 as usize;
        if idx < n {
            if var_span[idx].is_dummy() {
                var_span[idx] = *sp;
            }
            if var_name[idx].is_empty() {
                var_name[idx] = name.clone();
            }
        }
    }
    SourceInfo {
        var_span,
        var_name,
        stmt_spans: ctx.stmt_spans.clone(),
        term_span: ctx.term_spans.clone(),
        fn_span,
    }
}

#[cfg(test)]
mod ir_lower_test;
