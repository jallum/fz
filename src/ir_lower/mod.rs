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
use crate::compiler::{Compiler, CompilerWorld, FnGroupDescriptor, LoweredFnGroup, ModuleId};
use crate::diag::Span;
#[cfg(test)]
use crate::diag::{codes, emit_through};
use crate::exec::matcher::SubjectRef;
#[cfg(test)]
use crate::exec::matcher::{GuardExpr, Matcher, MatcherConst, MatcherNode};
#[cfg(test)]
use crate::exec::runtime::{DbgCapture, Runtime};
use crate::frontend::protocols::{
    PROTOCOL_ELEM_VAR, ProtocolImplFact, impl_target_type, impl_target_type_with_element,
};
#[cfg(test)]
use crate::frontend::resolve::flatten_modules;
#[cfg(test)]
use crate::fz_ir::{BinOp, BranchOrigin, Const, DeadBranch, ExternMarshal, FnBuilder, ModuleBuilder};
use crate::fz_ir::{
    BlockId, ContinuationProvenance, ContinuationProvenanceKind, ExternDecl, ExternId, ExternTy, FnCategory, FnId,
    FnIr, Module, Prim, SourceInfo, Stmt, Term, Var,
};
use crate::ir_capture_norm::normalize_continuation_captures_with_telemetry;
#[cfg(test)]
use crate::ir_codegen::compile_planned;
#[cfg(test)]
use crate::ir_planner::{collect_diagnostics, plan_module};
use crate::modules::identity::ModuleName;
use crate::modules::runtime_library::{interface, root_type_env_from_attrs};
#[cfg(test)]
use crate::parser::Parser;
#[cfg(test)]
use crate::parser::lexer::Lexer;
use crate::parser::lexer::Tok;
#[cfg(test)]
use crate::pattern_matrix::BodyId;
use crate::specs::{
    StructuralCorrespondenceGroup, StructuralOccurrence, StructuralPathStep, spec_set_correspondence_groups,
};
use crate::telemetry::Telemetry;
#[cfg(test)]
use crate::telemetry::{Capture, ConfiguredTelemetry, NullTelemetry, Value, bus};
#[cfg(test)]
use crate::test_support::linked_runtime_graph_with_telemetry;
use crate::type_expr::{ModuleTypeEnv, parse_type_expr, resolve_spec_decls};
use crate::types::{Ty, TypeVarId, Types, check_brand_mint_visibility};
use crate::{measurements, metadata};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
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
mod matcher;
mod param_guards;
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
use extern_table::{ExternTable, extern_symbol_from_name, extern_ty_from_name};
use lambda::{collect_pattern_bound_names, collect_pattern_pinned_names, lower_lambda};
use matcher::{
    MatchedBinding, collect_matcher_pinned_names_recursive, lower_guard_helper_call_to_dispatch,
    lower_pattern_matrix_to_current_fn, materialize_prepared_matcher_key,
};
use param_guards::emit_param_type_guards;
#[cfg(test)]
use receive::build_receive_pattern_matrix;
use receive::lower_receive;

pub(crate) const REPL_ENTRY_PREFIX: &str = "__repl_eval_";

/// Return the prelude as a flat `Program` whose `module_type_envs[""]`,
/// `opaque_inners`, and `brand_inners` include compiler-known runtime
/// types plus any root declarations still present in `runtime.fz`.
fn parse_runtime_prelude<T: Types<Ty = Ty>>(
    compiler: &mut CompilerWorld,
    t: &mut T,
    tel: &dyn Telemetry,
) -> (Program, HashMap<(String, usize), String>) {
    let prelude_id = compiler.discover_primitive_prelude(tel);
    let parsed_prelude = compiler
        .ensure_prelude(prelude_id, tel)
        .expect("runtime.fz parse error (bug in built-in prelude)");
    let items = parsed_prelude.items;
    let attrs = parsed_prelude.attrs;
    let root_types = root_type_env_from_attrs(t, &attrs);
    let prelude_imports = collect_runtime_prelude_imports(compiler, tel, &items);
    let staged = Program {
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
    let mut flat = crate::frontend::resolve::flatten_modules_with_compiler(t, compiler, None, staged, tel)
        .expect("runtime.fz module flatten error (bug in built-in prelude)");
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

fn collect_runtime_prelude_imports(
    compiler: &mut CompilerWorld,
    tel: &dyn Telemetry,
    items: &[Rc<Item>],
) -> HashMap<(String, usize), String> {
    let mut out = HashMap::new();
    for item in items {
        match item.as_ref() {
            Item::Import {
                path,
                only,
                except,
                span,
            } => {
                collect_runtime_prelude_import(compiler, tel, &mut out, path, only.as_deref(), except.as_deref(), *span)
            }
            Item::Alias { .. } => {
                panic!("runtime.fz prelude aliases are not supported; use import")
            }
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
    compiler: &mut CompilerWorld,
    tel: &dyn Telemetry,
    out: &mut HashMap<(String, usize), String>,
    module: &ModuleName,
    only: Option<&[(String, usize)]>,
    except: Option<&[(String, usize)]>,
    span: Span,
) {
    let interface = interface(compiler, module, tel)
        .expect("runtime interface lookup must succeed")
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

    fn project_path_through_matcher_subject(
        path: &[StructuralPathStep],
        subject: &SubjectRef,
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
            SubjectRef::Input(_) => Some(path.to_vec()),
            SubjectRef::TupleField { tuple, index } => {
                let inner = project_path_through_matcher_subject(path, tuple)?;
                strip_after_union_prefix(&inner, StructuralPathStep::TupleElem(*index as usize))
            }
            SubjectRef::ListHead(list) => {
                let inner = project_path_through_matcher_subject(path, list)?;
                strip_after_union_prefix(&inner, StructuralPathStep::ListElem)
            }
            SubjectRef::ListTail(list) => project_path_through_matcher_subject(path, list),
            SubjectRef::MapValue { .. } | SubjectRef::BitstringField { .. } => None,
        }
    }

    fn project_matcher_binding_groups(
        provenance: &ContinuationProvenance,
        bindings: &[(Var, SubjectRef)],
        groups: &[StructuralCorrespondenceGroup],
    ) -> Vec<BTreeSet<StructuralOccurrence>> {
        fn binding_input_id(source: &SubjectRef) -> Option<u32> {
            match source {
                SubjectRef::Input(input_id) => Some(input_id.0),
                SubjectRef::TupleField { tuple, .. } | SubjectRef::ListHead(tuple) | SubjectRef::ListTail(tuple) => {
                    binding_input_id(tuple)
                }
                SubjectRef::MapValue { .. } | SubjectRef::BitstringField { .. } => None,
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
                                let Some(projected_path) = project_path_through_matcher_subject(path, source) else {
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
                ContinuationProvenanceKind::MatcherBody { bindings } => {
                    sets.extend(rebase_caller_groups(provenance, &caller_params, &caller_groups, true));
                    sets.extend(project_matcher_binding_groups(provenance, bindings, &caller_groups));
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

type FnKey = (String, usize);

fn fn_arity(fn_def: &FnDef) -> usize {
    fn_def.clauses.first().map(|clause| clause.params.len()).unwrap_or(0)
}

fn collect_lowerable_fn_keys(items: &[Rc<Item>]) -> HashSet<FnKey> {
    items
        .iter()
        .filter_map(|item| match item.as_ref() {
            Item::Fn(fn_def) if fn_def.extern_abi.is_none() && !fn_def.is_macro => {
                Some((fn_def.name.clone(), fn_arity(fn_def)))
            }
            _ => None,
        })
        .collect()
}

fn collect_public_fn_keys(items: &[Rc<Item>]) -> HashSet<FnKey> {
    items
        .iter()
        .filter_map(|item| match item.as_ref() {
            Item::Fn(fn_def) if fn_def.extern_abi.is_none() && !fn_def.is_macro && !fn_def.is_private => {
                Some((fn_def.name.clone(), fn_arity(fn_def)))
            }
            _ => None,
        })
        .collect()
}

fn select_entry_fn_keys(items: &[Rc<Item>]) -> HashSet<FnKey> {
    items
        .iter()
        .filter_map(|item| match item.as_ref() {
            Item::Fn(fn_def)
                if fn_def.extern_abi.is_none()
                    && !fn_def.is_macro
                    && (fn_def.name == "main" || fn_def.name.starts_with(REPL_ENTRY_PREFIX)) =>
            {
                Some((fn_def.name.clone(), fn_arity(fn_def)))
            }
            _ => None,
        })
        .collect()
}

fn select_initial_root_fn_keys(user_items: &[Rc<Item>], root_entry_keys: Option<&HashSet<FnKey>>) -> HashSet<FnKey> {
    if let Some(root_entry_keys) = root_entry_keys
        && !root_entry_keys.is_empty()
    {
        return root_entry_keys.clone();
    }
    let user_entries = select_entry_fn_keys(user_items);
    if !user_entries.is_empty() {
        return user_entries;
    }
    collect_public_fn_keys(user_items)
}

fn collect_lowerable_fn_defs(items: &[Rc<Item>]) -> HashMap<FnKey, Rc<FnDef>> {
    items
        .iter()
        .filter_map(|item| match item.as_ref() {
            Item::Fn(fn_def) if fn_def.extern_abi.is_none() && !fn_def.is_macro => {
                Some(((fn_def.name.clone(), fn_arity(fn_def)), Rc::new(fn_def.clone())))
            }
            _ => None,
        })
        .collect()
}

fn collect_source_fn_key_by_id(items: &[Rc<Item>], ctx: &LowerCtx) -> HashMap<FnId, FnKey> {
    let mut by_id = HashMap::new();
    for item in items {
        let Item::Fn(fn_def) = item.as_ref() else {
            continue;
        };
        if fn_def.extern_abi.is_some() || fn_def.is_macro {
            continue;
        }
        let key = (fn_def.name.clone(), fn_arity(fn_def));
        let Some(&fn_id) = ctx.fns.get(&key) else {
            continue;
        };
        by_id.insert(fn_id, key);
    }
    by_id
}

fn discover_requested_source_fn_keys(
    function_ids: &[FnIr],
    fn_key_by_id: &HashMap<FnId, FnKey>,
    lowered: &HashSet<FnKey>,
) -> HashSet<FnKey> {
    let mut requested = HashSet::new();
    for fn_ir in function_ids {
        for block in &fn_ir.blocks {
            for Stmt::Let(_, prim) in &block.stmts {
                if let Prim::MakeFnRef(_, target) | Prim::MakeClosure(_, target, _) = prim
                    && let Some(key) = fn_key_by_id.get(target)
                    && !lowered.contains(key)
                {
                    requested.insert(key.clone());
                }
            }
            match &block.terminator {
                Term::Call {
                    callee, continuation, ..
                } => {
                    if let Some(key) = fn_key_by_id.get(callee)
                        && !lowered.contains(key)
                    {
                        requested.insert(key.clone());
                    }
                    if let Some(key) = fn_key_by_id.get(&continuation.fn_id)
                        && !lowered.contains(key)
                    {
                        requested.insert(key.clone());
                    }
                }
                Term::TailCall { callee, .. } => {
                    if let Some(key) = fn_key_by_id.get(callee)
                        && !lowered.contains(key)
                    {
                        requested.insert(key.clone());
                    }
                }
                Term::CallClosure { continuation, .. } => {
                    if let Some(key) = fn_key_by_id.get(&continuation.fn_id)
                        && !lowered.contains(key)
                    {
                        requested.insert(key.clone());
                    }
                }
                Term::ReceiveMatched { clauses, after, .. } => {
                    for clause in clauses {
                        if let Some(key) = fn_key_by_id.get(&clause.body)
                            && !lowered.contains(key)
                        {
                            requested.insert(key.clone());
                        }
                        if let Some(guard) = clause.guard
                            && let Some(key) = fn_key_by_id.get(&guard)
                            && !lowered.contains(key)
                        {
                            requested.insert(key.clone());
                        }
                    }
                    if let Some(after) = after
                        && let Some(key) = fn_key_by_id.get(&after.body)
                        && !lowered.contains(key)
                    {
                        requested.insert(key.clone());
                    }
                }
                Term::Goto(..) | Term::If { .. } | Term::TailCallClosure { .. } | Term::Return(_) | Term::Halt(_) => {}
            }
        }
    }
    requested
}

fn reserve_cached_source_fn_ids(
    compiler: &mut CompilerWorld,
    root_source: ModuleId,
    items: &[Rc<Item>],
    ctx: &mut LowerCtx,
    tel: &dyn Telemetry,
) {
    let mut next_reserved_fn = Some(ctx.mb.next_fn_id());
    let mut next_reserved_extern = None;
    for item in items {
        let Item::Fn(fn_def) = item.as_ref() else {
            continue;
        };
        if fn_def.extern_abi.is_some() || fn_def.is_macro {
            continue;
        }
        let Some(descriptor) = compiler
            .source_fn_group_descriptor(root_source, &fn_def.name, fn_arity(fn_def), tel)
            .expect("compiler source group lookup should succeed after parse")
        else {
            continue;
        };
        let Some(group) = compiler.lowered_group(root_source, &descriptor.source) else {
            continue;
        };
        let Some(max_fn_id) = group.function_ids.iter().map(|id| id.0).max() else {
            continue;
        };
        next_reserved_fn = Some(next_reserved_fn.map_or(max_fn_id + 1, |current: u32| current.max(max_fn_id + 1)));
        if let Some(max_extern_id) = group.extern_decls.iter().map(|decl| decl.id.0).max() {
            next_reserved_extern =
                Some(next_reserved_extern.map_or(max_extern_id + 1, |current: u32| current.max(max_extern_id + 1)));
        }
    }
    if let Some(next_reserved_fn) = next_reserved_fn {
        ctx.mb.advance_next_fn_to(next_reserved_fn);
    }
    if let Some(next_reserved_extern) = next_reserved_extern {
        ctx.next_extern = ctx.next_extern.max(next_reserved_extern);
    }
}

fn assign_compiler_source_root_fn_ids(
    compiler: &mut CompilerWorld,
    root_source: ModuleId,
    items: &[Rc<Item>],
    ctx: &mut LowerCtx,
    tel: &dyn Telemetry,
) -> Result<(), LowerError> {
    let prelude_cutoff = ctx.prelude_fn_id_cutoff;
    let mut next_reserved_fn = prelude_cutoff;
    for item in items {
        let Item::Fn(fn_def) = item.as_ref() else {
            continue;
        };
        if fn_def.extern_abi.is_some() {
            continue;
        }
        let arity = fn_arity(fn_def);
        let Some(descriptor) = compiler
            .source_fn_group_descriptor(root_source, &fn_def.name, arity, tel)
            .map_err(|diagnostic| LowerError::Unsupported {
                span: fn_def.span,
                what: diagnostic.message,
            })?
        else {
            continue;
        };
        let id = FnId(prelude_cutoff + descriptor.id.0);
        ctx.fns.insert((fn_def.name.clone(), arity), id);
        next_reserved_fn = next_reserved_fn.max(id.0 + 1);
        if fn_def.attrs.iter().any(|a| matches!(a, Attribute::Spec(_))) {
            ctx.boundary_fns.insert(id);
        }
    }
    ctx.mb.advance_next_fn_to(next_reserved_fn);
    Ok(())
}

fn merge_lowered_fn_group(ctx: &mut LowerCtx, group: &LoweredFnGroup) {
    for decl in &group.extern_decls {
        if ctx.extern_decls.iter().all(|existing| existing.id != decl.id) {
            ctx.extern_decls.push(decl.clone());
        }
        ctx.externs.insert(decl.fz_name.clone(), decl.id);
    }
    for fn_ir in &group.fns {
        ctx.mb.add_fn(fn_ir.clone());
    }
    if let Some(max_fn_id) = group.function_ids.iter().map(|id| id.0).max() {
        ctx.mb.advance_next_fn_to(max_fn_id + 1);
    }
    ctx.mb.external_call_edges.extend(group.external_call_edges.clone());
    ctx.mb.protocol_call_targets.extend(group.protocol_call_targets.clone());
    ctx.fn_spans.extend(group.fn_spans.clone());
    ctx.stmt_spans.extend(group.stmt_spans.clone());
    ctx.term_spans.extend(group.term_spans.clone());
    ctx.var_meta.extend(group.var_meta.clone());
    ctx.continuation_provenance
        .extend(group.continuation_provenance.clone());
    ctx.extern_wrappers.extend(group.extern_wrappers.clone());
    ctx.external_stubs.extend(group.external_stubs.clone());
    ctx.imported_fn_value_wrappers
        .extend(group.imported_fn_value_wrappers.clone());
    ctx.protocol_stubs.extend(group.protocol_stubs.clone());
}

fn capture_lowered_fn_group(ctx: &LowerCtx, before_fn_count: usize, descriptor: &FnGroupDescriptor) -> LoweredFnGroup {
    let fns = ctx.mb.fn_slice_from(before_fn_count).to_vec();
    let function_ids = fns.iter().map(|fn_ir| fn_ir.id).collect::<Vec<_>>();
    let function_id_set = function_ids.iter().copied().collect::<HashSet<_>>();
    let used_extern_ids = fns
        .iter()
        .flat_map(|fn_ir| fn_ir.blocks.iter())
        .flat_map(|block| block.stmts.iter())
        .filter_map(|stmt| match stmt {
            Stmt::Let(_, Prim::Extern(_, eid, _)) => Some(*eid),
            _ => None,
        })
        .collect::<HashSet<_>>();
    LoweredFnGroup {
        id: descriptor.id,
        source: descriptor.source.clone(),
        function_ids: function_ids.clone(),
        fns,
        extern_decls: ctx
            .extern_decls
            .iter()
            .filter(|decl| {
                used_extern_ids.contains(&decl.id)
                    || function_id_set.contains(ctx.extern_wrappers.get(&decl.id).unwrap_or(&FnId(u32::MAX)))
            })
            .cloned()
            .collect(),
        external_call_edges: ctx
            .mb
            .external_call_edges
            .iter()
            .filter(|edge| function_id_set.contains(&edge.callsite.caller))
            .cloned()
            .collect(),
        protocol_call_targets: ctx
            .mb
            .protocol_call_targets
            .iter()
            .filter(|(fn_id, _)| function_id_set.contains(fn_id))
            .map(|(fn_id, target)| (*fn_id, target.clone()))
            .collect(),
        fn_spans: ctx
            .fn_spans
            .iter()
            .filter(|(fn_id, _)| function_id_set.contains(fn_id))
            .map(|(fn_id, span)| (*fn_id, *span))
            .collect(),
        stmt_spans: ctx
            .stmt_spans
            .iter()
            .filter(|((fn_id, _), _)| function_id_set.contains(fn_id))
            .map(|(key, spans)| (*key, spans.clone()))
            .collect(),
        term_spans: ctx
            .term_spans
            .iter()
            .filter(|((fn_id, _), _)| function_id_set.contains(fn_id))
            .map(|(key, span)| (*key, *span))
            .collect(),
        var_meta: ctx
            .var_meta
            .iter()
            .filter(|((fn_id, _), _)| function_id_set.contains(fn_id))
            .map(|(key, meta)| (*key, meta.clone()))
            .collect(),
        continuation_provenance: ctx
            .continuation_provenance
            .iter()
            .filter(|(fn_id, _)| function_id_set.contains(fn_id))
            .map(|(fn_id, provenance)| (*fn_id, provenance.clone()))
            .collect(),
        extern_wrappers: ctx
            .extern_wrappers
            .iter()
            .filter(|(_, fn_id)| function_id_set.contains(fn_id))
            .map(|(extern_id, fn_id)| (*extern_id, *fn_id))
            .collect(),
        external_stubs: ctx
            .external_stubs
            .iter()
            .filter(|(_, fn_id)| function_id_set.contains(fn_id))
            .map(|(target, fn_id)| (target.clone(), *fn_id))
            .collect(),
        imported_fn_value_wrappers: ctx
            .imported_fn_value_wrappers
            .iter()
            .filter(|(_, fn_id)| function_id_set.contains(fn_id))
            .map(|(target, fn_id)| (target.clone(), *fn_id))
            .collect(),
        protocol_stubs: ctx
            .protocol_stubs
            .iter()
            .filter(|(_, fn_id)| function_id_set.contains(fn_id))
            .map(|(key, fn_id)| (key.clone(), *fn_id))
            .collect(),
    }
}

fn lower_source_fn_group<T: Types<Ty = Ty>>(
    compiler: &mut CompilerWorld,
    root_source: ModuleId,
    descriptor: &FnGroupDescriptor,
    fn_def: &FnDef,
    ctx: &mut LowerCtx,
    t: &mut T,
    tel: &dyn Telemetry,
) -> Result<(), LowerError> {
    let module_key = compiler.module_key_render(root_source);
    if let Some(group) = compiler.lowered_group(root_source, &descriptor.source) {
        merge_lowered_fn_group(ctx, &group);
        tel.execute(
            &["fz", "compiler", "fn_group_cache_hit"],
            &measurements! {
                fn_group_id: descriptor.id.0,
                functions: group.function_ids.len() as u64,
            },
            &metadata! {
                module_key: module_key.clone(),
                owner_module: descriptor.source.owner_module.clone(),
                fn_name: descriptor.qualified_name(),
            },
        );
        return Ok(());
    }

    let before_fn_count = ctx.mb.fn_count();
    lower_fn(ctx, t, fn_def, user_fn_category(fn_def))?;
    let group = capture_lowered_fn_group(ctx, before_fn_count, descriptor);
    tel.execute(
        &["fz", "compiler", "fn_group_lowered"],
        &measurements! {
            fn_group_id: descriptor.id.0,
            functions: group.function_ids.len() as u64,
        },
        &metadata! {
            module_key: module_key,
            owner_module: descriptor.source.owner_module.clone(),
            fn_name: descriptor.qualified_name(),
        },
    );
    compiler.record_lowered_group(root_source, group);
    Ok(())
}

/// Lower a resolved `Program` to its fz-IR `Module`.
///
/// The single public entry. Telemetry is threaded unconditionally so tests and
/// operators observe the same lowering surface; pass `NullTelemetry` to silence
/// it. The atom table built during lowering is folded into `module.atom_names`,
/// so the `Module` is the complete result — there is no second return value.
pub fn lower_program<T: Types<Ty = Ty>>(t: &mut T, prog: &Program, tel: &dyn Telemetry) -> Result<Module, LowerError> {
    let mut compiler = Compiler::new();
    lower_program_with_compiler(compiler.world_mut(), None, t, prog, tel)
}

pub fn lower_program_with_compiler<T: Types<Ty = Ty>>(
    compiler: &mut CompilerWorld,
    root_source: Option<ModuleId>,
    t: &mut T,
    prog: &Program,
    tel: &dyn Telemetry,
) -> Result<Module, LowerError> {
    if let Some(root_source) = root_source
        && !matches!(
            compiler.module(root_source).origin,
            crate::compiler::ModuleOrigin::PrimitivePrelude
        )
    {
        let runtime_entry_keys = compiler.runtime_entry_fn_keys(root_source);
        let root_entry_keys = (!runtime_entry_keys.is_empty()).then_some(&runtime_entry_keys);
        let selected_fn_keys = select_initial_root_fn_keys(&prog.items, root_entry_keys);
        return lower_program_once_with_compiler_selection(
            compiler,
            Some(root_source),
            t,
            prog,
            tel,
            Some(&selected_fn_keys),
        );
    }
    lower_program_once_with_compiler_selection(compiler, None, t, prog, tel, None)
}

fn lower_program_once_with_compiler_selection<T: Types<Ty = Ty>>(
    compiler: &mut CompilerWorld,
    root_source: Option<ModuleId>,
    t: &mut T,
    prog: &Program,
    tel: &dyn Telemetry,
    explicit_selection: Option<&HashSet<FnKey>>,
) -> Result<Module, LowerError> {
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
    let (prelude, prelude_imports) = parse_runtime_prelude(compiler, t, tel);
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
    let prelude_items = &all_items[..runtime_item_count];
    let user_items = &all_items[runtime_item_count..];
    let selected_fn_keys = explicit_selection
        .cloned()
        .unwrap_or_else(|| collect_lowerable_fn_keys(user_items));
    let prelude_fn_defs = collect_lowerable_fn_defs(prelude_items);
    let user_fn_defs = collect_lowerable_fn_defs(user_items);

    // Snapshot user FnDefs (non-extern, non-prelude) by (name, arity) for
    // guard helpers. Receive guards lower helper calls through Matcher
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
                let params: Vec<ExternTy> = fn_def
                    .extern_params
                    .iter()
                    .map(|name| extern_ty_from_name(name).unwrap_or(ExternTy::Any))
                    .collect();
                let (ret, ret_descr) = lower_extern_ret_ty(t, fn_def, &ctx.prelude_type_env)?;
                ctx.extern_decls.push(ExternDecl {
                    id: eid,
                    fz_name: fn_def.name.clone(),
                    symbol: extern_symbol_from_name(&fn_def.name).to_string(),
                    params,
                    variadic: fn_def.variadic,
                    ret,
                    ret_descr,
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
            && selected_fn_keys.contains(&(fn_def.name.clone(), fn_arity(fn_def)))
        {
            lower_fn(&mut ctx, t, fn_def, FnCategory::Prelude)?;
        }
    }
    ctx.prelude_fn_id_cutoff = ctx.mb.next_fn_id();

    if let Some(root_source) = root_source {
        assign_compiler_source_root_fn_ids(compiler, root_source, user_items, &mut ctx, tel)?;
    }

    for item in all_items.iter().skip(runtime_item_count) {
        match item.as_ref() {
            Item::Fn(fn_def) => {
                if fn_def.extern_abi.is_some() {
                    let eid = ExternId(ctx.next_extern);
                    ctx.next_extern += 1;
                    let params: Vec<ExternTy> = fn_def
                        .extern_params
                        .iter()
                        .map(|name| extern_ty_from_name(name).unwrap_or(ExternTy::Any))
                        .collect();
                    let (ret, ret_descr) = lower_extern_ret_ty(t, fn_def, &ctx.prelude_type_env)?;
                    ctx.extern_decls.push(ExternDecl {
                        id: eid,
                        fz_name: fn_def.name.clone(),
                        symbol: extern_symbol_from_name(&fn_def.name).to_string(),
                        params,
                        variadic: fn_def.variadic,
                        ret,
                        ret_descr,
                    });
                    ctx.externs.insert(fn_def.name.clone(), eid);
                } else if !ctx.fns.contains_key(&(fn_def.name.clone(), fn_arity(fn_def))) {
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
    if let Some(root_source) = root_source {
        reserve_cached_source_fn_ids(compiler, root_source, user_items, &mut ctx, tel);
    }

    let fn_key_by_id = collect_source_fn_key_by_id(&all_items, &ctx);
    let mut work_queue = selected_fn_keys.iter().cloned().collect::<VecDeque<_>>();
    let mut lowered_fn_keys = HashSet::new();
    while let Some(fn_key) = work_queue.pop_front() {
        if !lowered_fn_keys.insert(fn_key.clone()) {
            continue;
        }
        let before_fn_count = ctx.mb.fn_count();
        if let Some(fn_def) = user_fn_defs.get(&fn_key) {
            let arity = fn_key.1;
            if let Some(root_source) = root_source
                && let Some(descriptor) = compiler
                    .source_fn_group_descriptor(root_source, &fn_def.name, arity, tel)
                    .expect("compiler source group lookup should succeed after parse")
            {
                lower_source_fn_group(compiler, root_source, &descriptor, fn_def, &mut ctx, t, tel)?;
            } else {
                lower_fn(&mut ctx, t, fn_def, user_fn_category(fn_def))?;
            }
        } else if let Some(fn_def) = prelude_fn_defs.get(&fn_key) {
            lower_fn(&mut ctx, t, fn_def, FnCategory::Prelude)?;
        } else {
            continue;
        }

        let newly_lowered = ctx.mb.fn_slice_from(before_fn_count);
        let requested = discover_requested_source_fn_keys(newly_lowered, &fn_key_by_id, &lowered_fn_keys);
        if let Some(root_source) = root_source {
            for requested_key in &requested {
                if let Some(descriptor) = compiler
                    .source_fn_group_descriptor(root_source, &requested_key.0, requested_key.1, tel)
                    .expect("compiler source group lookup should succeed after parse")
                {
                    tel.execute(
                        &["fz", "compiler", "fn_group_requested"],
                        &measurements! {
                            fn_group_id: descriptor.id.0,
                            loaded_functions: ctx.mb.fn_count() as u64,
                        },
                        &metadata! {
                            module_key: compiler.module_key_render(root_source),
                            owner_module: descriptor.source.owner_module.clone(),
                            fn_name: descriptor.qualified_name(),
                        },
                    );
                }
            }
        }
        for requested_key in requested {
            if !lowered_fn_keys.contains(&requested_key) {
                work_queue.push_back(requested_key);
            }
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
    module.boundary_fns.retain(|fn_id| module.fn_idx.contains_key(fn_id));
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
        if !module.fn_idx.contains_key(&fid) {
            continue;
        }
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
    normalize_continuation_captures_with_telemetry(&mut module, tel);
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
            if !module.fn_idx.contains_key(&fid) {
                continue;
            }
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

/// Parse `extern_ret_tokens` into an ExternTy (wire format) and semantic type
/// (semantic type for the type system).
///
/// `type_env` is consulted for named type references (e.g. `pid`).
pub(super) fn lower_extern_ret_ty<T: Types<Ty = Ty>>(
    t: &mut T,
    fn_def: &FnDef,
    type_env: &ModuleTypeEnv,
) -> Result<(ExternTy, Ty), LowerError> {
    let tokens = &fn_def.extern_ret_tokens.0;

    // Try to resolve via parse_type_expr first (handles named types like `pid`).
    if !tokens.is_empty()
        && let Ok((ty, _)) = parse_type_expr(t, tokens, type_env)
    {
        let wire = ty_to_extern_ty(t, &ty);
        return Ok((wire, ty));
    }

    // Fallback: first-meaningful-token heuristic for tokens that don't
    // parse as a full type expression (e.g. bare `unit` which is not a
    // built-in fz type name).
    let ty = tokens.iter().find_map(|t| match &t.tok {
        Tok::Nil => Some(ExternTy::Unit),
        Tok::True | Tok::False => Some(ExternTy::Any),
        Tok::Ident(n) | Tok::Upper(n) => extern_ty_from_name(n.as_str()),
        _ => None,
    });
    ty.map(|wire| (wire, t.any())).ok_or_else(|| LowerError::Unsupported {
        span: fn_def.name_span,
        what: format!(
            "unrecognised return type in `extern fn {}` (expected any/nil/never/float/pid/…)",
            fn_def.name
        ),
    })
}

/// Derive a coarse C-ABI wire type from a semantic Ty.
///
/// Opaque types erase to Any (they are fz tagged values at runtime).
/// Float-only types get the F64 wire. Nil-only → Unit. Never → Never.
/// Everything else → Any (opaque u64 fz value).
pub(super) fn ty_to_extern_ty<T: Types>(t: &mut T, d: &T::Ty) -> ExternTy {
    if t.is_empty(d) {
        return ExternTy::Never;
    }
    if t.is_nil(d) {
        return ExternTy::Unit;
    }
    if t.is_floating(d) {
        return ExternTy::F64;
    }
    if t.is_integer(d) {
        return ExternTy::I64;
    }
    ExternTy::Any
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
