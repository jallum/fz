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
//! Every `Cont.fn_id` referenced by a `Term::Call` / `Term::CallClosure` /
//! `Term::Receive` must be unique across the whole module — no two
//! call-shaped terminators may share a continuation fn. Continuation
//! provenance, activation facts, and planned call edges all rely on each
//! continuation naming one return edge. `debug_assert_unique_conts` at the
//! end of `lower_program_full` pins the invariant down so a regression
//! in this file (or a future corner case) panics in debug rather than
//! corrupting downstream passes.

#[cfg(test)]
use crate::ast::MatchClause;
use crate::ast::{Attribute, Expr, FnDef, Item, Program, Spanned};
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
use crate::modules::runtime_library::{
    core_prelude_module_sources, interface, prelude_source, root_type_env_from_attrs,
};
use crate::parser::Parser;
use crate::parser::lexer::{Lexer, Tok};
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
use crate::types::{ConcreteTypes, Ty, TypeVarId, Types, check_brand_mint_visibility};
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
    cps_split_receive, finalize_arm, mint_cont_fn, switch_to_cont_fn,
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
fn parse_runtime_prelude<T: Types<Ty = Ty>>(t: &mut T) -> (Program, HashMap<(String, usize), String>) {
    let runtime_fz = prelude_source();
    let (items, attrs) = parse_runtime_source_items(runtime_fz, "runtime.fz");
    let root_types = root_type_env_from_attrs(t, &attrs);
    let prelude_imports = collect_runtime_prelude_imports(&items);
    let mut items = items;
    for (name, source) in core_prelude_module_sources() {
        let (mut module_items, _module_attrs) = parse_runtime_source_items(source, name);
        items.append(&mut module_items);
    }
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
    let mut flat = flatten_modules(t, staged).expect("runtime.fz module flatten error (bug in built-in prelude)");
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

fn parse_runtime_source_items(src: &str, label: &str) -> (Vec<Rc<Item>>, Vec<Attribute>) {
    let toks = Lexer::new(src)
        .tokenize()
        .unwrap_or_else(|_| panic!("{label} lex error (bug in built-in prelude)"));
    Parser::new(toks)
        .parse_prelude()
        .unwrap_or_else(|_| panic!("{label} parse error (bug in built-in prelude)"))
}

fn collect_runtime_prelude_imports(items: &[Rc<Item>]) -> HashMap<(String, usize), String> {
    let mut out = HashMap::new();
    for item in items {
        match item.as_ref() {
            Item::Import {
                path,
                only,
                except,
                span,
            } => collect_runtime_prelude_import(&mut out, path, only.as_deref(), except.as_deref(), *span),
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
    out: &mut HashMap<(String, usize), String>,
    module: &ModuleName,
    only: Option<&[(String, usize)]>,
    except: Option<&[(String, usize)]>,
    span: Span,
) {
    let interface =
        interface(module).unwrap_or_else(|| panic!("runtime.fz imports unknown built-in runtime module `{}`", module));
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

/// Lower a resolved `Program` to its fz-IR `Module`.
///
/// The single public entry. Telemetry is threaded unconditionally so tests and
/// operators observe the same lowering surface; pass `NullTelemetry` to silence
/// it. The atom table built during lowering is folded into `module.atom_names`,
/// so the `Module` is the complete result — there is no second return value.
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
    let (prelude, prelude_imports) = parse_runtime_prelude(t);
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
/// referenced by a `Term::Call` / `Term::CallClosure` / `Term::Receive`
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
                Term::Call { continuation, .. }
                | Term::CallClosure { continuation, .. }
                | Term::Receive { continuation, ident: _ } => continuation.fn_id,
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

pub(super) fn concrete_any_tuple(arity: usize) -> Ty {
    let mut t = ConcreteTypes;
    let elems: Vec<Ty> = (0..arity).map(|_| t.any()).collect();
    t.tuple(&elems)
}

pub(super) fn concrete_any_map() -> Ty {
    let mut t = ConcreteTypes;
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
mod tests {
    use super::*;

    fn lower_src(src: &str) -> Module {
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        lower_program(&mut ConcreteTypes, &prog, &NullTelemetry).expect("lower failed")
    }

    fn lower_flat_src(src: &str) -> (ConcreteTypes, Module) {
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let mut ct = ConcreteTypes;
        let prog = flatten_modules(&mut ct, prog).expect("flatten");
        let module = lower_program(&mut ct, &prog, &NullTelemetry).expect("lower failed");
        (ct, module)
    }

    fn lower_src_with_capture(src: &str) -> (Module, Capture) {
        let tel = ConfiguredTelemetry::new();
        let cap = Capture::new();
        tel.attach(&[], cap.handler());
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let module = lower_program(&mut ConcreteTypes, &prog, &tel).expect("lower failed");
        (module, cap)
    }

    fn lower_src_err(src: &str) -> LowerError {
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        lower_program(&mut ConcreteTypes, &prog, &NullTelemetry).expect_err("expected lower error")
    }

    #[test]
    fn struct_record_type_registers_opaque_underlying_tuple_in_schema_order() {
        let (mut ct, m) = lower_flat_src(
            r#"
defmodule Range do
  defstruct [:first, :last, :step]
  @type t :: %Range{first: integer, last: integer, step: integer}
  fn new(first, last, step), do: %Range{first: first, last: last, step: step}
end
"#,
        );
        let inner = m
            .opaque_inners
            .get("impl-target::Range")
            .expect("Range struct underlying tuple")
            .clone();
        let fields = ct.tuple_projections(&inner, 3);
        let int = ct.int();
        assert!(fields.iter().all(|field| ct.is_equivalent(field, &int)));
    }

    /// fz-qbg.4 — Compile + run a fz program through the JIT and return
    /// captured stdout (joined by newline). Mirrors `ir_codegen::tests::
    /// capture_main`; lets ir_lower-level tests assert end-to-end runtime
    /// correctness rather than just IR shape.
    fn run_and_capture(src: &str) -> String {
        let mut t = ConcreteTypes;
        let graph = linked_runtime_graph_with_telemetry(&mut t, src, &NullTelemetry);
        let entry = graph.module.fn_by_name("main").expect("no main fn").id;
        let compiled =
            compile_planned(&mut t, &graph.module, &graph.module_plan, &NullTelemetry).expect("compile planned");
        let tel = bus::ConfiguredTelemetry::new();
        let dbg = DbgCapture::new();
        tel.attach(&[], dbg.handler());
        let mut rt = Runtime::new(&compiled, 1).with_telemetry(&tel);
        let _ = rt.spawn(entry);
        rt.run_until_idle();
        dbg.lines().join("\n")
    }

    fn count_prims(m: &Module, pred: impl Fn(&Prim) -> bool) -> usize {
        m.fns
            .iter()
            .flat_map(|f| &f.blocks)
            .flat_map(|b| &b.stmts)
            .filter(|stmt| {
                let Stmt::Let(_, prim) = stmt;
                pred(prim)
            })
            .count()
    }

    fn count_prims_in_fn(f: &FnIr, pred: impl Fn(&Prim) -> bool) -> usize {
        f.blocks
            .iter()
            .flat_map(|b| &b.stmts)
            .filter(|stmt| {
                let Stmt::Let(_, prim) = stmt;
                pred(prim)
            })
            .count()
    }

    fn first_make_closure(f: &FnIr) -> (FnId, Vec<Var>) {
        f.blocks
            .iter()
            .flat_map(|block| &block.stmts)
            .find_map(|stmt| {
                let Stmt::Let(_, prim) = stmt;
                if let Prim::MakeClosure(_, lambda_id, captured) = prim {
                    Some((*lambda_id, captured.clone()))
                } else {
                    None
                }
            })
            .expect("expected closure construction")
    }

    fn first_make_fn_ref(f: &FnIr) -> FnId {
        f.blocks
            .iter()
            .flat_map(|block| &block.stmts)
            .find_map(|stmt| {
                let Stmt::Let(_, prim) = stmt;
                if let Prim::MakeFnRef(_, fn_id) = prim {
                    Some(*fn_id)
                } else {
                    None
                }
            })
            .expect("expected fn ref construction")
    }

    #[test]
    fn lower_const_int_returns_in_entry_block() {
        let m = lower_src("fn f() do 42 end");
        let s = format!("{}", m);
        assert!(s.contains("const(42)"), "{}", s);
        assert!(s.contains("return v"), "{}", s);
    }

    #[test]
    fn lower_var_lookup() {
        let m = lower_src("fn id(x), do: x");
        let s = format!("{}", m);
        assert!(s.contains("return v0"), "got:\n{}", s);
    }

    #[test]
    fn lower_binop_add() {
        let m = lower_src("fn add1(x), do: x + 1");
        let s = format!("{}", m);
        assert!(s.contains("const(1)"), "{}", s);
        assert!(s.contains(" + "), "{}", s);
    }

    #[test]
    fn lower_unop_neg() {
        let m = lower_src("fn neg(x), do: -x");
        let s = format!("{}", m);
        assert!(s.contains("- v0"));
    }

    #[test]
    fn lower_tail_call_uses_tail_call() {
        let m = lower_src("fn caller(x), do: callee(x)\nfn callee(y), do: y");
        let s = format!("{}", m);
        assert!(s.contains("tail_call"), "got:\n{}", s);
    }

    #[test]
    fn lower_nontail_call_splits_into_continuation() {
        let m = lower_src("fn caller(x), do: callee(x) + 1\nfn callee(y), do: y");
        let s = format!("{}", m);
        // "call fnN" where N is callee's FnId (shifts with runtime.fz prelude).
        assert!(s.contains("call fn"), "expected explicit call, got:\n{}", s);
        assert!(s.contains("cont(fn"), "expected continuation, got:\n{}", s);
        // Continuation fn is named "k_{FnId}"; FnId shifts with runtime.fz prelude.
        assert!(
            s.contains(" k_") || s.contains("lambda_"),
            "expected continuation fn, got:\n{}",
            s
        );
    }

    #[test]
    fn lower_program_returns_normalized_call_continuation_captures() {
        let (m, cap) = lower_src_with_capture("fn callee(x), do: x\nfn caller(x, y), do: callee(x) + x");
        let caller = m.fn_by_name("caller").expect("caller fn missing");
        let continuation = caller
            .blocks
            .iter()
            .find_map(|b| {
                if let Term::Call { continuation, .. } = &b.terminator {
                    Some(continuation)
                } else {
                    None
                }
            })
            .expect("caller should contain non-tail call");
        let ev = cap
            .find(&["fz", "ir", "capture_norm", "captures_pruned"])
            .into_iter()
            .find(|ev| {
                matches!(
                    ev.metadata.get("producer"),
                    Some(Value::Str(s)) if s.as_ref() == "call_continuation"
                ) && matches!(
                    ev.measurements.get("fn_id"),
                    Some(Value::U64(id)) if *id == continuation.fn_id.0 as u64
                )
            })
            .expect("captures_pruned event");
        assert!(matches!(ev.measurements.get("before_captures"), Some(Value::U64(2))));
        assert!(matches!(ev.measurements.get("after_captures"), Some(Value::U64(1))));
        assert!(matches!(ev.measurements.get("pruned_captures"), Some(Value::U64(1))));

        assert_eq!(
            continuation.captured.len(),
            1,
            "only x is live after callee(x); y must not survive as a continuation capture"
        );

        let k = m.fn_by_id(continuation.fn_id);
        let entry = k.block(k.entry);
        assert_eq!(
            entry.params.len(),
            2,
            "continuation entry should be [result, x], not [result, x, y]"
        );
    }

    #[test]
    fn lower_records_declared_spec_overload_set() {
        let m = lower_src(
            "@spec pick(integer) :: integer\n\
             @spec pick(float) :: float\n\
             fn pick(x), do: x",
        );
        let pick = m.fn_by_name("pick").expect("pick fn missing");
        let specs = m.declared_specs.get(&pick.id).expect("declared specs missing");
        assert_eq!(specs.arrows.len(), 2);
    }

    #[test]
    fn lower_records_source_function_correspondence() {
        let m = lower_src(
            "@spec drop(Enumerable.t(a), integer) :: [a]\n\
             fn drop(_enumerable, _count), do: []",
        );
        let drop = m.fn_by_name("drop").expect("drop fn missing");
        let groups = m
            .function_correspondence
            .get(&drop.id)
            .expect("function correspondence missing");
        assert_eq!(
            groups,
            &vec![StructuralCorrespondenceGroup {
                var: TypeVarId(0),
                occurrences: vec![
                    StructuralOccurrence::Param {
                        param_index: 0,
                        path: vec![StructuralPathStep::NamedArg(0)],
                    },
                    StructuralOccurrence::Result {
                        path: vec![StructuralPathStep::ListElem],
                    },
                ],
            }]
        );
    }

    #[test]
    fn lower_synthesizes_direct_call_continuation_correspondence() {
        let m = lower_src(
            "@spec id(a) :: a\n\
             fn id(x), do: x\n\
             @spec pair_after_id(a) :: {a, a}\n\
             fn pair_after_id(x) do\n\
               y = id(x)\n\
               {x, y}\n\
             end",
        );
        let pair_after_id = m.fn_by_name("pair_after_id").expect("pair_after_id fn missing");
        let continuation = m
            .fns
            .iter()
            .find(|f| f.name.starts_with("k_") && f.owner_module == pair_after_id.owner_module)
            .expect("continuation fn missing");
        let groups = m
            .function_correspondence
            .get(&continuation.id)
            .expect("continuation correspondence missing");
        assert_eq!(
            groups,
            &vec![StructuralCorrespondenceGroup {
                var: TypeVarId(0),
                occurrences: vec![
                    StructuralOccurrence::Param {
                        param_index: 0,
                        path: vec![],
                    },
                    StructuralOccurrence::Param {
                        param_index: 1,
                        path: vec![],
                    },
                    StructuralOccurrence::Result {
                        path: vec![StructuralPathStep::TupleElem(0)],
                    },
                    StructuralOccurrence::Result {
                        path: vec![StructuralPathStep::TupleElem(1)],
                    },
                ],
            }]
        );
    }

    #[test]
    fn lower_persists_direct_call_continuation_provenance() {
        let m = lower_src(
            "@spec id(a) :: a\n\
             fn id(x), do: x\n\
             fn pair_after_id(x) do\n\
               y = id(x)\n\
               {x, y}\n\
             end",
        );
        let pair_after_id = m.fn_by_name("pair_after_id").expect("pair_after_id fn missing");
        let continuation = m
            .fns
            .iter()
            .find(|f| f.name.starts_with("k_") && f.owner_module == pair_after_id.owner_module)
            .expect("continuation fn missing");
        let provenance = m
            .continuation_provenance
            .get(&continuation.id)
            .expect("continuation provenance missing");
        let id = m.fn_by_name("id").expect("id fn missing");
        assert_eq!(
            provenance,
            &ContinuationProvenance {
                caller: pair_after_id.id,
                captured: vec![pair_after_id.block(pair_after_id.entry).params[0]],
                capture_param_offset: 1,
                kind: ContinuationProvenanceKind::DirectCall {
                    callee: id.id,
                    args: vec![pair_after_id.block(pair_after_id.entry).params[0]],
                },
            }
        );
    }

    #[test]
    fn lower_synthesizes_closure_call_continuation_correspondence() {
        let m = lower_src(
            "@spec apply_pair((a) -> b, a) :: {a, b}\n\
             fn apply_pair(f, x) do\n\
               y = f.(x)\n\
               {x, y}\n\
             end",
        );
        let apply_pair = m.fn_by_name("apply_pair").expect("apply_pair fn missing");
        let continuation = m
            .fns
            .iter()
            .find(|f| f.name.starts_with("k_") && f.owner_module == apply_pair.owner_module)
            .expect("continuation fn missing");
        let groups = m
            .function_correspondence
            .get(&continuation.id)
            .expect("continuation correspondence missing");
        assert_eq!(
            groups,
            &vec![
                StructuralCorrespondenceGroup {
                    var: TypeVarId(0),
                    occurrences: vec![
                        StructuralOccurrence::Param {
                            param_index: 0,
                            path: vec![],
                        },
                        StructuralOccurrence::Result {
                            path: vec![StructuralPathStep::TupleElem(1)],
                        },
                    ],
                },
                StructuralCorrespondenceGroup {
                    var: TypeVarId(1),
                    occurrences: vec![
                        StructuralOccurrence::Param {
                            param_index: 2,
                            path: vec![],
                        },
                        StructuralOccurrence::Result {
                            path: vec![StructuralPathStep::TupleElem(0)],
                        },
                    ],
                },
            ]
        );
    }

    #[test]
    fn lower_persists_matcher_body_continuation_provenance() {
        let m = lower_src(
            "fn f(x) do\n\
               case x do\n\
                 [head | tail] -> {head, tail}\n\
               end\n\
             end",
        );
        let continuation = m
            .fns
            .iter()
            .find(|f| f.name.starts_with("case_clause_"))
            .expect("matcher-body continuation missing");
        let provenance = m
            .continuation_provenance
            .get(&continuation.id)
            .expect("matcher-body provenance missing");
        match &provenance.kind {
            ContinuationProvenanceKind::MatcherBody { bindings } => {
                assert_eq!(provenance.capture_param_offset, 0);
                assert_eq!(bindings.len(), 2, "expected head/tail bindings");
            }
            other => panic!("expected matcher-body provenance, got {:?}", other),
        }
    }

    #[test]
    fn lower_if_uses_continuation_fns() {
        // fz-duq.2 — `if` lowers to: outer fn with Term::If + per-arm
        // TailCalls into separate fns (if_then / if_else / optional
        // if_join). The old block-join shape is gone.
        let m = lower_src("fn pos(x), do: if x > 0, do: 1, else: -1");
        let s = format!("{}", m);
        assert!(s.contains("if v"), "expected If terminator: {}", s);
        assert!(s.contains("if_then"), "expected if_then arm fn: {}", s);
        assert!(s.contains("if_else"), "expected if_else arm fn: {}", s);
        assert!(s.contains("tail_call"), "expected TailCall from arm block: {}", s);
        // Tail-position if: no join fn (arms self-Return).
        assert!(
            !s.contains("if_join"),
            "tail-position if should not need a join fn: {}",
            s
        );
    }

    #[test]
    fn fz_84m_repro_a_prints_99() {
        // fz-84m repro A — constant cond + non-tail call in if-arm.
        // Pre-fz-duq.2 panicked at fz_ir.rs:453 (block_mut "unknown
        // block") during IR construction. Now runs end-to-end.
        let out = run_and_capture(
            "fn helper(), do: 7\n\
             fn main() do\n\
               if 1 == 0 do dbg(helper()) else dbg(99) end\n\
             end",
        );
        assert_eq!(out, "99");
    }

    #[test]
    fn fz_84m_repro_b_prints_7_then_99() {
        // fz-84m repro B — tail-call in if-arm + per-callsite narrowing.
        // Pre-fz-duq.2 silently dropped the tail call by overwriting its
        // TailCall terminator with `Goto(join_b, [Var(0)])`, propagating
        // the sentinel as the if's value. Result: exit 0, no stdout.
        let out = run_and_capture(
            "fn helper(), do: 7\n\
             fn pick(n) do if n == 0 do helper() else 99 end end\n\
             fn main() do dbg(pick(0)); dbg(pick(1)) end",
        );
        assert_eq!(out, "7\n99");
    }

    #[test]
    fn lower_case_uses_per_clause_cont_fns() {
        // fz-duq.3 — `case` lowers each clause body into its own cont fn
        // so that internal CPS-splits stay confined.
        let m = lower_src(
            "fn helper(), do: 7\n\
             fn classify(n) do\n\
               case n do\n\
                 0 -> helper()\n\
                 _ -> 99\n\
               end\n\
             end",
        );
        let s = format!("{}", m);
        assert!(s.contains("case_clause_0"), "expected clause cont: {}", s);
        assert!(s.contains("case_clause_1"), "expected clause cont: {}", s);
        // Tail-position case: no join fn.
        assert!(
            !s.contains("case_join"),
            "tail-position case should not need a join fn: {}",
            s
        );
    }

    #[test]
    fn lower_cond_uses_per_arm_cont_fns() {
        // fz-duq.4 — cond arms each lower into their own cont fn so that
        // both test- and body-side CPS-splits stay confined.
        let m = lower_src(
            "fn helper(), do: 7\n\
             fn route(n) do\n\
               cond do\n\
                 n == 0 -> helper()\n\
                 true -> 99\n\
               end\n\
             end",
        );
        let s = format!("{}", m);
        assert!(s.contains("cond_arm_0"), "expected arm cont: {}", s);
        assert!(s.contains("cond_arm_1"), "expected arm cont: {}", s);
        assert!(s.contains("cond_fail"), "expected fail cont: {}", s);
    }

    #[test]
    fn lower_with_uses_continuation_fns() {
        // fz-duq.4 — `with`'s mismatch funnel becomes a continuation fn
        // (`with_fail`) and each else-clause body lives in its own cont fn.
        let m = lower_src(
            "fn f(v) do\n\
               with :ok <- v do\n\
                 1\n\
               else\n\
                 :err -> 2\n\
               end\n\
             end",
        );
        let s = format!("{}", m);
        assert!(s.contains("with_fail"), "expected with_fail cont: {}", s);
        assert!(s.contains("with_else_0"), "expected else clause cont: {}", s);
    }

    #[test]
    fn lower_case_with_call_in_clause_no_panic() {
        // case body with a call (was silently broken via Bug 2 — same
        // class as fz-84m's if repros).
        let _ = lower_src(
            "fn helper(), do: 7\n\
             fn classify(n) do\n\
               case n do\n\
                 0 -> helper()\n\
                 _ -> 99\n\
               end\n\
             end\n\
             fn main() do\n\
               dbg(classify(0))\n\
               dbg(classify(5))\n\
             end",
        );
    }

    #[test]
    fn fz_ben_tuple_pattern_typetest_routes_non_tuple_to_else() {
        // fz-ben — `{:ok, x}` pattern on `:err` (a non-tuple). Pre-fix,
        // lower_pattern_bind for Pattern::Tuple unconditionally emitted
        // `Prim::TupleField(:err, 0)`, which codegen lowered to a
        // `load notrap aligned :err+16` reading heap garbage. With
        // `notrap` swallowing the SIGSEGV, this fixture silently failed
        // (exit 0, no stdout). After fix: a TypeTest gates the
        // projection — non-tuple subjects route to the fail_block, which
        // dispatches the else-clause `:err -> 0`.
        let out = run_and_capture(
            "fn f(v) do\n\
               with {:ok, x} <- v do x else :err -> 0 end\n\
             end\n\
             fn main() do dbg(f(:err)) end",
        );
        assert_eq!(out, "0");
    }

    #[test]
    fn fz_84m_repro_c_prints_7_then_99_no_narrowing() {
        // fz-84m repro C — same bug shape as B but with `n > 0` rather
        // than `n == 0`, so the planner doesn't narrow either arm. Proves
        // the bug was structural in lowering, not type-narrowing driven.
        let out = run_and_capture(
            "fn helper(), do: 7\n\
             fn pick(n) do if n > 0 do helper() else 99 end end\n\
             fn main() do dbg(pick(5)); dbg(pick(0)) end",
        );
        assert_eq!(out, "7\n99");
    }

    #[test]
    fn lower_if_nontail_uses_join_fn() {
        // Non-tail if (used as call argument): all three cont fns minted.
        let m = lower_src(
            "fn id(x), do: x\n\
             fn pick(x), do: id(if x > 0, do: 1, else: -1)",
        );
        let s = format!("{}", m);
        assert!(s.contains("if_then"), "{}", s);
        assert!(s.contains("if_else"), "{}", s);
        assert!(s.contains("if_join"), "expected join fn for non-tail: {}", s);
    }

    #[test]
    fn non_tail_if_call_arm_flows_through_join() {
        // The branch body is not final tail position when the if has a join.
        // Pre-fix, `fun.(head)` returned directly from if_then and skipped the
        // surrounding list construction.
        let out = run_and_capture(
            "fn map_every_list([], _nth, _index, _fun), do: []\n\
             fn map_every_list([head | tail], nth, index, fun) do\n\
               next = if (index % nth) == 0, do: fun.(head), else: head\n\
               [next | map_every_list(tail, nth, index + 1, fun)]\n\
             end\n\
             fn main() do\n\
               dbg(map_every_list([1, 2, 3, 4], 2, 0, fn (x) -> x * 100 end))\n\
             end",
        );
        assert_eq!(out, "[100, 2, 300, 4]");
    }

    #[test]
    fn non_tail_case_call_arm_flows_through_join() {
        let out = run_and_capture(
            "fn pick(x, fun) do\n\
               next = case x do\n\
                 0 -> fun.(x)\n\
                 _ -> x\n\
               end\n\
               [next]\n\
             end\n\
             fn main() do dbg(pick(0, fn (x) -> x + 1 end)) end",
        );
        assert_eq!(out, "[1]");
    }

    #[test]
    fn non_tail_cond_call_arm_flows_through_join() {
        let out = run_and_capture(
            "fn pick(x, fun) do\n\
               next = cond do\n\
                 x == 0 -> fun.(x)\n\
                 true -> x\n\
               end\n\
               [next]\n\
             end\n\
             fn main() do dbg(pick(0, fn (x) -> x + 1 end)) end",
        );
        assert_eq!(out, "[1]");
    }

    #[test]
    fn lower_block_evaluates_last_expr() {
        let m = lower_src("fn b() do\n  1\n  2\n  3\nend");
        let s = format!("{}", m);
        assert!(s.contains("const(1)"), "{}", s);
        assert!(s.contains("const(2)"), "{}", s);
        assert!(s.contains("const(3)"), "{}", s);
        assert!(s.contains("return v"), "{}", s);
    }

    #[test]
    fn lower_list_makes_list_prim() {
        let m = lower_src("fn l(), do: [1, 2]");
        let s = format!("{}", m);
        assert!(s.contains("list(["), "{}", s);
        assert!(!s.contains("list([] |"), "no-tail list shouldn't have | sep: {}", s);
    }

    #[test]
    fn lower_list_with_tail() {
        let m = lower_src("fn l(t), do: [1 | t]");
        let s = format!("{}", m);
        assert!(s.contains("] | v0)"), "expected list with v0 (param t) tail: {}", s);
    }

    #[test]
    fn lower_tuple_makes_tuple_prim() {
        let m = lower_src("fn t(), do: {1, :ok}");
        let s = format!("{}", m);
        assert!(s.contains("tuple(["), "{}", s);
    }

    #[test]
    fn lower_tuple_pattern_projects_fields() {
        let m = lower_src("fn first({a, b}), do: a");
        let s = format!("{}", m);
        assert!(s.contains("tuple_field(v0, 0)"), "got:\n{}", s);
        assert!(s.contains("tuple_field(v0, 1)"), "got:\n{}", s);
    }

    #[test]
    fn lower_match_expr_binds_var() {
        let m = lower_src("fn m(p) do\n  x = p\n  x\nend");
        let s = format!("{}", m);
        assert!(s.contains("return v0"), "got:\n{}", s);
    }

    /// fz-fyq.3 — `collect_diagnostics` filters `unreachable-arm` to
    /// `BranchOrigin::User`. A destructure (`{a,b} = ...`) and a fn-clause
    /// dispatch both synthesize Ifs the planner can prove dead-edged; neither
    /// should warn. User-authored Ifs whose dead branch the planner can
    /// prove (here: `if true do A else B` where the else is structurally
    /// unreachable) still do.
    #[test]
    fn unreachable_arm_silenced_on_synthesized_ifs() {
        let m = lower_src(concat!(
            "fn fst(0), do: :zero\n",
            "fn fst(_), do: :other\n",
            "fn main() do\n",
            "  {a, b} = {1, 2}\n",
            "  fst(a + b)\n",
            "end\n",
        ));
        let mut ct = ConcreteTypes;
        let mt = plan_module(&mut ct, &m, &NullTelemetry);
        let diags = collect_diagnostics(&mut ct, &m, &mt, &NullTelemetry);
        let unreachable: Vec<_> = diags
            .as_slice()
            .iter()
            .filter(|d| d.code == codes::TYPE_UNREACHABLE_ARM)
            .collect();
        assert!(
            unreachable.is_empty(),
            "synthesized dispatch Ifs must not warn; got {:?}",
            unreachable,
        );
    }

    /// fz-bsx.5 — the dead-binop ("always false") diagnostic is observed
    /// through the telemetry bus ([fz, diag, warning] carrying
    /// type/dead-binop), per the project's telemetry-over-stderr policy.
    #[test]
    fn dead_binop_diagnostic_observable_via_telemetry() {
        let m = lower_src("fn main() do\n  dbg(1 == :ok)\nend\n");
        let mut ct = ConcreteTypes;
        let mt = plan_module(&mut ct, &m, &NullTelemetry);
        let diags = collect_diagnostics(&mut ct, &m, &mt, &NullTelemetry);

        let tel = ConfiguredTelemetry::new();
        let cap = Capture::new();
        tel.attach(&["fz", "diag"], cap.handler());
        emit_through(&tel, None, diags.as_slice());

        assert!(
            cap.count(&["fz", "diag", "warning"]) >= 1,
            "dead-binop warning must surface on the telemetry bus",
        );
        assert!(
            diags.as_slice().iter().any(|d| d.code == codes::TYPE_DEAD_BINOP),
            "the surfaced warning carries the type/dead-binop code",
        );
    }

    #[test]
    fn generated_dead_binop_diagnostic_is_not_rendered() {
        let mut f = FnBuilder::new(FnId(0), "generated");
        let entry = f.block(vec![]);
        let one = f.let_(entry, Prim::Const(Const::Int(1)));
        let atom = f.let_(entry, Prim::Const(Const::Atom(0)));
        let eq = f.let_(entry, Prim::BinOp(BinOp::Eq, one, atom));
        f.set_terminator(entry, Term::Return(eq));
        let mut mb = ModuleBuilder::new();
        mb.add_fn(f.build());
        let m = mb.build();

        let mut ct = ConcreteTypes;
        let mt = plan_module(&mut ct, &m, &NullTelemetry);
        let diags = collect_diagnostics(&mut ct, &m, &mt, &NullTelemetry);

        assert!(
            !diags.as_slice().iter().any(|d| d.code == codes::TYPE_DEAD_BINOP),
            "generated comparisons without source spans must not render dead-binop diagnostics",
        );
    }

    /// `ModulePlan::dead_branches` publishes only branch facts that are safe
    /// for shared-body mutation. Narrow recursive list-dispatch facts stay on
    /// the individual `SpecPlan`, because folding the canonical body with them
    /// would make the body invalid for wider keys.
    #[test]
    fn dead_branches_published_for_destructure_and_recursive_list_dispatch() {
        // Irrefutable destructure on a known-2-tuple — the planner proves
        // the synthesized fail edge dead under the one live spec.
        let m = lower_src("fn main() do\n  {a, b} = {1, 2}\n  a + b\nend\n");
        let mut ct = ConcreteTypes;
        let mt = plan_module(&mut ct, &m, &NullTelemetry);
        assert!(
            mt.dead_branches.values().any(|d| matches!(d, DeadBranch::Else)),
            "expected an Else dead branch for {{a,b}} = {{1,2}}; got {:?}",
            mt.dead_branches,
        );

        // Recursive sum — with `[]` and `[_ | _]` modeled as disjoint
        // shapes, clause-dispatch branches can be proven dead per
        // specialized dispatch block.
        let m2 = lower_src(concat!(
            "fn sum([]), do: 0\n",
            "fn sum([h | t]), do: h + sum(t)\n",
            "fn main(), do: sum([1, 2, 3])\n",
        ));
        let mt2 = plan_module(&mut ct, &m2, &NullTelemetry);
        let sum_fid = m2.fn_by_name("sum").expect("sum exists").id;
        assert!(
            mt2.specs
                .iter()
                .any(|(key, spec)| key.fn_id == sum_fid && !spec.dead_branches.is_empty()),
            "sum/1 should keep per-spec dead clause-dispatch facts with explicit list shapes; got {:?}",
            mt2.specs
                .iter()
                .filter(|(key, _)| key.fn_id == sum_fid)
                .map(|(key, spec)| (key, &spec.dead_branches))
                .collect::<Vec<_>>(),
        );
    }

    /// fz-fyq.1 — every lowering path that synthesizes a `Term::If` tags it
    /// with the right `BranchOrigin`. Cover one source program that exercises
    /// each origin and assert the right set appears in the lowered module.
    #[test]
    fn branch_origin_tagged_per_lowering_path() {
        let m = lower_src(concat!(
            // ParamGuard: typed param synthesizes a TypeTest If.
            "fn f(x :: integer), do: x\n",
            // ClauseDispatch (multi-clause): two clauses on a literal.
            "fn g(0), do: :zero\n",
            "fn g(_), do: :other\n",
            // PatternBind: `{a, b} = ...` synthesizes Ifs that check tuple arity.
            "fn h() do\n",
            "  {a, b} = {1, 2}\n",
            "  a + b\n",
            "end\n",
            // User: hand-written `if`.
            "fn i(n), do: if n > 0, do: 1, else: 0\n",
        ));
        let mut seen: HashSet<BranchOrigin> = HashSet::new();
        for f in &m.fns {
            for b in &f.blocks {
                if let Term::If { origin, .. } = &b.terminator {
                    seen.insert(*origin);
                }
            }
        }
        assert!(seen.contains(&BranchOrigin::User), "missing User: {:?}", seen);
        assert!(
            seen.contains(&BranchOrigin::PatternBind),
            "missing PatternBind: {:?}",
            seen,
        );
        assert!(
            seen.contains(&BranchOrigin::ClauseDispatch),
            "missing ClauseDispatch: {:?}",
            seen,
        );
        assert!(
            seen.contains(&BranchOrigin::ParamGuard),
            "missing ParamGuard: {:?}",
            seen,
        );
    }

    #[test]
    fn multi_clause_dispatch_lowers_matcher_inline() {
        // fz-puj.52.7 — multi-clause fns lower the Matcher inline
        // into the user fn again so dispatch does not become a separate
        // spec-producing matcher fn.
        let m = lower_src("fn fact(0), do: 1\nfn fact(n), do: n * fact(n - 1)");
        let s = format!("{}", m);
        assert!(!s.contains("fact_matcher_"), "did not expect fact_matcher_N fn: {}", s);
        assert!(s.contains("if v"), "expected pattern test If: {}", s);
        assert!(s.contains("halt v"), "expected halt in fail block:\n{}", s);
        assert!(s.contains(":atom_"), "expected interned atom in fail block:\n{}", s);
    }

    #[test]
    fn lower_lambda_creates_separate_fn_and_closure() {
        let m = lower_src("fn mk(x), do: fn(y) -> x + y end");
        let s = format!("{}", m);
        assert!(s.contains("closure(fn"), "expected closure prim, got:\n{}", s);
        assert!(s.contains("lambda_"), "expected lambda fn name: {}", s);
        assert!(
            m.fns.len() >= 2,
            "expected ≥2 fns (mk + lambda + prelude), got {}",
            m.fns.len()
        );
        assert!(m.fns.iter().any(|f| f.name == "mk"), "expected 'mk' fn");
        assert!(
            m.fns.iter().any(|f| f.name.starts_with("lambda_")),
            "expected lambda fn"
        );
    }

    #[test]
    fn lower_named_fn_ref_emits_thin_fn_ref_prim() {
        let m = lower_src("fn id(x), do: x\nfn main(), do: &id/1");
        let main = m.fn_by_name("main").expect("main fn missing");
        let fn_id = first_make_fn_ref(main);

        assert_eq!(m.fn_by_id(fn_id).name, "id");
        assert_eq!(count_prims_in_fn(main, |prim| matches!(prim, Prim::MakeClosure(..))), 0);
    }

    #[test]
    fn lower_bare_top_level_fn_value_emits_thin_fn_ref_prim() {
        let m = lower_src("fn id(x), do: x\nfn main(), do: id");
        let main = m.fn_by_name("main").expect("main fn missing");
        let fn_id = first_make_fn_ref(main);

        assert_eq!(m.fn_by_id(fn_id).name, "id");
        assert_eq!(count_prims_in_fn(main, |prim| matches!(prim, Prim::MakeClosure(..))), 0);
    }

    #[test]
    fn lower_lambda_captures_only_referenced_outer_names() {
        let m = lower_src("fn mk(x, y), do: fn(z) -> x + z end");
        let mk = m.fn_by_name("mk").expect("mk fn missing");
        let (lambda_id, captured) = first_make_closure(mk);

        assert_eq!(
            captured.len(),
            1,
            "lambda body reads x but not y, so only x should be captured"
        );

        let lambda = m.fn_by_id(lambda_id);
        assert_eq!(
            lambda.block(lambda.entry).params.len(),
            2,
            "entry params should be [captured x, lambda arg z]"
        );
    }

    #[test]
    fn lower_lambda_with_no_outer_reads_has_no_captures() {
        let m = lower_src("fn mk(x), do: fn(y) -> y + 1 end");
        let mk = m.fn_by_name("mk").expect("mk fn missing");
        let lambda_id = first_make_fn_ref(mk);

        assert_eq!(
            count_prims_in_fn(mk, |prim| matches!(prim, Prim::MakeClosure(..))),
            0,
            "lambda body reads no outer names, so it should lower as a thin fn ref"
        );

        let lambda = m.fn_by_id(lambda_id);
        assert_eq!(
            lambda.block(lambda.entry).params.len(),
            1,
            "entry params should contain only lambda arg y"
        );
    }

    /// `dbg(x)` routes through the runtime.fz prelude import to the
    /// core-prelude `Kernel.dbg/1` implementation instead of exposing raw
    /// externs from the root prelude.
    #[test]
    fn print_call_routes_through_runtime_fz_wrapper() {
        let m = lower_src("fn p(), do: dbg(1)");
        let print = m
            .fns
            .iter()
            .find(|f| f.name == "Kernel.dbg" && f.block(f.entry).params.len() == 1)
            .expect("Kernel.dbg/1 prelude fn missing");
        let p = m.fn_by_name("p").expect("p fn missing");
        let Term::TailCall { callee, .. } = p.block(p.entry).terminator else {
            panic!("expected p to tail-call print/1");
        };
        assert_eq!(callee, print.id);
    }

    /// `spawn(x)` routes through the runtime.fz prelude import to
    /// `Kernel.spawn/1`, whose implementation owns the raw extern.
    #[test]
    fn spawn_callsite_routes_through_runtime_fz_wrapper() {
        let m = lower_src("fn child(), do: 0\nfn p() do spawn(child) end");
        assert!(
            !m.fns.iter().any(|f| f.name == "fz_spawn_thunk"),
            "spawn must not synthesize fz_spawn_thunk; fns: {:?}",
            m.fns.iter().map(|f| &f.name).collect::<Vec<_>>()
        );
        let spawn = m
            .fns
            .iter()
            .find(|f| f.name == "Kernel.spawn" && f.block(f.entry).params.len() == 1)
            .expect("Kernel.spawn/1 prelude fn missing");
        let p = m.fn_by_name("p").expect("p fn missing");
        let entry = p.block(p.entry);
        let Term::TailCall { callee, .. } = entry.terminator else {
            panic!("expected p to tail-call spawn/1, got {:?}", entry.terminator);
        };
        assert_eq!(callee, spawn.id);
        assert!(
            spawn.blocks.iter().any(|b| b.stmts.iter().any(|stmt| {
                let Stmt::Let(_, prim) = stmt;
                matches!(prim, Prim::Extern(_, _, _))
            })),
            "Kernel.spawn/1 must call its runtime extern"
        );
    }

    #[test]
    fn spawn_wrapper_extern_keeps_intrinsic_boundary_identity() {
        let m = lower_src("fn child(), do: nil\nfn main() do spawn(child) end");
        let spawn = m
            .fns
            .iter()
            .find(|f| f.name == "Kernel.spawn" && f.block(f.entry).params.len() == 1)
            .expect("Kernel.spawn/1 prelude fn missing");
        let (ident, args) = spawn
            .blocks
            .iter()
            .flat_map(|block| block.stmts.iter())
            .find_map(|stmt| match stmt {
                Stmt::Let(_, Prim::Extern(ident, _, args)) => Some((ident, args.as_slice())),
                _ => None,
            })
            .expect("Kernel.spawn/1 must contain a runtime extern");

        assert_eq!(args.len(), 1, "spawn wrapper should pass exactly one callable");
        assert_ne!(
            ident.span(),
            Span::DUMMY,
            "runtime extern boundary must carry an intrinsic callsite span"
        );
    }

    #[test]
    fn lambda_tail_receive_does_not_terminate_enclosing_spawn_call() {
        let m = lower_src("fn p(parent) do\nspawn(fn () -> send(parent, receive()) end)\nend");
        let p = m.fn_by_name("p").expect("p fn missing");
        let entry = p.block(p.entry);
        let spawn = m
            .fns
            .iter()
            .find(|f| f.name == "Kernel.spawn" && f.block(f.entry).params.len() == 1)
            .expect("Kernel.spawn/1 prelude fn missing");
        let callee = match entry.terminator {
            Term::TailCall { callee, .. } => callee,
            ref other => panic!("expected enclosing fn to tail-call spawn/1, got {:?}", other),
        };
        assert_eq!(callee, spawn.id);
        assert!(
            !p.blocks.iter().any(|b| matches!(b.terminator, Term::Receive { .. })),
            "lambda lowering must not leak tail-receive termination into the caller"
        );
    }

    /// `spawn/2` follows the same prelude-import path as `spawn/1`.
    #[test]
    fn spawn2_routes_through_runtime_fz_wrapper() {
        let m = lower_src("fn child(), do: 0\nfn p() do spawn(child, 4096) end");
        assert!(
            !m.fns.iter().any(|f| f.name == "fz_spawn_thunk"),
            "spawn/2 must not synthesize fz_spawn_thunk"
        );
        let spawn = m
            .fns
            .iter()
            .find(|f| f.name == "Kernel.spawn" && f.block(f.entry).params.len() == 2)
            .expect("Kernel.spawn/2 prelude fn missing");
        let p = m.fn_by_name("p").expect("p fn missing");
        let entry = p.block(p.entry);
        let Term::TailCall { callee, .. } = entry.terminator else {
            panic!("expected p to tail-call spawn/2, got {:?}", entry.terminator);
        };
        assert_eq!(callee, spawn.id);
        assert!(
            spawn.blocks.iter().any(|b| b.stmts.iter().any(|stmt| {
                let Stmt::Let(_, prim) = stmt;
                matches!(prim, Prim::Extern(_, _, _))
            })),
            "Kernel.spawn/2 must call its runtime extern"
        );
    }

    /// The lowerer no longer synthesizes fz_spawn_thunk for any program.
    #[test]
    fn spawn_free_program_has_no_compiler_spawn_thunk() {
        let m = lower_src("fn p(), do: 0");
        assert!(
            !m.fns.iter().any(|f| f.name == "fz_spawn_thunk"),
            "expected no compiler-synthesized fz_spawn_thunk"
        );
    }

    #[test]
    fn unbound_var_returns_lower_error() {
        let err = lower_src_err("fn f(), do: missing");
        assert!(matches!(err, LowerError::Unbound { .. }));
    }

    /// .21 step 3: lower errors carry a real Span of the offending node,
    /// not Span::DUMMY.
    #[test]
    fn unbound_var_diag_has_real_span() {
        let err = lower_src_err("fn f(), do: missing");
        let d = err.to_diagnostic();
        assert_ne!(
            d.primary.span,
            Span::DUMMY,
            "lower diagnostic should carry the unbound Var's span"
        );
        assert_eq!(d.code, codes::LOWER_UNBOUND);
    }

    #[test]
    fn unbound_callee_returns_lower_error() {
        let err = lower_src_err("fn f(), do: nonesuch(1)");
        assert!(matches!(err, LowerError::Unbound { .. }));
    }

    #[test]
    fn empty_case_returns_unsupported() {
        let err = lower_src_err("fn f() do case 1 do end end");
        assert!(matches!(err, LowerError::Unsupported { .. }));
    }

    #[test]
    fn map_lowers_to_make_map() {
        let m = lower_src("fn m(), do: %{k: 1}");
        let s = format!("{}", m);
        assert!(s.contains("map({"), "got:\n{}", s);
    }

    #[test]
    fn map_update_lowers() {
        let m = lower_src("fn u(m), do: %{m | k: 2}");
        let s = format!("{}", m);
        assert!(s.contains("map_update("), "got:\n{}", s);
    }

    #[test]
    fn index_lowers_to_map_get() {
        let m = lower_src("fn g(m), do: m[:k]");
        let s = format!("{}", m);
        assert!(s.contains("map_get("), "got:\n{}", s);
    }

    #[test]
    fn bitstring_expr_lowers() {
        let m = lower_src("fn b(), do: << 0xA5 >>");
        let s = format!("{}", m);
        assert!(s.contains("bitstring(["), "got:\n{}", s);
    }

    #[test]
    fn case_lowers_matcher_inline() {
        // fz-puj.52.7 — case sites lower the Matcher inline so the
        // planner does not see a case_matcher_N function boundary.
        let m = lower_src(
            r#"
fn c(x) do
  case x do
    0 -> :zero
    _ -> :other
  end
end
"#,
        );
        let s = format!("{}", m);
        assert!(
            !s.contains("case_matcher_"),
            "did not expect case_matcher_N fn in module dump: {}",
            s
        );
        assert!(s.contains("if v"), "expected if for inline pattern check: {}", s);
        assert!(s.contains("tail_call"), "expected tail_call to clause cont fns: {}", s);
    }

    #[test]
    fn cond_lowers() {
        // cond is parsed; lowering should emit If terminators.
        let m = lower_src(
            r#"
fn c(x) do
  cond do
    x > 0 -> :pos
    true -> :nonpos
  end
end
"#,
        );
        let s = format!("{}", m);
        assert!(s.contains("if v"), "got:\n{}", s);
    }

    #[test]
    fn with_simple_lowers() {
        let m = lower_src(
            r#"
fn w() do
  with {:ok, a} <- {:ok, 1}, do: a
end
"#,
        );
        let s = format!("{}", m);
        assert!(s.contains("tuple_field"), "expected pattern projection: {}", s);
    }

    #[test]
    fn map_pattern_uses_map_get_check() {
        let m = lower_src("fn first(%{name: n}), do: n");
        let s = format!("{}", m);
        assert!(s.contains("map_get("), "got:\n{}", s);
    }

    #[test]
    fn inline_matcher_reuses_tuple_subject_across_test_guard_and_binding() {
        let m = lower_src(
            "fn positive(n), do: n > 0
             fn classify(t) do
               case t do
                 {:ok, x} when positive(x) -> x + x
                 _ -> 0
               end
             end",
        );

        let classify = m.fn_by_name("classify").expect("classify fn");
        let field_1_count = count_prims_in_fn(classify, |prim| matches!(prim, Prim::TupleField(_, 1)));
        assert_eq!(
            field_1_count, 1,
            "tuple field used by guard and binding should materialize once:\n{}",
            m
        );
    }

    #[test]
    fn inline_matcher_reuses_list_head_across_guard_and_binding() {
        let m = lower_src(
            "fn positive(n), do: n > 0
             fn classify(xs) do
               case xs do
                 [h | _] when positive(h) -> h + h
                 _ -> 0
               end
             end",
        );

        let classify = m.fn_by_name("classify").expect("classify fn");
        let head_count = count_prims_in_fn(classify, |prim| matches!(prim, Prim::ListHead(_)));
        assert_eq!(
            head_count, 1,
            "list head used by guard and binding should materialize once:\n{}",
            m
        );
    }

    #[test]
    fn inline_matcher_reuses_map_value_across_guard_and_binding() {
        let m = lower_src(
            "fn positive(n), do: n > 0
             fn classify(m) do
               case m do
                 %{id: x} when positive(x) -> x + x
                 _ -> 0
               end
             end",
        );

        let map_get_count = count_prims(&m, |prim| matches!(prim, Prim::MatcherMapGet(_, _)));
        assert_eq!(
            map_get_count, 1,
            "map value used by guard and binding should materialize once:\n{}",
            m
        );
    }

    #[test]
    fn bitstring_pattern_lowers_to_per_field_reads() {
        let m = lower_src("fn p(<<x::8>>), do: x");
        let s = format!("{}", m);
        assert!(s.contains("bit_reader_init("), "got:\n{}", s);
        assert!(s.contains("bit_read_field("), "got:\n{}", s);
        assert!(s.contains("bit_reader_done("), "got:\n{}", s);
    }

    #[test]
    fn quote_returns_post_expansion_node() {
        // Skip macro expansion to surface the leftover-quote error path.
        let err = lower_src_err("fn f(), do: quote do: 1");
        assert!(matches!(err, LowerError::PostExpansionNode { .. }));
    }

    /// Span round-trip: AST nodes parsed by the parser carry non-DUMMY spans
    /// that slice back to their source lexemes.
    #[test]
    fn parser_attaches_real_spans_to_expressions() {
        let src = "fn ident(x), do: x + 1";
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let Item::Fn(def) = &*prog.items[0] else {
            panic!("expected fn")
        };
        // The body `x + 1` is a BinOp; its span should be non-DUMMY and
        // slice to the operator-bracketed substring.
        let body = &def.clauses[0].body;
        assert!(!body.span.is_dummy());
        let lexeme = &src[body.span.start as usize..body.span.end as usize];
        assert!(
            lexeme.contains('+'),
            "body span should cover the binop expression, got {:?}",
            lexeme
        );
    }

    /// FnDef.name_span pinpoints the source name token (not the whole def).
    #[test]
    fn parser_records_fn_name_span() {
        let src = "fn foobar(), do: 0";
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let Item::Fn(def) = &*prog.items[0] else {
            panic!("expected fn")
        };
        let name_text = &src[def.name_span.start as usize..def.name_span.end as usize];
        assert_eq!(name_text, "foobar");
    }

    // ----- .20.4: SourceInfo side-tables -----

    /// Pattern-bound parameters record their name + binding span in
    /// `Module.source`. The ticket's canonical test: lower a `double(x)`
    /// function and verify the param's Var → "x", span → the `x` token.
    #[test]
    fn pattern_var_records_source_name_and_span() {
        let src = "fn double(x), do: x * 2";
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let m = lower_program(&mut ConcreteTypes, &prog, &NullTelemetry).expect("lower");
        let f = m.fn_by_name("double").unwrap();
        let param = f.blocks[0].params[0];
        assert_eq!(m.source.var_name_of(param), Some("x"));
        let sp = m.source.var_span_of(param);
        assert!(!sp.is_dummy());
        let txt = &src[sp.start as usize..sp.end as usize];
        assert_eq!(txt, "x");
    }

    /// Every top-level fn gets its source span recorded under
    /// `fn_span[fn_id.0]`.
    #[test]
    fn fn_span_records_def_position() {
        let src = "fn alpha(), do: 1\nfn beta(), do: 2";
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let m = lower_program(&mut ConcreteTypes, &prog, &NullTelemetry).expect("lower");
        let beta = m.fn_by_name("beta").unwrap();
        let sp = m.source.fn_span_of(beta.id);
        let txt = &src[sp.start as usize..sp.end as usize];
        assert!(txt.starts_with("fn beta"));
    }

    /// CPS continuations created when a non-tail Call splits use the
    /// originating call expression's span as their `fn_span`, so a
    /// diagnostic on the continuation can point at where the work
    /// originated in source.
    #[test]
    fn continuation_fn_span_points_at_originating_call() {
        // `callee(x) + 1` forces a non-tail Call -> CPS split.
        let src = "fn callee(y), do: y\nfn caller(x), do: callee(x) + 1";
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let m = lower_program(&mut ConcreteTypes, &prog, &NullTelemetry).expect("lower");
        let caller = m.fn_by_name("caller").unwrap();
        // The continuation fn is the one whose name starts with "k_".
        // Filter out continuations from the runtime.fz prelude (e.g.
        // Utf8.from_bytes also CPS-splits) by checking FnCategory.
        let k = m
            .fns
            .iter()
            .find(|f| f.name.starts_with("k_") && f.category == FnCategory::CpsCont && f.id.0 >= caller.id.0)
            .expect("expected a continuation fn in user code");
        let cont_span = m.source.fn_span_of(k.id);
        assert!(!cont_span.is_dummy());
        // The originating call is `callee(x)` inside `caller`'s body.
        // The continuation's fn_span must be inside caller's source range.
        let caller_span = m.source.fn_span_of(caller.id);
        assert!(
            cont_span.start >= caller_span.start && cont_span.end <= caller_span.end,
            "continuation span {:?} should lie within caller's range {:?}",
            cont_span,
            caller_span
        );
        let txt = &src[cont_span.start as usize..cont_span.end as usize];
        assert!(
            txt.contains("callee"),
            "continuation span should cover the originating call, got {:?}",
            txt
        );
    }

    /// Compiler-introduced Vars (constants, tuple projections, etc.)
    /// keep their source-expression span on `var_span` and an empty
    /// name on `var_name`. .20.8's diagnostic renderer uses the empty-
    /// name signal to render "this value" instead of "`<name>`".
    #[test]
    fn temp_var_records_span_and_empty_name() {
        // `x + 1` produces a Const(1) Var whose source position is the
        // literal `1` in the body.
        let src = "fn add_one(x), do: x + 1";
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let m = lower_program(&mut ConcreteTypes, &prog, &NullTelemetry).expect("lower");
        let f = m.fn_by_name("add_one").unwrap();
        // Find a Var bound to `Const(Int(1))`.
        let mut const1_var: Option<Var> = None;
        for blk in &f.blocks {
            for s in &blk.stmts {
                let Stmt::Let(v, prim) = s;
                if matches!(prim, Prim::Const(Const::Int(1))) {
                    const1_var = Some(*v);
                }
            }
        }
        let v = const1_var.expect("Const(1) Var");
        // No source name on this temp.
        assert_eq!(m.source.var_name_of(v), None);
        // But its span points at the `1` literal.
        let sp = m.source.var_span_of(v);
        let txt = &src[sp.start as usize..sp.end as usize];
        assert_eq!(txt, "1");
    }

    #[test]
    fn self_recursive_fn_has_back_edge() {
        // fz-qbg.2: with multi-clause body cont fns, prelude multi-clause
        // fns (`print`) contribute TailCalls to their per-clause
        // cont fns earlier in module order. Look up `loop` specifically
        // rather than the first TailCall anywhere.
        let m = lower_src("fn loop(n), do: loop(n)");
        let loop_fn = m.fn_by_name("loop").expect("loop fn missing");
        let (callee, is_back_edge) = loop_fn
            .blocks
            .iter()
            .find_map(|b| {
                if let Term::TailCall {
                    ident: _,
                    callee,
                    is_back_edge,
                    ..
                } = &b.terminator
                {
                    Some((*callee, *is_back_edge))
                } else {
                    None
                }
            })
            .expect("no TailCall in loop");
        assert!(is_back_edge, "self-recursion must be a back-edge; callee={:?}", callee);
    }

    #[test]
    fn non_recursive_call_is_not_back_edge() {
        let m = lower_src("fn id(x), do: x\nfn main(), do: id(1)");
        // Find the TailCall from main to id.
        let mut found = false;
        for f in &m.fns {
            if f.name == "main" {
                for b in &f.blocks {
                    if let Term::TailCall { is_back_edge, .. } = &b.terminator {
                        assert!(!is_back_edge, "non-recursive call must NOT be back-edge");
                        found = true;
                    }
                }
            }
        }
        assert!(found, "no TailCall from main");
    }

    #[test]
    fn extern_fn_registers_in_module_externs() {
        let toks = Lexer::new("extern \"C\" fn fz_nop(any) :: nil\nfn main() do fz_nop(1) end\n")
            .tokenize()
            .expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let module = lower_program(&mut ConcreteTypes, &prog, &NullTelemetry).expect("lower");
        // fz_nop is at the end (user externs follow runtime.fz externs).
        let nop = module
            .externs
            .iter()
            .find(|e| e.fz_name == "fz_nop")
            .expect("fz_nop not found in externs");
        assert_eq!(nop.id.0 + 1, module.externs.len() as u32);
        assert_eq!(nop.params, vec![ExternTy::Any]);
        assert_eq!(nop.ret, ExternTy::Unit);
        // main's IR references fz_nop as the last (user) extern — its index
        // moves whenever runtime.fz grows. The test inspects only that
        // it lands in extern position #(externs.len()-1).
        let last_extern_idx = module.externs.len() - 1;
        let ir = format!("{}", module);
        let needle = format!("extern#{}", last_extern_idx);
        assert!(ir.contains(&needle), "expected {} in IR:\n{}", needle, ir);
    }

    /// fz-0cv — `binary` lowers to ExternTy::Binary; `cstring` lowers to
    /// ExternTy::CString. Both are distinct from ExternTy::Any.
    #[test]
    fn binary_and_cstring_lower_to_distinct_extern_tys() {
        let src = "\
extern \"C\" fn fz_open(cstring, integer) :: integer
extern \"C\" fn fz_write(integer, binary, integer) :: integer
fn main() do fz_open(\"x\", 0) end
";
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let module = lower_program(&mut ConcreteTypes, &prog, &NullTelemetry).expect("lower");
        let open = module
            .externs
            .iter()
            .find(|e| e.fz_name == "fz_open")
            .expect("fz_open missing");
        assert_eq!(open.params, vec![ExternTy::CString, ExternTy::I64]);
        let write = module
            .externs
            .iter()
            .find(|e| e.fz_name == "fz_write")
            .expect("fz_write missing");
        assert_eq!(write.params, vec![ExternTy::I64, ExternTy::Binary, ExternTy::I64]);
        // Sanity: previous `binary` → ExternTy::Any mapping is gone.
        assert_ne!(write.params[1], ExternTy::Any);
    }

    /// fz-eol — `&libc::close/1` resolves to a synthesized top-level
    /// wrapper fn whose body contains a single `Prim::Extern` call. This
    /// is the canonical shape `resolve_dtor_from_closure` walks at
    /// runtime so `make_resource(_, &libc::close/1)` resolves to
    /// libc::close. The wrapper has zero captures so the AOT static dtor
    /// table accepts it.
    #[test]
    fn fn_ref_to_extern_synthesizes_wrapper() {
        let src = "\
extern \"C\" fn libc::close(integer) :: integer
fn main() do &libc::close/1 end
";
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let module = lower_program(&mut ConcreteTypes, &prog, &NullTelemetry).expect("lower");
        let wrap = module
            .fns
            .iter()
            .find(|f| f.name.contains("libc::close"))
            .expect("synthesized wrapper not found");
        let has_extern = wrap
            .blocks
            .iter()
            .any(|b| b.stmts.iter().any(|s| matches!(s, Stmt::Let(_, Prim::Extern(_, _, _)))));
        assert!(
            has_extern,
            "wrapper fn must contain a Prim::Extern statement; got: {}",
            wrap.name
        );
    }

    /// fz-y3k — `extern "C" fn libc::open(path :: cstring, integer) :: integer`
    /// produces an extern whose fz_name carries the `libc::` prefix while
    /// the linker-visible symbol is the bare last segment. Named-typed
    /// params (`path :: cstring`) parse identically to positional ones.
    #[test]
    fn extern_with_library_prefix_splits_fz_name_from_symbol() {
        let src = "\
extern \"C\" fn libc::open(path :: cstring, integer) :: integer
fn main() do libc::open(\"x\", 0) end
";
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let module = lower_program(&mut ConcreteTypes, &prog, &NullTelemetry).expect("lower");
        let open = module
            .externs
            .iter()
            .find(|e| e.fz_name == "libc::open")
            .expect("libc::open missing from module.externs");
        assert_eq!(open.symbol, "open", "linker symbol is the bare suffix");
        assert_eq!(open.params, vec![ExternTy::CString, ExternTy::I64]);
    }

    /// fz-jex — calling an extern with the wrong arg count must produce a
    /// LowerError at compile time, not a silent codegen truncation that
    /// panics at runtime in fz_unbox_int with a tag mismatch.
    #[test]
    fn extern_call_arity_mismatch_is_lower_error() {
        let src = "\
extern \"C\" fn libc::open(path :: cstring, integer, integer) :: integer
fn main() do libc::open(\"x\", \"x\", 0, 0) end
";
        let err = lower_src_err(src);
        match err {
            LowerError::Unsupported { what, .. } => {
                assert!(
                    what.contains("open") && what.contains("3") && what.contains("4"),
                    "expected arity-mismatch message naming open/3 vs 4 args, got: {}",
                    what
                );
            }
            other => panic!("expected Unsupported arity error, got {:?}", other),
        }
    }

    #[test]
    fn variadic_extern_records_decl_and_call_marshal_specs() {
        let src = "\
extern \"C\" fn libc::open(path :: cstring, flags :: integer, ...) :: integer
fn main() do libc::open(\"x\", 0, 0o644 :: integer) end
";
        let m = lower_src(src);
        let open = m
            .externs
            .iter()
            .find(|e| e.fz_name == "libc::open")
            .expect("libc::open missing");
        assert!(open.variadic);
        assert_eq!(open.params, vec![ExternTy::CString, ExternTy::I64]);

        let main = m.fn_by_name("main").expect("main missing");
        let extern_args = main
            .blocks
            .iter()
            .flat_map(|b| b.stmts.iter())
            .find_map(|s| match s {
                Stmt::Let(_, Prim::Extern(_, _, args)) => Some(args),
                _ => None,
            })
            .expect("extern call missing");
        assert_eq!(extern_args.len(), 3);
        assert_eq!(extern_args[0].marshal, ExternMarshal::Fixed(ExternTy::CString));
        assert_eq!(extern_args[1].marshal, ExternMarshal::Fixed(ExternTy::I64));
        assert_eq!(extern_args[2].marshal, ExternMarshal::Ascribed(ExternTy::I64));
    }

    #[test]
    fn variadic_extern_unascribed_extra_arg_stays_auto() {
        let src = "\
extern \"C\" fn libc::printf(fmt :: cstring, ...) :: integer
fn main() do libc::printf(\"%d\", 7) end
";
        let m = lower_src(src);
        let main = m.fn_by_name("main").expect("main missing");
        let extern_args = main
            .blocks
            .iter()
            .flat_map(|b| b.stmts.iter())
            .find_map(|s| match s {
                Stmt::Let(_, Prim::Extern(_, _, args)) => Some(args),
                _ => None,
            })
            .expect("extern call missing");
        assert_eq!(extern_args[1].marshal, ExternMarshal::Auto);
    }

    #[test]
    fn variadic_extern_too_few_args_is_lower_error() {
        let src = "\
extern \"C\" fn libc::open(path :: cstring, flags :: integer, ...) :: integer
fn main() do libc::open(\"x\") end
";
        let err = lower_src_err(src);
        match err {
            LowerError::Unsupported { what, .. } => {
                assert!(
                    what.contains("open") && what.contains("at least 2") && what.contains("1"),
                    "expected variadic arity message, got: {}",
                    what
                );
            }
            other => panic!("expected Unsupported arity error, got {:?}", other),
        }
    }

    #[test]
    fn extern_id_is_stable_and_extern_idx_is_consistent() {
        let toks = Lexer::new("extern \"C\" fn fz_nop(any) :: nil\nfn main() do fz_nop(1) end\n")
            .tokenize()
            .expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let module = lower_program(&mut ConcreteTypes, &prog, &NullTelemetry).expect("lower");
        // extern_idx must have an entry for every extern.
        assert_eq!(module.extern_idx.len(), module.externs.len());
        // Each extern's id field must resolve via extern_by_id to itself.
        for (i, e) in module.externs.iter().enumerate() {
            assert_eq!(module.extern_idx[&e.id], i, "extern_idx out of sync at index {}", i);
            assert_eq!(module.extern_by_id(e.id).fz_name, e.fz_name);
        }
        // ExternIds are monotonically increasing (counter-based, not len()-based).
        let ids: Vec<u32> = module.externs.iter().map(|e| e.id.0).collect();
        assert!(
            ids.windows(2).all(|w| w[0] < w[1]),
            "ExternIds not monotonic: {:?}",
            ids
        );
    }

    /// fz-f88.5 — every lowered FnIr carries an origin category. This
    /// test pins the contract: prelude fns are `Prelude`, user fns are
    /// `User`, and the well-known synthesized cont families
    /// (fn_clause_, k_, lambda_, if_, case_) map to their respective
    /// variants based on name prefix.
    #[test]
    fn fn_category_tags_match_origin() {
        // Mix user fns covering: multi-clause dispatch (-> MultiClauseCont),
        // CPS-split via non-tail call (-> CpsCont), and lambda lifting
        // (-> LambdaLift).
        let src = "\
fn id(x), do: x
fn pick(:a), do: 1
fn pick(:b), do: 2
fn make_adder(x), do: fn (z) -> x + z end

fn main() do
  id(pick(:a))
  make_adder(1)
end
";
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let module = lower_program(&mut ConcreteTypes, &prog, &NullTelemetry).expect("lower");

        let user_names = ["id", "pick", "make_adder", "main"];
        for f in &module.fns {
            let expected = if user_names.contains(&f.name.as_str()) {
                FnCategory::User
            } else if f.name.starts_with("fn_clause_") {
                FnCategory::MultiClauseCont
            } else if f.name.starts_with("lambda_") {
                FnCategory::LambdaLift
            } else if f.name.starts_with("k_") {
                FnCategory::CpsCont
            } else if f.name.contains("_matcher_") {
                // Internal matchers are no longer production lowering
                // artifacts, but keep the category rule for any explicit
                // matcher helper tests that construct such fns.
                FnCategory::Matcher
            } else if f.name.starts_with("if_")
                || f.name.starts_with("case_")
                || f.name.starts_with("cond_")
                || f.name.starts_with("with_")
            {
                FnCategory::ControlFlowCont
            } else {
                // Anything else must be prelude lowered from runtime.fz.
                FnCategory::Prelude
            };
            assert_eq!(
                f.category, expected,
                "{} (id {}) categorized as {:?}, expected {:?}",
                f.name, f.id.0, f.category, expected,
            );
        }
    }

    // fz-puj.52.7 — internal case / multi-clause / with-else dispatch no
    // longer mints production matcher fns. Receive remains the ABI-driven
    // matcher-fn path.

    // ----- fz-puj.36 (H7) — PatternMatrix construction from receive clauses -----

    fn parse_receive_clauses(src: &str) -> Vec<MatchClause> {
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        fn find_receive(e: &Expr) -> Option<&Vec<MatchClause>> {
            match e {
                Expr::Receive { clauses, .. } => Some(clauses),
                Expr::Block(es) => es.iter().find_map(|s| find_receive(&s.node)),
                _ => None,
            }
        }
        for item in &prog.items {
            if let Item::Fn(fd) = item.as_ref() {
                for clause in &fd.clauses {
                    if let Some(rxs) = find_receive(&clause.body.node) {
                        return rxs.clone();
                    }
                }
            }
        }
        panic!("no receive clauses found in source");
    }

    #[test]
    fn build_receive_pattern_matrix_one_clause_shape() {
        let clauses = parse_receive_clauses("fn rx() do receive do {:ping, _} -> :pong end end");
        let pattern_matrix = build_receive_pattern_matrix(Var(0), &clauses);
        assert_eq!(pattern_matrix.subjects, vec![Var(0)]);
        assert_eq!(pattern_matrix.rows.len(), 1);
        assert_eq!(pattern_matrix.rows[0].patterns.len(), 1);
        assert!(pattern_matrix.rows[0].preconditions.is_empty());
        assert!(pattern_matrix.rows[0].guard.is_none());
        assert_eq!(pattern_matrix.rows[0].body_id, 0);
    }

    #[test]
    fn build_receive_pattern_matrix_multi_clause_preserves_order_and_ids() {
        let clauses = parse_receive_clauses(
            "fn rx() do receive do
                :ping -> :pong
                {:msg, _} -> :ok
                _ -> :other
            end end",
        );
        let pattern_matrix = build_receive_pattern_matrix(Var(7), &clauses);
        assert_eq!(pattern_matrix.subjects, vec![Var(7)]);
        assert_eq!(pattern_matrix.rows.len(), 3);
        for (i, row) in pattern_matrix.rows.iter().enumerate() {
            assert_eq!(row.body_id, i as BodyId);
            assert_eq!(row.patterns.len(), 1);
            assert!(row.preconditions.is_empty());
        }
    }

    #[test]
    fn build_receive_pattern_matrix_carries_guard() {
        let clauses = parse_receive_clauses(
            "fn rx() do receive do
                n when n > 0 -> :positive
                _ -> :other
            end end",
        );
        let pattern_matrix = build_receive_pattern_matrix(Var(0), &clauses);
        assert_eq!(pattern_matrix.rows.len(), 2);
        assert!(
            pattern_matrix.rows[0].guard.is_some(),
            "first clause's `when n > 0` guard must appear in row[0].guard"
        );
        assert!(pattern_matrix.rows[1].guard.is_none());
    }

    #[test]
    fn case_guard_with_pure_user_fn_inlines_and_lowers() {
        let src = "fn is_pos(n) do n > 0 end
                   fn main() do
                     case 5 do
                       n when is_pos(n) -> :pos
                       _ -> :neg
                     end
                   end";
        let _ = lower_src(src);
    }

    #[test]
    fn case_guard_with_multi_clause_user_fn_lowers_dispatch() {
        let src = "fn is_pos(0) do false end
                   fn is_pos(n) do n > 0 end
                   fn main() do
                     case 5 do
                       n when is_pos(n) -> dbg(1)
                       _ -> dbg(0)
                     end
                   end";
        assert_eq!(run_and_capture(src).trim(), "1");
    }

    #[test]
    fn guarded_list_cons_clause_survives_compiled_folding() {
        let src = "fn partition(_, [], lo, hi), do: {lo, hi}
                   fn partition(p, [h | t], lo, hi) when h < p, do: partition(p, t, [h | lo], hi)
                   fn partition(p, [h | t], lo, hi), do: partition(p, t, lo, [h | hi])
                   fn main() do dbg(partition(3, [1, 4, 2], [], [])) end";
        assert_eq!(run_and_capture(src).trim(), "{[2, 1], [4]}");
    }

    // ----- fz-yxs (E2) — selective receive lowering -----

    #[test]
    fn lower_receive_one_clause_emits_receive_matched() {
        let src = "fn loop_one() do
              receive do
                {:ping, sender} -> :pong
              end
            end";
        let m = lower_src(src);
        let s = format!("{}", m);
        assert!(
            s.contains("receive_matched [1 clauses]"),
            "expected Term::ReceiveMatched, got:\n{}",
            s
        );
        assert!(
            s.contains("rx_clause_0_body"),
            "expected clause body fn name, got:\n{}",
            s
        );
    }

    #[test]
    fn lower_receive_after_clause_emits_after_body() {
        let src = "fn rx_timeout() do
              receive do
                {:done, x} -> x
              after 100 -> :timeout
              end
            end";
        let m = lower_src(src);
        let s = format!("{}", m);
        assert!(s.contains("rx_after_body"), "expected after body fn, got:\n{}", s);
        assert!(
            s.contains("after("),
            "expected after annotation on terminator, got:\n{}",
            s
        );
    }

    #[test]
    fn lower_receive_pinned_resolves_outer_scope() {
        let src = "fn rx_pinned(want) do
              receive do
                {^want, payload} -> payload
              end
            end";
        let m = lower_src(src);
        let s = format!("{}", m);
        assert!(
            s.contains("pinned=[^want="),
            "expected pinned `want` resolved against outer scope, got:\n{}",
            s
        );
    }

    #[test]
    fn lower_receive_pinned_unbound_is_error() {
        let src = "fn rx() do
              receive do
                {^nope, _} -> 0
              end
            end";
        let err = lower_src_err(src);
        match err {
            LowerError::Unbound { name, .. } => {
                assert_eq!(name, "^nope");
            }
            other => panic!("expected Unbound(^nope), got {:?}", other),
        }
    }

    #[test]
    fn lower_receive_planner_accepts_well_formed() {
        // Acceptance bullet: planner accepts well-formed selective receive.
        let src = "fn rx() do
              receive do
                {:ping, _} -> 1
                {:pong, _} -> 2
              end
            end";
        let m = lower_src(src);
        // Typing must not panic and must produce a ModulePlan for the
        // module. We don't pin the return type — that depends on the
        // body return type which the bodies set to const ints.
        let mut ct = ConcreteTypes;
        let mt = plan_module(&mut ct, &m, &NullTelemetry);
        // No diagnostics from the pure-guard / pure-pattern pass either.
        let diags = collect_diagnostics(&mut ct, &m, &mt, &NullTelemetry);
        let impure: Vec<_> = diags
            .as_slice()
            .iter()
            .filter(|d| d.code == codes::TYPE_IMPURE_RECEIVE_GUARD)
            .collect();
        assert!(impure.is_empty(), "unexpected purity diags: {:?}", impure);
    }

    #[test]
    fn lower_receive_rejects_impure_guard() {
        // The helper body calls an extern-backed runtime fn, so it cannot
        // lower into the restricted Matcher guard subset.
        let src = "fn helper(), do: make_ref()
            fn rx() do
              receive do
                {:foo, _} when helper() -> 0
              end
            end";
        let err = lower_src_err(src);
        assert!(
            format!("{:?}", err).contains("UnsupportedGuardExpr"),
            "expected restricted guard-lowering error, got {:?}",
            err
        );
    }

    fn first_receive_matcher(m: &Module) -> Option<&Matcher> {
        for f in &m.fns {
            for b in &f.blocks {
                if let Term::ReceiveMatched { matcher, .. } = &b.terminator {
                    return Some(matcher.as_ref());
                }
            }
        }
        None
    }

    fn matcher_has_guard_dispatch(matcher: &Matcher) -> bool {
        fn expr_has_dispatch(expr: &GuardExpr) -> bool {
            match expr {
                GuardExpr::Dispatch { .. } => true,
                GuardExpr::Unary { expr, .. } => expr_has_dispatch(expr),
                GuardExpr::Binary { lhs, rhs, .. } => expr_has_dispatch(lhs) || expr_has_dispatch(rhs),
                GuardExpr::Const(_) | GuardExpr::Subject(_) | GuardExpr::Pinned(_) => false,
            }
        }
        matcher.nodes.iter().any(|node| {
            matches!(
                node,
                MatcherNode::Guard { expr, .. } if expr_has_dispatch(expr)
            )
        })
    }

    #[test]
    fn receive_guard_with_single_clause_helper_lowers_into_matcher() {
        let src = "fn positive(n), do: n > 0
            fn rx() do
              receive do
                n when positive(n) -> n
                _ -> 0
              end
            end";
        let m = lower_src(src);
        let matcher = first_receive_matcher(&m).expect("receive matcher");
        assert!(
            matcher
                .nodes
                .iter()
                .any(|node| matches!(node, MatcherNode::Guard { .. })),
            "expected inlined helper guard in Matcher: {:#?}",
            matcher
        );
    }

    #[test]
    fn receive_guard_capture_walks_helper_call_args() {
        let src = "fn positive(n), do: n > 0
            fn rx(limit) do
              receive do
                n when positive(n + limit) -> n
                _ -> 0
              end
            end";
        let m = lower_src(src);
        let matcher = first_receive_matcher(&m).expect("receive matcher");
        assert!(
            matcher.pinned.iter().any(|pinned| pinned.name == "limit"),
            "expected guard call argument capture in Matcher pinned inputs: {:#?}",
            matcher
        );
    }

    #[test]
    fn receive_guard_with_transitive_helper_lowers_into_matcher() {
        let src = "fn positive(n), do: n > 0
            fn wanted(n), do: positive(n)
            fn rx() do
              receive do
                n when wanted(n) -> n
                _ -> 0
              end
            end";
        let m = lower_src(src);
        let matcher = first_receive_matcher(&m).expect("receive matcher");
        assert!(
            matcher
                .nodes
                .iter()
                .any(|node| matches!(node, MatcherNode::Guard { .. })),
            "expected transitive helper guard in Matcher: {:#?}",
            matcher
        );
    }

    #[test]
    fn receive_guard_with_multi_clause_helper_lowers_dispatch() {
        let src = "fn wanted({:ok, n}), do: n > 0
            fn wanted(_), do: false
            fn rx() do
              receive do
                msg when wanted(msg) -> msg
                _ -> 0
              end
            end";
        let m = lower_src(src);
        let matcher = first_receive_matcher(&m).expect("receive matcher");
        assert!(
            matcher_has_guard_dispatch(matcher),
            "expected multi-clause helper guard dispatch in Matcher: {:#?}",
            matcher
        );
    }

    #[test]
    fn receive_guard_helper_dispatch_handles_destructuring() {
        let src = "fn wanted({:ok, {n, _}}), do: n > 0
            fn wanted(_), do: false
            fn rx() do
              receive do
                msg when wanted(msg) -> msg
                _ -> 0
              end
            end";
        let m = lower_src(src);
        let matcher = first_receive_matcher(&m).expect("receive matcher");
        assert!(
            matcher_has_guard_dispatch(matcher),
            "expected nested helper dispatch for destructuring helper: {:#?}",
            matcher
        );
    }

    #[test]
    fn receive_matcher_prepares_heap_map_keys_outside_matcher() {
        let src = "fn rx() do
              receive do
                %{\"id\" => value} -> value
                _ -> 0
              end
            end";
        let m = lower_src(src);
        let matcher = first_receive_matcher(&m).expect("receive matcher");
        assert_eq!(matcher.prepared_keys, vec![MatcherConst::Utf8Binary(b"id".to_vec())]);
        let s = format!("{}", m);
        assert!(
            s.contains("pinned=[^__matcher_key_0="),
            "expected prepared map key to be threaded as receive pinned input, got:\n{}",
            s
        );
    }

    // ----------------------------------------------------------------
    // fz-axu.24 (M3) — brand-mint visibility gate
    // ----------------------------------------------------------------

    fn module_with_brand_in_fn(fn_name: &str, brand_tag: &str) -> (Module, HashMap<(FnId, BlockId), Vec<Span>>) {
        let mut b = FnBuilder::new(FnId(0), fn_name);
        let entry = b.block(vec![]);
        let bs = b.let_(entry, Prim::ConstBitstring(vec![104], 8));
        let branded = b.let_(entry, Prim::Brand(bs, brand_tag.to_string()));
        b.set_terminator(entry, Term::Halt(branded));
        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        (mb.build(), HashMap::new())
    }

    #[test]
    fn brand_visibility_passes_for_builtin_utf8_anywhere() {
        // Built-in `utf8` (no `::` in tag) has no owner; minting it
        // from any fn — even a user module — is allowed.
        let (m, spans) = module_with_brand_in_fn("Mail.send", "utf8");
        let fn_spans = HashMap::new();
        check_brand_visibility(&mut ConcreteTypes, &m, &spans, &fn_spans).expect("utf8 mint must be allowed");
    }

    #[test]
    fn brand_visibility_passes_when_fn_owns_brand() {
        // Brand `Mail::Email` minted from fn `Mail.send` (using_module
        // = "Mail") is fine — same owner.
        let (m, spans) = module_with_brand_in_fn("Mail.send", "Mail::Email");
        let fn_spans = HashMap::new();
        check_brand_visibility(&mut ConcreteTypes, &m, &spans, &fn_spans).expect("same-module mint must be allowed");
    }

    #[test]
    fn brand_visibility_rejects_cross_module_mint() {
        // Brand `Mail::Email` minted from fn `Other.handler`
        // (using_module = "Other") must be rejected.
        let (m, spans) = module_with_brand_in_fn("Other.handler", "Mail::Email");
        let fn_spans = HashMap::new();
        let err = check_brand_visibility(&mut ConcreteTypes, &m, &spans, &fn_spans)
            .expect_err("cross-module mint must be rejected");
        match err {
            LowerError::BrandMintVisibility {
                brand,
                owner_module,
                using_module,
                ..
            } => {
                assert_eq!(brand, "Mail::Email");
                assert_eq!(owner_module, "Mail");
                assert_eq!(using_module, "Other");
            }
            _ => panic!("expected BrandMintVisibility, got {:?}", err),
        }
    }

    #[test]
    fn brand_visibility_rejects_top_level_mint_of_owned_brand() {
        // Top-level fn `main` (no module prefix) trying to mint a
        // module-owned brand is also rejected.
        let (m, spans) = module_with_brand_in_fn("main", "Mail::Email");
        let fn_spans = HashMap::new();
        let err = check_brand_visibility(&mut ConcreteTypes, &m, &spans, &fn_spans)
            .expect_err("top-level mint of owned brand must be rejected");
        let diag = err.to_diagnostic();
        assert!(
            diag.message.contains("<top-level>"),
            "diag should mention top-level using_module: {}",
            diag.message,
        );
    }
}
