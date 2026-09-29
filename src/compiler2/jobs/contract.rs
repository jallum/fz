//! Compiler2 function-contract derivation jobs.
//!
//! A contract is the callee-owned declared surface for one function. Semantic
//! call resolution consumes it to refine observed arguments before waking
//! activations or callable-boundary demand.

use std::collections::HashMap;

use crate::ast::Attribute;
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::extern_contract::{
    ExternContractError, explicit_extern_wire_hint, extern_semantic_contract, extern_symbol_from_name, ty_to_extern_ty,
    variadic_tail_domain,
};
use crate::function_surface::FunctionSurface;
use crate::fz_ir::ExternAbi;

use super::super::body::LoweredExtern;
use super::super::code::SourceOwner;
use super::super::contract::FunctionContract;
use super::super::drive::{FactKey, JobEffects, current_uses};
use super::super::identity::FunctionId;
use super::super::scheduler::FatalError;
use super::super::world::World;

pub(super) fn derive_function_contract(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    function: FunctionId,
) -> Result<JobEffects, FatalError> {
    let Some(_) = world.function_defined_revision(function) else {
        return Ok(world.wait_for_function_definition(function));
    };
    if !world.function_declares_contract(function) {
        return Ok(JobEffects::default());
    }

    let (source, surface) = world.function_definition(function);
    let declared_specs = surface
        .attrs
        .iter()
        .filter_map(|attr| match attr {
            Attribute::Spec(spec) => Some(spec.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let specs = if !declared_specs.is_empty() {
        declared_specs
    } else {
        match extern_semantic_contract(&surface) {
            Ok(spec) => vec![spec],
            Err(ExternContractError::NotAnExtern) => Vec::new(),
            Err(refusal @ ExternContractError::WireSpellingInsideType { .. }) => {
                emit_job_diagnostic(tel, refusal.diagnostic(&surface.name, surface.name_span));
                Vec::new()
            }
        }
    };

    let mut reads = vec![FactKey::FunctionDefined(function)];
    let mut waits = Vec::new();
    for referenced in world.function_type_refs(function).iter().cloned() {
        let fact = FactKey::TypeDefined(referenced);
        if world.has_fact(&fact) {
            reads.push(fact);
        } else {
            waits.push(fact);
        }
    }
    // Same wait, `StructDefined` side: a `%Mod{...}` in this contract needs
    // `Mod`'s precise field order before `resolve_spec_decl` can classify it,
    // exactly as the `TypeDefined` loop above waits on referenced aliases
    // (fz-rh2.17.5.6.10).
    for module in world.function_type_struct_refs(function).iter().copied() {
        let fact = FactKey::StructDefined(module);
        if world.has_fact(&fact) {
            reads.push(fact);
        } else {
            waits.push(fact);
        }
    }
    if !waits.is_empty() {
        return Ok(JobEffects {
            reads: current_uses(reads),
            waits: current_uses(waits),
            ..JobEffects::default()
        });
    }

    // A spec that fails to resolve is the user's error, not the engine's:
    // report it and let the diagnosed spec constrain nothing. Resolved
    // sibling specs still contribute, and the contract fact still publishes
    // so consumers never block on a diagnosed declaration.
    let mut contract = Vec::with_capacity(specs.len());
    for spec in &specs {
        match world.resolve_spec_decl(source.namespace, spec) {
            Ok(resolved) => contract.push(resolved),
            Err(error) => emit_job_diagnostic(
                tel,
                Diagnostic::error(
                    codes::RESOLVE_TYPE_ALIAS,
                    format!(
                        "compiler2 could not resolve function contract for `{}`: {}",
                        surface.name, error.msg
                    ),
                    error.span,
                ),
            ),
        }
    }
    let contract = if surface.variadic {
        let tail = variadic_tail_domain(world.types_mut());
        FunctionContract::from_resolved_variadic(world.types_mut(), contract, tail)
    } else {
        FunctionContract::from_resolved(world.types_mut(), contract)
    };
    let contract = if surface.extern_abi.is_some() {
        let wire = resolve_extern_wire(world, tel, source.owner, &surface, &contract)?;
        contract.with_extern_wire(wire)
    } else {
        contract
    };
    Ok(publish_contract(world, tel, function, reads, contract))
}

/// The declared calling convention, or a diagnostic.
///
/// Three ways to get it wrong, and every one of them is refused HERE rather
/// than in a door's lowering, because a diagnostic raised in the shared front
/// end is the only kind every door raises identically. Each of these was, at
/// some point, a per-door check that protected fewer doors than it appeared
/// to.
///
/// 1. An unrecognised name must not fall back to C: the conventions disagree
///    about the implicit process argument and about what a `binary`
///    parameter is, so a wrong guess is a crash inside the callee.
///
/// 2. `"fz"` is reserved to the runtime library, because it passes fz's own
///    `*mut Process` and fz's internal value representation. Both belong to
///    the runtime, and a foreign function cannot accept either.
///
/// 3. There is no variadic `"fz"`: a variadic call goes through a
///    fixed-arity C dispatcher with nowhere to put the process.
fn resolve_extern_abi(
    tel: &impl crate::telemetry::Telemetry,
    world: &World,
    owner: SourceOwner,
    surface: &FunctionSurface,
) -> Result<ExternAbi, FatalError> {
    let declared = surface
        .extern_abi
        .as_deref()
        .expect("extern signatures only resolve for extern fns");
    let Some(abi) = ExternAbi::parse(declared) else {
        return Err(extern_abi_error(
            tel,
            surface,
            format!(
                "unknown extern ABI `{}` on `{}`; expected one of {}",
                declared,
                surface.name,
                ExternAbi::ALL
                    .iter()
                    .map(|known| format!("`{known}`"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        ));
    };
    if abi.takes_process() && !world.is_bootstrap(owner) {
        return Err(extern_abi_error(
            tel,
            surface,
            format!(
                "`{}` declares the `fz` ABI, which is reserved for fz's own runtime library; \
                 it passes the running process and fz's internal value representation, \
                 so declare a foreign symbol `extern \"C\"` instead",
                surface.name
            ),
        ));
    }
    if abi.takes_process() && surface.variadic {
        return Err(extern_abi_error(
            tel,
            surface,
            format!(
                "`{}` is variadic and declares the `fz` ABI; every variadic call goes through a \
                 fixed-arity C dispatcher, which has nowhere to put the implicit process argument",
                surface.name
            ),
        ));
    }
    Ok(abi)
}

fn extern_abi_error(tel: &impl crate::telemetry::Telemetry, surface: &FunctionSurface, message: String) -> FatalError {
    emit_job_diagnostic(
        tel,
        Diagnostic::error(codes::LOWER_UNSUPPORTED, message, surface.name_span),
    );
    FatalError
}

/// An extern has no body of its own, so its declared types and bounds come
/// off the contract clause this same job just built, not a second
/// resolution somewhere downstream.
fn resolve_extern_wire(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    owner: SourceOwner,
    surface: &FunctionSurface,
    contract: &FunctionContract,
) -> Result<LoweredExtern, FatalError> {
    // Checked first: it is the cheapest question, and a wrong answer makes
    // every later one moot.
    let abi = resolve_extern_abi(tel, world, owner, surface)?;
    // A refused contract (a wire spelling with no register of its own inside
    // a tuple, say) already reported its own diagnostic in the specs loop
    // above, and leaves this contract with no arrow. There is nothing here
    // to lower an extern signature from, so the compile halts on the
    // diagnostic already filed rather than panicking on a witness that was
    // never going to exist.
    let Some(clause) = contract.arrows.first().cloned() else {
        return Err(FatalError);
    };
    let params_ty = world.types().arrow_params(&clause.arrow);
    let result_ty = world
        .types()
        .arrow_result(&clause.arrow)
        .expect("a contract clause is an arrow with a result slot");
    let params: Vec<_> = surface
        .extern_param_tokens
        .iter()
        .zip(params_ty.iter())
        .map(|(body, ty)| extern_param_wire(world.types_mut(), body, ty, &clause.bounds, abi))
        .collect::<Result<_, _>>()
        .map_err(|message| extern_abi_error(tel, surface, format!("`{}`: {message}", surface.name)))?;
    let ret = extern_return_wire(
        world.types_mut(),
        &surface.extern_ret_tokens,
        &result_ty,
        &clause.bounds,
        abi,
    )
    .map_err(|message| extern_abi_error(tel, surface, format!("`{}`: {message}", surface.name)))?;
    let symbol = extern_symbol_from_name(&surface.name);
    Ok(LoweredExtern {
        abi,
        symbol: symbol.to_string(),
        params,
        variadic: surface.variadic,
        ret,
    })
}

fn extern_wire_ty(
    types: &mut super::super::types::Types,
    body: &crate::ast::TypeExprBody,
    semantic_ty: &super::super::types::Ty,
    constraints: &HashMap<super::super::types::TypeVarId, super::super::types::Ty>,
) -> crate::fz_ir::ExternTy {
    if let Some(hint) = explicit_extern_wire_hint(body) {
        return hint;
    }
    let upper_bound = if constraints.is_empty() {
        *semantic_ty
    } else {
        types.instantiate(semantic_ty, constraints)
    };
    ty_to_extern_ty(types, &upper_bound)
}

fn extern_param_wire(
    types: &mut super::super::types::Types,
    body: &crate::ast::TypeExprBody,
    semantic_ty: &super::super::types::Ty,
    constraints: &HashMap<super::super::types::TypeVarId, super::super::types::Ty>,
    abi: crate::fz_ir::ExternAbi,
) -> Result<crate::fz_ir::ExternTy, String> {
    let resolved = if constraints.is_empty() {
        *semantic_ty
    } else {
        types.instantiate(semantic_ty, constraints)
    };
    if abi == crate::fz_ir::ExternAbi::C && types.max_tuple_arity(&resolved) != 0 {
        return Err("C extern aggregate arguments are unsupported; pass an opaque value reference or define an exact scalar C signature".to_string());
    }
    Ok(extern_wire_ty(types, body, semantic_ty, constraints))
}

fn extern_return_wire(
    types: &mut super::super::types::Types,
    body: &crate::ast::TypeExprBody,
    semantic_ty: &super::super::types::Ty,
    constraints: &HashMap<super::super::types::TypeVarId, super::super::types::Ty>,
    abi: crate::fz_ir::ExternAbi,
) -> Result<crate::fz_ir::ExternReturn, String> {
    let resolved = if constraints.is_empty() {
        *semantic_ty
    } else {
        types.instantiate(semantic_ty, constraints)
    };
    let tuple_arity = {
        let predicate = types.runtime_type_predicate(&resolved);
        let arities = predicate.tuples.arities();
        (!arities.cofinite && arities.values.len() == 1)
            .then(|| arities.values.iter().next().copied())
            .flatten()
    };
    if let Some(arity) = tuple_arity {
        if abi != crate::fz_ir::ExternAbi::C {
            return Err("fixed scalar-pair returns are supported only by the `C` ABI".to_string());
        }
        if arity != 2 {
            return Err(format!(
                "C extern aggregate returns require exactly two scalar fields, found tuple arity {arity}"
            ));
        }
        let fields = types.tuple_projections(&resolved, 2);
        let fields: [crate::fz_ir::ExternTy; 2] = fields
            .iter()
            .map(|field| ty_to_extern_ty(types, field))
            .collect::<Vec<_>>()
            .try_into()
            .expect("two tuple projections");
        if fields.iter().any(|field| {
            !matches!(
                field,
                crate::fz_ir::ExternTy::I64 | crate::fz_ir::ExternTy::F64 | crate::fz_ir::ExternTy::Bool
            )
        }) {
            return Err(format!(
                "C extern aggregate return fields must be integer, float, or boolean, found {fields:?}"
            ));
        }
        return Ok(crate::fz_ir::ExternReturn::Pair(fields));
    }
    if types.max_tuple_arity(&resolved) != 0 {
        return Err("C extern aggregate return must resolve to one exact two-field tuple".to_string());
    }
    Ok(crate::fz_ir::ExternReturn::Scalar(extern_wire_ty(
        types,
        body,
        semantic_ty,
        constraints,
    )))
}

fn publish_contract(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    function: FunctionId,
    reads: Vec<FactKey>,
    contract: FunctionContract,
) -> JobEffects {
    let changed = super::super::drive::ExecutionContext::new(world, tel).define_function_contract(function, contract);
    JobEffects {
        reads: current_uses(reads),
        outputs: vec![FactKey::FunctionContract(function)],
        changed: changed
            .then_some(FactKey::FunctionContract(function))
            .into_iter()
            .collect(),
        ..JobEffects::default()
    }
}

fn emit_job_diagnostic(tel: &impl crate::telemetry::Telemetry, diagnostic: Diagnostic) {
    emit_through(tel, &[diagnostic]);
}
