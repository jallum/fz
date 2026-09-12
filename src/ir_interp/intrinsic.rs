use super::*;
use fz_runtime::any_value::{AnyValue as RuntimeAnyValue, closure_arity};
use fz_runtime::intrinsic::{Comparison, Domain, Intrinsic, IntrinsicFault, NumericValue, Operation};

pub(super) fn call_intrinsic<T: crate::telemetry::Telemetry + ?Sized>(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &crate::compiler2::transport::TransportStore,
    tel: &T,
    program: &crate::compiler2::BackendProgram,
    module: &Module,
    identity: Intrinsic,
    args: &[AnyValue],
) -> Result<AnyValue, String> {
    let descriptor = identity.descriptor();
    if args.len() != descriptor.inputs.len() {
        return Err(intrinsic_fault(IntrinsicFault::Domain));
    }
    for (domain, value) in descriptor.inputs.iter().zip(args) {
        let Some(kinds) = domain.runtime_kinds() else {
            continue;
        };
        let value = value.value(runtime.cur_proc())?;
        if !kinds.contains(&value.kind()) {
            return Err(intrinsic_fault(IntrinsicFault::Domain));
        }
        if let Domain::Callable(arity) = domain
            && unsafe { closure_arity(value.heap_addr().expect("admitted closure")) } != *arity
        {
            return Err(intrinsic_fault(IntrinsicFault::Domain));
        }
    }
    match descriptor.operation {
        Operation::Arithmetic(_) | Operation::Negate => {
            let inputs = args
                .iter()
                .map(|value| match value.value(runtime.cur_proc())? {
                    RuntimeAnyValue::Int(value) => Ok(NumericValue::Integer(value)),
                    RuntimeAnyValue::Float(bits) => Ok(NumericValue::Float(f64::from_bits(bits))),
                    _ => Err(intrinsic_fault(IntrinsicFault::Domain)),
                })
                .collect::<Result<Vec<_>, _>>()?;
            identity
                .evaluate_numeric(&inputs)
                .map(|value| match value {
                    NumericValue::Integer(value) => AnyValue::Int(value),
                    NumericValue::Float(value) => AnyValue::Float(value),
                })
                .map_err(intrinsic_fault)
        }
        Operation::Compare(operation) => {
            let proc = runtime.cur_proc();
            let answer = match operation {
                Comparison::Equal => interp_operator_eq(proc, args[0], args[1])?,
                Comparison::NotEqual => !interp_operator_eq(proc, args[0], args[1])?,
                Comparison::Identical => interp_value_eq(proc, args[0], args[1])?,
                Comparison::NotIdentical => !interp_value_eq(proc, args[0], args[1])?,
                Comparison::Less => interp_cmp(proc, args[0], args[1])? < 0,
                Comparison::LessEqual => interp_cmp(proc, args[0], args[1])? <= 0,
                Comparison::Greater => interp_cmp(proc, args[0], args[1])? > 0,
                Comparison::GreaterEqual => interp_cmp(proc, args[0], args[1])? >= 0,
            };
            Ok(super::value::interp_bool_value(answer))
        }
        Operation::Panic => Err(format!("fz panic: {}", args[0].render(runtime.cur_proc()))),
        Operation::SelfPid => Ok(AnyValue::Int(unsafe { &*runtime.cur_proc() }.pid as i64)),
        Operation::MakeRef => Ok(AnyValue::Int(fz_runtime::ir_runtime::fz_make_ref_raw() as i64)),
        Operation::Send => {
            let receiver = args[0].as_i64().ok_or_else(|| "send/2: pid must be Int".to_string())? as u32;
            runtime.send_opaque(types, transport, tel, program, module, &receiver, args[1])?;
            Ok(args[1])
        }
        Operation::Spawn | Operation::SpawnOpt => {
            let (fn_id, captured) = super::binop::unpack_callable(args[0], runtime.cur_proc())?;
            let (target, inputs) = super::backend::construction_wrapper_invocation(
                runtime,
                types,
                transport,
                program,
                module,
                fn_id,
                &captured,
                &[],
            )?;
            let pid = runtime.spawn_backend(target, inputs)?;
            Ok(AnyValue::Int(pid as i64))
        }
        Operation::MakeResource => {
            let payload = args[0]
                .as_i64()
                .ok_or_else(|| "make_resource/2: payload must be integer".to_string())?;
            super::make_resource_in_current_process(
                runtime.cur_proc(),
                module,
                payload,
                args[1].value(runtime.cur_proc())?,
            )
            .map(interp_value_from_slot)
        }
    }
}

fn intrinsic_fault(fault: IntrinsicFault) -> String {
    format!("fz intrinsic fault: {fault}")
}
