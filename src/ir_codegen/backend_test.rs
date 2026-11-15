use super::*;
use cranelift_codegen::ir::InstBuilder;
use cranelift_frontend::FunctionBuilder;

/// Bytes of machine code above which the system allocator on macOS places a
/// block in a region gigabytes away from small blocks.
const FAR_PLACED_CODE_BYTES: usize = 4 << 20;

/// A function with more code than the allocator keeps near small blocks still
/// reaches its module's data: the module's code and data share one span, so
/// the pc-relative reference resolves and the function reads the data.
#[test]
fn a_function_with_megabytes_of_code_reads_its_modules_data() {
    let mut backend = JitBackend::new();
    let module = backend.module_mut();
    let data = module.declare_data("answer", Linkage::Local, false, false).unwrap();
    let mut description = DataDescription::new();
    description.define(42u64.to_le_bytes().to_vec().into_boxed_slice());
    module.define_data(data, &description).unwrap();

    let mut ctx = module.make_context();
    ctx.func.signature.params.push(AbiParam::new(types::I64));
    ctx.func.signature.returns.push(AbiParam::new(types::I64));
    let function = module
        .declare_function("long", Linkage::Local, &ctx.func.signature)
        .unwrap();
    let mut fbctx = FunctionBuilderContext::new();
    let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
    let entry = b.create_block();
    b.append_block_params_for_function_params(entry);
    b.switch_to_block(entry);
    b.seal_block(entry);
    let input = b.block_params(entry)[0];
    let mut acc = input;
    let steps = FAR_PLACED_CODE_BYTES / 6;
    for step in 0..steps {
        acc = b.ins().imul(acc, input);
        acc = b.ins().iadd_imm(acc, step as i64);
    }
    let global = module.declare_data_in_func(data, b.func);
    let address = b.ins().symbol_value(types::I64, global);
    let answer = b
        .ins()
        .load(types::I64, cranelift_codegen::ir::MemFlags::trusted(), address, 0);
    let result = b.ins().iadd(answer, acc);
    b.ins().return_(&[result]);
    b.finalize();
    module.define_function(function, &mut ctx).unwrap();
    let code_bytes = ctx.compiled_code().unwrap().code_info().total_size as usize;
    assert!(
        code_bytes > FAR_PLACED_CODE_BYTES,
        "the function has {code_bytes} bytes of code"
    );

    module.finalize_definitions().unwrap();
    let long: extern "C" fn(i64) -> i64 = unsafe { std::mem::transmute(module.get_finalized_function(function)) };
    let last_step = steps as i64 - 1;
    assert_eq!(
        long(0),
        42 + last_step,
        "the function reads the data its module defines"
    );
}
