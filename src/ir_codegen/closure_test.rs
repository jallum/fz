use super::*;
use cranelift_codegen::Context;
use cranelift_codegen::ir::{AbiParam, Signature};
use cranelift_codegen::isa::CallConv;

fn render_pointer_ref_pack_for_arch(arch: TaggedRefArch) -> String {
    let mut ctx = Context::new();
    ctx.func.signature = Signature::new(CallConv::SystemV);
    ctx.func.signature.params.push(AbiParam::new(types::I64));
    ctx.func.signature.returns.push(AbiParam::new(types::I64));
    let mut fbctx = FunctionBuilderContext::new();
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let ptr = b.block_params(entry)[0];
        let value = emit_tagged_pointer_ref_word_for_arch(&mut b, ptr, TAG_FWD, arch);
        b.ins().return_(&[value]);
        b.finalize();
    }
    ctx.func.display().to_string()
}

#[test]
fn arm64_tbi_pointer_ref_pack_omits_clear_step() {
    let clif = render_pointer_ref_pack_for_arch(TaggedRefArch::Arm64Tbi);

    assert!(
        !clif.contains("band_imm"),
        "arm64/TBI must not mask fresh pointers:\n{clif}"
    );
    assert!(
        !clif.contains("ishl_imm") && !clif.contains("ushr_imm"),
        "arm64/TBI must not shift-clear fresh pointers:\n{clif}"
    );
    assert!(
        clif.contains("bor_imm v0, 0x0800_0000_0000_0000"),
        "arm64/TBI should OR the top-byte tag directly into the pointer:\n{clif}"
    );
}

#[test]
fn x86_64_pointer_ref_pack_shift_clears_before_tagging() {
    let clif = render_pointer_ref_pack_for_arch(TaggedRefArch::X86_64Canonical57);

    assert!(
        clif.contains("ishl_imm v0, 7") && clif.contains("ushr_imm"),
        "x86_64 canonical refs must shift-clear high bits before tagging:\n{clif}"
    );
    assert!(
        !clif.contains("band_imm"),
        "x86_64 must not use mask immediates for this clear:\n{clif}"
    );
    assert!(
        clif.contains("bor_imm") && clif.contains("0x1000_0000_0000_0000"),
        "x86_64 canonical refs should OR the shifted tag word after clearing:\n{clif}"
    );
}
