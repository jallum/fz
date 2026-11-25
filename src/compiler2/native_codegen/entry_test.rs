//! What a continuation's entry harness emits for the frame it resumes in. Each
//! test compiles the harness for one frame shape and reads the CLIF it left.

use super::*;
use crate::fz_ir::{Block, BlockId, Term, Var};
use cranelift_codegen::ir::{InstBuilder, InstructionData, Opcode, types};
use cranelift_frontend::FunctionBuilderContext;
use fz_runtime::any_value::closure_size_for_count;

/// User captures of the frame under test, behind the outer continuation.
const USER_CAPTURES: usize = 2;

/// The frame's slots: the outer continuation and the user captures.
const FRAME_SLOTS: usize = 1 + USER_CAPTURES;

/// Emits `harness_cont_fn` for a continuation that takes `USER_CAPTURES`
/// reference captures and no extras, and answers the function it built.
fn resume_entry(in_frame: bool) -> ir::Function {
    let object = cranelift_object::ObjectBuilder::new(
        host_isa_for(CodeHome::Executable),
        "entry_test",
        cranelift_module::default_libcall_names(),
    )
    .expect("an object builder for the host");
    let mut module = cranelift_object::ObjectModule::new(object);
    let mut ctx = module.make_context();
    let mut fbctx = FunctionBuilderContext::new();
    let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
    let entry = b.create_block();
    b.append_block_param(entry, types::I64);
    b.switch_to_block(entry);
    b.seal_block(entry);
    let params = b.block_params(entry).to_vec();
    let mut cache = CodegenCache::default();
    let sites = std::cell::RefCell::new(SiteTable::declare(&mut module).expect("declare the site counters"));
    let scope = SiteScope {
        sites: &sites,
        function: "entry_test",
    };
    let mut body = CodegenFn::new(&mut b, &mut module, &mut cache, scope);
    let entry_blk = Block {
        id: BlockId(0),
        params: (0..USER_CAPTURES as u32).map(Var).collect(),
        stmts: Vec::new(),
        terminator: Term::Goto(BlockId(0), Vec::new()),
    };
    let reprs = [ArgRepr::ValueRef; USER_CAPTURES];
    let mut var_env = HashMap::default();
    let (outer, _) = harness_cont_fn(&mut body, &entry_blk, &params, &reprs, 0, in_frame, &mut var_env);
    body.b.ins().return_(&[outer]);
    drop(body);
    b.finalize(module.target_config());
    ctx.func
}

fn instructions(func: &ir::Function) -> impl Iterator<Item = &InstructionData> {
    func.layout
        .blocks()
        .flat_map(|block| func.layout.block_insts(block))
        .map(|inst| &func.dfg.insts[inst])
}

fn header_reads(func: &ir::Function) -> usize {
    instructions(func)
        .filter(|inst| matches!(inst, InstructionData::Load { opcode: Opcode::Uload32, offset, .. } if i32::from(*offset) == 0))
        .count()
}

/// The constants added to a value by the function's adds.
fn added_constants(func: &ir::Function) -> Vec<i64> {
    instructions(func)
        .filter_map(|inst| match inst {
            InstructionData::Binary {
                opcode: Opcode::Iadd,
                args: [_, addend],
            } => match func.dfg.insts[func.dfg.value_def(*addend).inst()?] {
                InstructionData::UnaryImm {
                    opcode: Opcode::Iconst,
                    imm,
                } => Some(imm.bits()),
                _ => None,
            },
            _ => None,
        })
        .collect()
}

/// The resume entry is compiled for one frame shape, so the capture count is
/// a number in the code: the entry reads no word of the frame's header.
#[test]
fn a_resume_entry_of_a_known_frame_shape_does_not_read_the_frame_header() {
    assert_eq!(header_reads(&resume_entry(false)), 0);
}

/// The frame's end, which the release compares with the heap's tip, is its
/// address plus the size the compiler computed for the frame's shape.
#[test]
fn a_resume_entry_finds_the_frame_end_by_a_constant_size() {
    let size = closure_size_for_count(FRAME_SLOTS) as i64;
    assert!(added_constants(&resume_entry(false)).contains(&size));
}

/// A shared body frame is wider than the continuation's own captures and is
/// never released at a resume; its reads still find the count in the header.
#[test]
fn a_body_frame_entry_still_reads_the_frame_header() {
    assert!(header_reads(&resume_entry(true)) > 0);
}
