//! A placement is counted at its own site and nowhere else: each kind
//! compiled code places inline, compiled into a one-placement function and run
//! on a process whose node holds the module's sites.

use super::*;
use crate::ir_codegen::backend::{Backend, JitBackend};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{Linkage, Module};
use fz_runtime::alloc_site::AllocSites as RuntimeAllocSites;
use fz_runtime::heap::{AllocStat, HeapAllocStats, INLINE_ALLOC_LAYOUT, SchemaRegistry};
use fz_runtime::pinned_abi;
use fz_runtime::process::{DEFAULT_REDUCTIONS_PER_QUANTUM, Node, Process};
use std::cell::RefCell;
use std::rc::Rc;

const FUNCTION: &str = "place_parity";

/// The kinds compiled code places inline, each with a size it places.
const PLACED: [(HeapAllocKind, usize); 5] = [
    (HeapAllocKind::Continuation, 48),
    (HeapAllocKind::ListCons, 16),
    (HeapAllocKind::Struct, 32),
    (HeapAllocKind::Closure, 32),
    (HeapAllocKind::ScalarBox, 16),
];

/// How full the tip is when the placement runs.
#[derive(Clone, Copy, Debug)]
enum Tip {
    Roomy,
    /// No room: the runtime finds some and the placement is still counted at
    /// its site.
    Full,
}

/// A function that places `size` bytes of `kind` once, with the process that
/// runs it: its node holds the module's one site, as a loaded program's does.
fn one_placement(kind: HeapAllocKind, size: usize) -> (Process, *const u8, JitBackend) {
    let mut backend = JitBackend::new();
    let module = backend.module_mut();
    let mut ctx = module.make_context();
    let mut fbctx = FunctionBuilderContext::new();
    let mut sig = module.make_signature();
    sig.params = vec![ir::AbiParam::new(types::I64)];
    sig.returns = vec![ir::AbiParam::new(types::I64)];
    ctx.func.signature = sig.clone();
    let sites = RefCell::new(AllocSites::declare(module).expect("declare the site counters"));
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let mut cache = CodegenCache::default();
        let scope = SiteScope {
            sites: &sites,
            function: FUNCTION,
        };
        let mut body = CodegenFn::new(&mut b, module, &mut cache, scope);
        let address = emit_place(&mut body, kind, size);
        body.b.ins().return_(&[address]);
        b.finalize(module.target_config());
    }
    let id = module
        .declare_function(FUNCTION, Linkage::Export, &sig)
        .expect("declare the function");
    module.define_function(id, &mut ctx).expect("define the function");
    let (counts_id, registered) = sites.into_inner().define(module).expect("define the site counters");
    assert_eq!(registered.len(), 1, "one placement is one site");
    module.finalize_definitions().expect("finalize the function");
    let code = module.get_finalized_function(id);
    let (counts, _) = module.get_finalized_data(counts_id);
    let node = Rc::new(Node::empty());
    node.register_alloc_sites(unsafe { RuntimeAllocSites::new(registered, counts.cast_mut().cast()) });
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let process = Process::with_node(node, schemas, 0, DEFAULT_REDUCTIONS_PER_QUANTUM);
    (process, code, backend)
}

fn tip_room(process: &Process) -> usize {
    let field = |offset: usize| unsafe {
        *(((&process.heap as *const fz_runtime::heap::Heap).cast::<u8>()).add(offset) as *const usize)
    };
    field(INLINE_ALLOC_LAYOUT.block_end) - field(INLINE_ALLOC_LAYOUT.bump_top)
}

/// One inline placement of each kind raises its site's count by one, and the
/// program's total and its kind's figure by that placement, whether the tip
/// had room or the runtime made it.
#[test]
fn one_inline_placement_is_one_count_at_its_site_and_one_in_the_total() {
    for (kind, size) in PLACED {
        for tip in [Tip::Roomy, Tip::Full] {
            let (mut process, code, _backend) = one_placement(kind, size);
            if let Tip::Full = tip {
                while tip_room(&process) >= size {
                    process.heap.alloc(16);
                }
            }
            let mut expected = process.node.alloc_stats();
            expected.add(
                kind,
                AllocStat {
                    allocs: 1,
                    bytes: size as u64,
                },
            );

            unsafe { pinned_abi::call1(code, &mut process, 0) };

            let sites = process.node.alloc_site_counts();
            let compiled: Vec<_> = sites.iter().filter(|site| site.function == FUNCTION).collect();
            assert_eq!(compiled.len(), 1, "{kind:?} on a {tip:?} tip: one site placed");
            assert_eq!(
                (compiled[0].kind, compiled[0].placed),
                (
                    kind,
                    AllocStat {
                        allocs: 1,
                        bytes: size as u64
                    }
                ),
                "{kind:?} on a {tip:?} tip"
            );
            let figure: HeapAllocStats = process.node.alloc_stats();
            assert_eq!(
                figure, expected,
                "{kind:?} on a {tip:?} tip: only its kind and the total rose"
            );
        }
    }
}
