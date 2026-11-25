use super::*;
use crate::process::Node;
use crate::site_table::{Site, SiteTable};

fn frame(bytes: u32, function: &str) -> Site {
    Site::Alloc(AllocSite {
        kind: HeapAllocKind::Continuation,
        bytes,
        function: function.to_owned(),
    })
}

/// A program's report lists each site that placed something, compiled sites
/// with their fixed size times their counter and runtime sites with the bytes
/// they recorded; a site that placed nothing is not listed.
#[test]
fn a_node_reports_each_site_that_placed_an_object() {
    let node = Node::empty();
    let mut counts = [3u64, 0];
    node.register_sites(unsafe { SiteTable::new(vec![frame(32, "main/0"), frame(48, "loop/2")], counts.as_mut_ptr()) });
    node.runtime_allocs.record(RuntimeAllocSite::MapNode, 64);
    node.runtime_allocs.record(RuntimeAllocSite::MapNode, 96);

    assert_eq!(
        node.alloc_site_counts(),
        [
            AllocSiteCount {
                function: "main/0".to_owned(),
                kind: HeapAllocKind::Continuation,
                placed: AllocStat { allocs: 3, bytes: 96 },
            },
            AllocSiteCount {
                function: "runtime::alloc_map_node".to_owned(),
                kind: HeapAllocKind::Map,
                placed: AllocStat { allocs: 2, bytes: 160 },
            },
        ]
    );
}
