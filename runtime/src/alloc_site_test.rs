use super::*;
use crate::process::Node;

fn frame(bytes: u32, function: &str) -> AllocSite {
    AllocSite {
        kind: HeapAllocKind::Continuation,
        bytes,
        function: function.to_owned(),
    }
}

/// A program's report lists each site that placed something, compiled sites
/// with their fixed size times their counter and runtime sites with the bytes
/// they recorded; a site that placed nothing is not listed.
#[test]
fn a_node_reports_each_site_that_placed_an_object() {
    let node = Node::empty();
    let mut counts = [3u64, 0];
    node.register_alloc_sites(unsafe {
        AllocSites::new(vec![frame(32, "main/0"), frame(48, "loop/2")], counts.as_mut_ptr())
    });
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

/// A linked program carries its site table as bytes; what the runtime decodes
/// is what the compiler encoded.
#[test]
fn the_encoded_table_decodes_to_the_same_sites() {
    let sites = vec![frame(32, "Main.loop/2"), frame(4096, "")];

    assert_eq!(decode_alloc_sites(&encode_alloc_sites(&sites)), Ok(sites));
}

/// A truncated table is an error the loader reports, never a partial table.
#[test]
fn a_truncated_table_is_refused() {
    let encoded = encode_alloc_sites(&[frame(32, "Main.loop/2")]);

    assert!(decode_alloc_sites(&encoded[..encoded.len() - 1]).is_err());
}
