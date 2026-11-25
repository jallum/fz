use super::*;
use crate::process::Node;
use crate::reuse_site::{Retention, ReuseSiteCount, RuntimeReuseSite};

fn frame(bytes: u32, function: &str) -> Site {
    Site::Alloc(AllocSite {
        kind: HeapAllocKind::Continuation,
        bytes,
        function: function.to_owned(),
    })
}

fn reuse(kind: ReuseKind, function: &str) -> Site {
    Site::Reuse(ReuseSite {
        kind,
        function: function.to_owned(),
    })
}

/// A linked program carries its site table as bytes; what the runtime decodes
/// is what the compiler encoded, allocation and reuse sites alike.
#[test]
fn the_encoded_table_decodes_to_the_same_sites() {
    let sites = vec![
        frame(32, "Main.loop/2"),
        reuse(ReuseKind::Tuple, "Main.put/2"),
        frame(4096, ""),
        reuse(ReuseKind::List, "Main.reverse/2"),
    ];

    assert_eq!(decode_sites(&encode_sites(&sites)), Ok(sites));
}

/// A truncated table is an error the loader reports, never a partial table.
#[test]
fn a_truncated_table_is_refused() {
    let encoded = encode_sites(&[frame(32, "Main.loop/2")]);

    assert!(decode_sites(&encoded[..encoded.len() - 1]).is_err());
}

/// An allocation site owns one counter word and a reuse site two, so each
/// reads its own words wherever it stands in the table.
#[test]
fn each_site_reads_its_own_counter_words() {
    let mut counts = [3u64, 5, 7, 11, 0];
    let table = unsafe {
        SiteTable::new(
            vec![frame(32, "a"), reuse(ReuseKind::List, "b"), frame(48, "c")],
            counts.as_mut_ptr(),
        )
    };

    let allocations: Vec<_> = table
        .allocations()
        .map(|(site, n)| (site.function.as_str(), n))
        .collect();
    let reuses: Vec<_> = table
        .reuses()
        .map(|(site, stat)| (site.function.as_str(), stat))
        .collect();

    assert_eq!(allocations, [("a", 3), ("c", 11)]);
    assert_eq!(reuses, [("b", ReuseStat { hits: 5, misses: 7 })]);
}

/// A program's retention figure sums its compiled and runtime reuse sites by
/// kind, and a tuple copy counts with the structs.
#[test]
fn the_struct_figure_includes_tuple_copies() {
    let node = Node::empty();
    let mut counts = [4u64, 1];
    node.register_sites(unsafe {
        SiteTable::new(vec![reuse(ReuseKind::Struct, "Main.update/1")], counts.as_mut_ptr())
    });
    node.runtime_reuses.miss(RuntimeReuseSite::TupleCopy);
    node.runtime_reuses.hit(RuntimeReuseSite::ListReuse);

    assert_eq!(
        node.retention_stats(),
        Retention {
            list: ReuseStat { hits: 1, misses: 0 },
            struct_: ReuseStat { hits: 4, misses: 2 },
        }
    );
    assert_eq!(node.reuse_stats(ReuseKind::Tuple), ReuseStat { hits: 0, misses: 1 });
    assert_eq!(
        node.reuse_site_counts().first(),
        Some(&ReuseSiteCount {
            function: "Main.update/1".to_owned(),
            kind: ReuseKind::Struct,
            reused: ReuseStat { hits: 4, misses: 1 },
        })
    );
}
