use super::HashMap;
use std::hash::BuildHasher;

#[test]
fn tables_built_the_same_way_do_not_share_a_seed() {
    // A shared seed would let code depend on iteration order without any test
    // noticing: two tables with the same inserts would always iterate alike.
    let first: HashMap<u32, u32> = HashMap::default();
    let second: HashMap<u32, u32> = HashMap::default();
    let probe = 0xdead_beef_u64;
    assert_ne!(
        first.hasher().hash_one(probe),
        second.hasher().hash_one(probe),
        "two tables built the same way hash with the same seed"
    );
}
