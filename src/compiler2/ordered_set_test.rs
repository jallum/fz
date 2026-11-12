use super::*;

/// The whole point: iteration follows the producer's order, and a repeat
/// insertion neither duplicates the value nor moves it. Membership order is
/// first-registration order, so a later re-registration cannot reshuffle
/// what an earlier one established (fz-f98.19).
#[test]
fn iteration_follows_first_registration_order() {
    let mut set = OrderedSet::default();
    for value in ["c", "a", "b", "a", "c"] {
        set.insert(value);
    }

    assert_eq!(
        set.iter().copied().collect::<Vec<_>>(),
        vec!["c", "a", "b"],
        "iteration is registration order, and re-registering does not move a member",
    );
}

#[test]
fn removing_a_member_leaves_the_rest_in_order() {
    let mut set: OrderedSet<&str> = ["c", "a", "b"].into_iter().collect();
    set.remove(&"a");

    assert!(!set.contains(&"a"), "a removed member is gone");
    assert_eq!(
        set.iter().copied().collect::<Vec<_>>(),
        vec!["c", "b"],
        "removal closes the gap without disturbing the surviving order",
    );
}

/// Consuming a set hands back the same sequence borrowed iteration gives, so
/// a caller that is done with the set can take its elements by value without
/// changing wake or emission order.
#[test]
fn consuming_a_set_yields_insertion_order_like_iter() {
    let set: OrderedSet<String> = ["c", "a", "b", "a", "c"].into_iter().map(String::from).collect();
    let borrowed: Vec<String> = set.iter().cloned().collect();

    let owned: Vec<String> = set.into_iter().collect();

    assert_eq!(
        owned,
        vec!["c", "a", "b"],
        "owned iteration is first-registration order"
    );
    assert_eq!(owned, borrowed, "owned and borrowed iteration agree");
}
