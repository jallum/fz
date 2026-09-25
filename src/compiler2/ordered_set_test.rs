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
