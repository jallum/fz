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

/// Past the point where the set indexes its members, the answers it gives are
/// the order vector's: `insert` reports whether the member was new, `contains`
/// and `remove` see exactly the members the iteration yields, and iteration
/// stays in insertion order whatever was removed or re-inserted.
#[test]
fn an_indexed_set_agrees_with_its_order() {
    let mut set = OrderedSet::default();
    let mut order: Vec<u32> = Vec::new();
    for member in (0..40).map(|n| (n * 7) % 31) {
        assert_eq!(
            set.insert(member),
            !order.contains(&member),
            "insert reports novelty of {member}"
        );
        if !order.contains(&member) {
            order.push(member);
        }
    }
    for member in [7, 0, 30, 99] {
        set.remove(&member);
        order.retain(|existing| *existing != member);
        assert!(!set.contains(&member), "{member} is gone after removal");
    }
    assert!(set.insert(7), "a removed member is new again");
    order.push(7);

    for member in 0..40 {
        assert_eq!(set.contains(&member), order.contains(&member), "membership of {member}");
    }
    assert_eq!(
        set.iter().copied().collect::<Vec<_>>(),
        order,
        "iteration keeps insertion order"
    );
}

/// Inserting a member that is already present changes nothing and says so, so
/// callers can use the answer to decide whether anything new happened.
#[test]
fn inserting_a_present_member_reports_false_and_changes_nothing() {
    let mut set: OrderedSet<&str> = ["c", "a"].into_iter().collect();

    assert!(!set.insert("c"), "a present member is not inserted again");
    assert!(set.insert("b"), "an absent member is inserted");

    assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec!["c", "a", "b"]);
}
