use super::*;

#[test]
fn an_empty_interest_observes_nothing() {
    assert!(!Interest::default().observes(&["fz", "a"]));
}

#[test]
fn a_prefix_observes_every_name_beneath_it_and_nothing_else() {
    let mut interest = Interest::default();
    interest.add(&["fz", "raw"]);

    assert!(interest.observes(&["fz", "raw"]));
    assert!(interest.observes(&["fz", "raw", "event"]));
    assert!(!interest.observes(&["fz"]));
    assert!(!interest.observes(&["fz", "other"]));
    assert!(!interest.observes(&["other", "raw"]));
}

#[test]
fn the_empty_prefix_observes_every_name() {
    let mut interest = Interest::default();
    interest.add(&[]);

    assert!(interest.observes(&[]));
    assert!(interest.observes(&["fz", "a"]));
}

#[test]
fn a_prefix_added_twice_is_observed_until_removed_twice() {
    let mut interest = Interest::default();
    interest.add(&["fz"]);
    interest.add(&["fz"]);

    interest.remove(&["fz"]);
    assert!(interest.observes(&["fz", "a"]));
    interest.remove(&["fz"]);
    assert!(!interest.observes(&["fz", "a"]));
    assert!(interest.is_empty());
}

#[test]
fn removing_a_deep_prefix_leaves_its_siblings_observed() {
    let mut interest = Interest::default();
    interest.add(&["fz", "a", "x"]);
    interest.add(&["fz", "a", "y"]);

    interest.remove(&["fz", "a", "x"]);

    assert!(!interest.observes(&["fz", "a", "x"]));
    assert!(interest.observes(&["fz", "a", "y"]));
}
