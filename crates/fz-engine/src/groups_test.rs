use super::Groups;
use crate::fast_hash::HashMap;
use crate::waits::StandingWaits;

fn waits(edges: &[u32]) -> StandingWaits<&'static str, u32> {
    edges
        .iter()
        .map(|producer| (crate::facts::FactUse::current("f"), Some(*producer)))
        .collect()
}

#[test]
fn a_job_with_no_group_is_its_own_members() {
    let groups = Groups::<u32>::default();
    assert_eq!(groups.members_or_self(&7), [7]);
    assert!(!groups.is_in_open_group(&7));
}

#[test]
fn a_group_is_open_from_formation_and_closes_only_when_idle() {
    let mut groups = Groups::<u32>::default();
    groups.join([1, 2]);
    assert!(groups.is_in_open_group(&1));

    assert_eq!(
        groups.close_if_idle(&1, |member| *member == 2),
        None,
        "member 2 is active"
    );
    assert!(groups.is_in_open_group(&2));

    assert_eq!(groups.close_if_idle(&1, |_| false), groups.group_of(&2));
    assert!(!groups.is_in_open_group(&1));
    assert_eq!(
        groups.close_if_idle(&1, |_| false),
        None,
        "a closed group has nothing to close"
    );

    groups.reopen(&2);
    assert!(groups.is_in_open_group(&1), "a member is group-wide");
}

#[test]
fn joining_a_member_of_a_closed_group_opens_the_merged_group() {
    let mut groups = Groups::<u32>::default();
    groups.join([1, 2]);
    groups.close_if_idle(&1, |_| false);
    groups.join([2, 3]);
    assert_eq!(groups.group_of(&1), groups.group_of(&3));
    assert!(groups.is_in_open_group(&3));
}

#[test]
fn a_wait_path_enters_a_foreign_group_whole() {
    let mut groups = Groups::<u32>::default();
    groups.join([2, 3]);
    let owned: HashMap<u32, StandingWaits<&'static str, u32>> =
        [(1, waits(&[2])), (3, waits(&[4])), (2, waits(&[])), (4, waits(&[]))]
            .into_iter()
            .collect();
    let lookup = |job: &u32| &owned[job];

    let path = groups
        .wait_path(&[1], &4, lookup)
        .expect("1 reaches 4 through the group");
    assert!(
        path.contains(&1) && path.contains(&3),
        "the path runs 1, then the group member that waits on 4: {path:?}"
    );
    assert_eq!(groups.wait_path(&[4], &1, lookup), None, "waits do not run backwards");
}
