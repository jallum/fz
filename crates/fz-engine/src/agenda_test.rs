use super::Agenda;

#[test]
fn duplicate_demand_preserves_fifo_position() {
    let mut agenda = Agenda::new();
    for job in [2, 1, 3] {
        assert!(agenda.enqueue(job));
    }
    assert!(!agenda.enqueue(1));
    assert_eq!(agenda.pop(), Some(2));
    assert!(agenda.enqueue(2));
    for expected in [1, 3, 2] {
        assert_eq!(agenda.pop(), Some(expected));
    }
    assert_eq!(agenda.pop(), None);
    assert!(agenda.is_empty());
}
