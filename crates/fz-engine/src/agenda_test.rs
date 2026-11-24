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

#[cfg(feature = "pop_order")]
mod seeded_order {
    use super::Agenda;
    use crate::pop_order::{PopOrder, with};

    fn drain(order: PopOrder, jobs: u32) -> Vec<u32> {
        with(order, || {
            let mut agenda = Agenda::new();
            for job in 0..jobs {
                agenda.enqueue(job);
            }
            std::iter::from_fn(|| agenda.pop()).collect()
        })
    }

    #[test]
    fn a_seed_replays_the_same_pop_sequence() {
        assert_eq!(drain(PopOrder::Seeded(7), 32), drain(PopOrder::Seeded(7), 32));
    }

    #[test]
    fn seed_zero_still_shuffles() {
        assert_ne!(drain(PopOrder::Seeded(0), 32), (0..32).collect::<Vec<_>>());
    }

    #[test]
    fn different_seeds_pop_in_different_sequences() {
        let sequences: Vec<_> = (1..=8).map(|seed| drain(PopOrder::Seeded(seed), 32)).collect();
        for (i, a) in sequences.iter().enumerate() {
            for b in &sequences[i + 1..] {
                assert_ne!(a, b);
            }
        }
    }

    #[test]
    fn a_seeded_drain_pops_every_queued_job_exactly_once() {
        for seed in 0..16 {
            let mut popped = drain(PopOrder::Seeded(seed), 64);
            popped.sort_unstable();
            assert_eq!(popped, (0..64).collect::<Vec<_>>(), "seed {seed}");
        }
    }

    #[test]
    fn with_restores_the_previous_order_and_its_draw_position() {
        let uninterrupted = drain(PopOrder::Seeded(3), 32);
        let interrupted = with(PopOrder::Seeded(3), || {
            let mut agenda = Agenda::new();
            for job in 0..32u32 {
                agenda.enqueue(job);
            }
            let mut popped = vec![agenda.pop().unwrap()];
            assert_eq!(drain(PopOrder::Seeded(9), 8).len(), 8);
            assert_eq!(drain(PopOrder::Lifo, 3), [2, 1, 0]);
            popped.extend(std::iter::from_fn(|| agenda.pop()));
            popped
        });
        assert_eq!(
            interrupted, uninterrupted,
            "a nested `with` must not disturb the outer seed's draws"
        );
        assert_eq!(
            drain(PopOrder::Fifo, 3),
            [0, 1, 2],
            "after `with` the order is fifo again"
        );
    }
}
