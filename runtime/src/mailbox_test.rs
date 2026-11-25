//! A mailbox keeps its messages in arrival order, outside the heap, and a take
//! brings a message into the heap.

use super::*;
use crate::any_value::{AnyValue, AnyValueRef};
use crate::heap::SchemaRegistry;
use crate::process::Process;
use crate::sched::{gift_copy_one, self_send};
use std::cell::RefCell;
use std::rc::Rc;

fn process() -> Process {
    Process::new(Rc::new(RefCell::new(SchemaRegistry::new())))
}

fn list_of(heap: &mut Heap, n: i64) -> AnyValueRef {
    heap.alloc_list_cons_int(n, AnyValueRef::empty_list())
        .expect("list ref")
}

/// A message `[n]` as a sender's gift: the message and the segment holding it.
fn gifted_list(sender: &mut Heap, n: i64) -> (Stored, GiftSegment) {
    let message = Stored::of_ref(list_of(sender, n));
    let (segment, copy) = gift_copy_one(sender, message);
    (copy, segment)
}

fn head(heap: &Heap, message: Stored) -> i64 {
    heap.read_list_head_ref(message.heap_ref())
        .expect("head")
        .load_int()
        .expect("int")
}

fn heads(process: &Process) -> Vec<i64> {
    process.mailbox.messages().map(|m| head(&process.heap, m)).collect()
}

#[test]
fn messages_stay_in_arrival_order_whether_another_process_or_the_receiver_sent_them() {
    let mut sender = process();
    let mut receiver = process();
    let own = Stored::of_ref(list_of(&mut receiver.heap, 1));
    self_send(&mut receiver, own);
    let (second, segment) = gifted_list(&mut sender.heap, 2);
    receiver.mailbox.push(second, segment);
    let own = Stored::of_ref(list_of(&mut receiver.heap, 3));
    self_send(&mut receiver, own);

    assert_eq!(heads(&receiver), vec![1, 2, 3]);
}

#[test]
fn a_self_sent_message_is_a_copy_that_waits_outside_the_heap() {
    let mut receiver = process();
    let own = Stored::of_ref(list_of(&mut receiver.heap, 7));
    let young_before = receiver.heap.young_bytes();

    self_send(&mut receiver, own);

    let waiting = receiver.mailbox.front().expect("the message");
    let waiting_addr = waiting.heap_ref().list_addr().expect("list addr");
    assert_ne!(
        waiting_addr,
        own.heap_ref().list_addr().expect("list addr"),
        "the message was copied"
    );
    assert!(!receiver.heap.contains_heap_addr(waiting_addr));
    assert_eq!(
        receiver.heap.young_bytes(),
        young_before,
        "the copy is not the heap's bytes yet"
    );
}

#[test]
fn taking_a_message_brings_its_block_into_the_heap_as_young_bytes() {
    let mut sender = process();
    let mut receiver = process();
    let (message, segment) = gifted_list(&mut sender.heap, 9);
    let addr = message.heap_ref().list_addr().expect("list addr");
    receiver.mailbox.push(message, segment);
    assert!(!receiver.heap.contains_heap_addr(addr));
    let young_before = receiver.heap.young_bytes();

    receiver.mailbox.take(0, &mut receiver.heap);

    assert!(receiver.mailbox.is_empty());
    assert!(receiver.heap.contains_heap_addr(addr));
    assert_eq!(receiver.heap.young_bytes(), young_before + 16);
    assert_eq!(receiver.heap.live_baseline, 0, "the taken message is young, not old");
}

#[test]
fn taking_from_the_middle_leaves_the_others_in_order() {
    let mut sender = process();
    let mut receiver = process();
    for n in 1..=3 {
        let (message, segment) = gifted_list(&mut sender.heap, n);
        receiver.mailbox.push(message, segment);
    }

    receiver.mailbox.take(1, &mut receiver.heap);

    assert_eq!(heads(&receiver), vec![1, 3]);
}

#[test]
fn the_mailbox_is_never_a_collection_root() {
    let mut sender = process();
    let mut receiver = process();
    let own = Stored::of_ref(list_of(&mut receiver.heap, 1));
    self_send(&mut receiver, own);
    let (message, segment) = gifted_list(&mut sender.heap, 2);
    receiver.mailbox.push(message, segment);
    let addrs: Vec<_> = receiver.mailbox.messages().map(|m| m.heap_ref().list_addr()).collect();

    let stats = receiver.collect_stats(&mut []);

    assert_eq!(stats.copied_bytes, 0, "no message was reached");
    let after: Vec<_> = receiver.mailbox.messages().map(|m| m.heap_ref().list_addr()).collect();
    assert_eq!(after, addrs, "every message stayed where it was");
    assert_eq!(heads(&receiver), vec![1, 2]);
}

#[test]
fn a_message_taken_after_a_collection_is_collected_by_the_next_one() {
    let mut sender = process();
    let mut receiver = process();
    let (message, segment) = gifted_list(&mut sender.heap, 2);
    receiver.mailbox.push(message, segment);
    receiver.collect_stats(&mut []);

    receiver.mailbox.take(0, &mut receiver.heap);
    let stats = receiver.collect_stats(&mut []);

    assert_eq!(stats.received_bytes, 16);
    assert_eq!(stats.copied_bytes, 0, "the taken message was dead at the collection");
    assert_eq!(receiver.heap.bytes_used(), 0);
}

#[test]
fn first_match_answers_the_oldest_message_the_probe_accepts_with_its_index() {
    let mut sender = process();
    let mut receiver = process();
    for n in [1, 2, 3, 3] {
        let (message, segment) = gifted_list(&mut sender.heap, n);
        receiver.mailbox.push(message, segment);
    }

    let found = receiver
        .mailbox
        .first_match::<_, ()>(|m| Ok((head(&receiver.heap, m) == 3).then_some("three")));

    assert_eq!(found, Ok(Some((2, "three"))));
}

#[test]
fn first_match_stops_at_the_first_error() {
    let mut sender = process();
    let mut receiver = process();
    for n in [1, 2] {
        let (message, segment) = gifted_list(&mut sender.heap, n);
        receiver.mailbox.push(message, segment);
    }
    let mut probed = 0;

    let found = receiver.mailbox.first_match::<(), _>(|_| {
        probed += 1;
        Err("matcher failed")
    });

    assert_eq!(found, Err("matcher failed"));
    assert_eq!(probed, 1);
}

#[test]
fn a_sent_number_waits_in_the_mailbox_without_a_block_and_a_collection_receives_nothing() {
    let mut sender = process();
    let mut receiver = process();
    let number = Stored::of(AnyValue::Int(41));
    let (segment, copy) = gift_copy_one(&mut sender.heap, number);
    receiver.mailbox.push(copy, segment);

    assert_eq!(receiver.mailbox.front(), Some(number));
    receiver.mailbox.take(0, &mut receiver.heap);
    let stats = receiver.collect_stats(&mut []);

    assert_eq!(stats.received_bytes, 0, "a number's gift holds no block to graft");
    assert_eq!(receiver.heap.young_bytes(), 0);
}
