use super::*;

#[test]
fn ascii_printable_passes() {
    assert!(is_printable_utf8("hello world"));
    assert!(is_printable_utf8(""));
    assert!(is_printable_utf8("/tmp/fz-x5m"));
}

#[test]
fn utf8_non_ascii_passes() {
    assert!(is_printable_utf8("héllo"));
    assert!(is_printable_utf8("日本語"));
}

#[test]
fn whitelisted_controls_pass() {
    assert!(is_printable_utf8("line\nbreak"));
    assert!(is_printable_utf8("tab\tseparated"));
    assert!(is_printable_utf8("\r\n"));
}

#[test]
fn other_controls_fail() {
    assert!(!is_printable_utf8("\x01"));
    assert!(!is_printable_utf8("\x00"));
    assert!(!is_printable_utf8("\x7f"));
    assert!(!is_printable_utf8("hello\x01world"));
}

#[test]
fn escape_round_trips_through_display() {
    assert_eq!(escape_for_display("a\nb"), "a\\nb");
    assert_eq!(escape_for_display("\"quoted\""), "\\\"quoted\\\"");
    assert_eq!(escape_for_display("plain"), "plain");
    assert_eq!(escape_for_display("a\tb\rc"), "a\\tb\\rc");
}

#[test]
fn escape_covers_every_control_elixir_names() {
    assert_eq!(escape_for_display("\x07\x08\x0b\x0c\x1b"), "\\a\\b\\v\\f\\e");
    assert_eq!(escape_for_display("#{x} # {"), "\\#{x} # {");
}

mod budget {
    use super::super::{Limit, render_with_limit};
    use crate::any_value::{AnyValue, EMPTY_LIST_BITS, ValueKind};
    use crate::heap::{Schema, SchemaRegistry};
    use crate::process::Process;
    use std::cell::RefCell;
    use std::rc::Rc;

    /// A process whose heap the tests build values on.
    struct Built {
        process: Box<Process>,
    }

    impl Built {
        fn new() -> Self {
            let process = Box::new(Process::new(Rc::new(RefCell::new(SchemaRegistry::new()))));
            // A linked module seeds the reserved ids first; a bare process does not.
            for reserved in ["nil", "true", "false"] {
                process.node.intern_atom(reserved);
            }
            Self { process }
        }

        fn atom(&self, name: &str) -> AnyValue {
            AnyValue::atom(self.process.node.intern_atom(name))
        }

        fn int(&self, n: i64) -> AnyValue {
            AnyValue::int(n)
        }

        fn text(&mut self, text: &str) -> AnyValue {
            self.process
                .heap
                .alloc_bitstring(text.as_bytes(), 8 * text.len() as u64)
        }

        fn bits(&mut self, bytes: &[u8], bit_len: u64) -> AnyValue {
            self.process.heap.alloc_bitstring(bytes, bit_len)
        }

        fn list(&mut self, items: &[AnyValue]) -> AnyValue {
            let bits = items.iter().rev().fold(EMPTY_LIST_BITS, |tail, item| {
                self.process.heap.alloc_list_cons_slot(*item, tail)
            });
            AnyValue::decode_tagged_heap_bits(bits).unwrap_or(AnyValue::empty_list())
        }

        fn chars(&mut self, codes: &[i64]) -> AnyValue {
            let items: Vec<AnyValue> = codes.iter().map(|c| AnyValue::int(*c)).collect();
            self.list(&items)
        }

        fn tuple(&mut self, items: &[AnyValue]) -> AnyValue {
            let schema = self.process.heap.register_schema(Schema::tuple_of_arity(items.len()));
            let p = self.process.heap.alloc_struct(schema);
            for (index, item) in items.iter().enumerate() {
                unsafe { self.process.heap.write_field_slot(p, 8 * index as u32, *item) };
            }
            AnyValue::heap_ptr(p, ValueKind::STRUCT)
        }

        fn map(&mut self, entries: &[(AnyValue, AnyValue)]) -> AnyValue {
            let bits = self.process.heap.alloc_map_slots(entries);
            AnyValue::decode_tagged_heap_bits(bits).expect("a map value")
        }

        fn pair(&mut self, key: &str, value: AnyValue) -> AnyValue {
            let key = self.atom(key);
            self.tuple(&[key, value])
        }

        fn show(&mut self, value: AnyValue, limit: Limit) -> String {
            render_with_limit(&mut *self.process, value, limit)
        }

        fn show_default(&mut self, value: AnyValue) -> String {
            super::super::render_value(&mut *self.process, value)
        }
    }

    use Limit::{Count, Infinity};

    fn ints(b: &Built, ns: &[i64]) -> Vec<AnyValue> {
        ns.iter().map(|n| b.int(*n)).collect()
    }

    #[test]
    fn each_list_element_costs_one_and_the_rest_is_an_ellipsis() {
        let mut b = Built::new();
        let items = ints(&b, &[1, 2, 3, 4]);
        let list = b.list(&items);
        assert_eq!(b.show(list, Count(3)), "[1, 2, 3, ...]");
        assert_eq!(b.show(list, Count(4)), "[1, 2, 3, 4]");
        assert_eq!(b.show(list, Count(0)), "[...]");
        assert_eq!(b.show(list, Infinity), "[1, 2, 3, 4]");
    }

    #[test]
    fn empty_containers_never_show_an_ellipsis() {
        let mut b = Built::new();
        let (list, tuple, map) = (b.list(&[]), b.tuple(&[]), b.map(&[]));
        assert_eq!(b.show(list, Count(0)), "[]");
        assert_eq!(b.show(tuple, Count(0)), "{}");
        assert_eq!(b.show(map, Count(0)), "%{}");
    }

    #[test]
    fn a_nested_container_spends_from_the_same_budget() {
        let mut b = Built::new();
        let (first, second) = (ints(&b, &[1, 2, 3]), ints(&b, &[4]));
        let (first, second) = (b.list(&first), b.list(&second));
        let outer = b.list(&[first, second]);
        assert_eq!(b.show(outer, Count(4)), "[[1, 2, 3], ...]");
    }

    #[test]
    fn a_tuple_spends_per_field() {
        let mut b = Built::new();
        let fields = ints(&b, &[1, 2, 3]);
        let tuple = b.tuple(&fields);
        assert_eq!(b.show(tuple, Count(2)), "{1, 2, ...}");
        assert_eq!(b.show(tuple, Count(0)), "{...}");
    }

    #[test]
    fn a_map_entry_costs_one_and_its_key_and_value_spend_after_it() {
        let mut b = Built::new();
        let (k1, v1, k2, v2) = (b.text("a"), b.int(1), b.text("b"), b.int(2));
        let map = b.map(&[(k1, v1), (k2, v2)]);
        assert_eq!(b.show(map, Count(1)), "%{\"a\" => 1, ...}");
        assert_eq!(b.show(map, Count(0)), "%{...}");

        let (key, value) = (ints(&b, &[1, 2, 3]), ints(&b, &[4, 5, 6]));
        let (key, value) = (b.list(&key), b.list(&value));
        let nested = b.map(&[(key, value)]);
        assert_eq!(b.show(nested, Count(4)), "%{[1, 2, 3] => [...]}");
    }

    #[test]
    fn nested_maps_hand_the_remaining_budget_back_out() {
        let mut b = Built::new();
        let inner: Vec<(AnyValue, AnyValue)> = ["a", "b", "c", "d", "e", "f"]
            .iter()
            .enumerate()
            .map(|(i, k)| (b.text(k), b.int(i as i64 + 1)))
            .collect();
        let inner = b.map(&inner);
        let (metadata, x, one) = (b.text("metadata"), b.text("x"), b.int(1));
        let outer = b.map(&[(metadata, inner), (x, one)]);
        assert_eq!(
            b.show(outer, Count(6)),
            "%{\"metadata\" => %{\"a\" => 1, \"b\" => 2, \"c\" => 3, \"d\" => 4, \"e\" => 5, ...}, ...}"
        );
    }

    #[test]
    fn a_keyword_list_spends_per_entry() {
        let mut b = Built::new();
        let (one, two) = (b.int(1), b.int(2));
        let entries = [b.pair("a", one), b.pair("b", two)];
        let list = b.list(&entries);
        assert_eq!(b.show(list, Count(1)), "[a: 1, ...]");
        assert_eq!(b.show(list, Count(0)), "[...]");
    }

    #[test]
    fn bitstrings_charge_a_byte_each_and_print_trailing_bits_with_size() {
        let mut b = Built::new();
        let bits = b.bits(&[1, 2, 3 << 4], 20);
        assert_eq!(b.show(bits, Count(100)), "<<1, 2, 3::size(4)>>");
        assert_eq!(b.show(bits, Count(2)), "<<1, 2, ...>>");
        assert_eq!(b.show(bits, Count(0)), "<<...>>");
        let bytes = b.bits(&[1, 2, 255], 24);
        assert_eq!(b.show(bytes, Count(3)), "<<1, 2, 255>>");
    }

    #[test]
    fn printable_strings_ignore_the_limit() {
        let mut b = Built::new();
        let text = b.text("abcdef");
        assert_eq!(b.show(text, Count(1)), "\"abcdef\"");
        assert_eq!(b.show(text, Count(0)), "\"abcdef\"");
    }

    #[test]
    fn scalars_cost_nothing_of_their_own() {
        let mut b = Built::new();
        let atom = b.atom("ok");
        let items = [b.int(7), atom, AnyValue::float(1.5)];
        let list = b.list(&items);
        assert_eq!(b.show(list, Count(3)), "[7, :ok, 1.5]");
        let seven = b.int(7);
        assert_eq!(b.show(seven, Count(0)), "7");
    }

    #[test]
    fn the_default_entry_means_a_limit_of_one_hundred() {
        let mut b = Built::new();
        let items: Vec<AnyValue> = (1..=101).map(|n| b.int(n)).collect();
        let list = b.list(&items);
        let shown = b.show_default(list);
        assert!(shown.ends_with("99, 100, ...]"), "{shown}");
        assert_eq!(shown, b.show(list, Count(100)));
    }

    #[test]
    fn atoms_spell_as_macro_inspect_atom_does() {
        let mut b = Built::new();
        let cases = [
            ("name", ":name"),
            ("ok?", ":ok?"),
            ("save!", ":save!"),
            ("_hidden", ":_hidden"),
            ("élan", ":élan"),
            ("1abc", ":\"1abc\""),
            ("foo bar", ":\"foo bar\""),
            ("a?b", ":\"a?b\""),
            ("a!?", ":\"a!?\""),
            ("+", ":+"),
            ("<>", ":<>"),
            ("|>", ":|>"),
            ("%{}", ":%{}"),
            ("...", ":..."),
            ("when", ":when"),
            ("<|>", ":\"<|>\""),
            ("^^^", ":\"^^^\""),
            ("=>", ":\"=>\""),
            ("::", ":\"::\""),
            ("\\\\", ":\\\\"),
            ("a\"b", ":\"a\\\"b\""),
            ("Elixir.Foo.Bar", "Foo.Bar"),
            ("Elixir.foo", ":\"Elixir.foo\""),
            ("nil", "nil"),
            ("true", "true"),
            ("false", "false"),
        ];
        for (name, expected) in cases {
            let atom = b.atom(name);
            assert_eq!(b.show_default(atom), expected, "atom {name:?}");
        }
    }

    #[test]
    fn keyword_keys_spell_as_macro_inspect_atom_key_does() {
        let mut b = Built::new();
        let cases = [
            ("name", "[name: 1]"),
            ("foo bar", "[\"foo bar\": 1]"),
            ("+", "[+: 1]"),
            ("ok?", "[ok?: 1]"),
            ("1abc", "[\"1abc\": 1]"),
            ("<|>", "[\"<|>\": 1]"),
        ];
        for (key, expected) in cases {
            let one = b.int(1);
            let entry = b.pair(key, one);
            let list = b.list(&[entry]);
            assert_eq!(b.show_default(list), expected, "key {key:?}");
        }
    }

    #[test]
    fn an_alias_key_keeps_a_list_and_a_map_out_of_keyword_style() {
        let mut b = Built::new();
        let (alias, one) = (b.atom("Elixir.Foo"), b.int(1));
        let entry = b.tuple(&[alias, one]);
        let list = b.list(&[entry]);
        assert_eq!(b.show_default(list), "[{Foo, 1}]");
        let map = b.map(&[(alias, one)]);
        assert_eq!(b.show_default(map), "%{Foo => 1}");
    }

    #[test]
    fn a_map_with_only_atom_keys_prints_in_keyword_style() {
        let mut b = Built::new();
        let (a, one, foo) = (b.atom("a"), b.int(1), b.atom("foo bar"));
        let map = b.map(&[(a, one)]);
        assert_eq!(b.show_default(map), "%{a: 1}");
        let quoted = b.map(&[(foo, one)]);
        assert_eq!(b.show_default(quoted), "%{\"foo bar\": 1}");
        let (text, two) = (b.text("k"), b.int(2));
        let mixed = b.map(&[(a, one), (text, two)]);
        assert_eq!(b.show_default(mixed), "%{:a => 1, \"k\" => 2}");
    }

    #[test]
    fn a_list_of_non_atom_keyed_pairs_is_not_a_keyword_list() {
        let mut b = Built::new();
        let (one, two) = (b.int(1), b.int(2));
        let entry = b.pair("a", one);
        let odd = b.tuple(&[one, two]);
        let list = b.list(&[entry, odd]);
        assert_eq!(b.show_default(list), "[{:a, 1}, {1, 2}]");
    }

    #[test]
    fn charlists_follow_ascii_printable() {
        let mut b = Built::new();
        let cases: [(&[i64], &str); 14] = [
            (&[104, 105], "~c\"hi\""),
            (&[7, 104], "~c\"\\ah\""),
            (&[27], "~c\"\\e\""),
            (&[7, 13, 32, 126], "~c\"\\a\\r ~\""),
            (&[34, 92], "~c\"\\\"\\\\\""),
            (&[35, 123], "~c\"\\#{\""),
            (&[10, 9], "~c\"\\n\\t\""),
            (&[6], "[6]"),
            (&[14], "[14]"),
            (&[0], "[0]"),
            (&[128], "[128]"),
            (&[233], "[233]"),
            (&[126, 127], "[126, 127]"),
            (&[31], "[31]"),
        ];
        for (codes, expected) in cases {
            let list = b.chars(codes);
            assert_eq!(b.show_default(list), expected, "codes {codes:?}");
        }
        let empty = b.list(&[]);
        assert_eq!(b.show_default(empty), "[]");
    }

    #[test]
    fn a_charlist_costs_nothing_inside_a_container() {
        let mut b = Built::new();
        let (chars, one) = (b.chars(&[104, 105]), b.int(1));
        let list = b.list(&[chars, one]);
        assert_eq!(b.show(list, Count(2)), "[~c\"hi\", 1]");
    }

    #[test]
    fn the_limit_option_is_read_from_a_checked_keyword_list() {
        let mut b = Built::new();
        let proc: *mut Process = &mut *b.process;
        let (three, ten, infinity) = (b.int(3), b.int(10), b.atom("infinity"));
        let none = b.list(&[]);
        assert_eq!(Limit::from_options(proc, none), Limit::DEFAULT);
        let entry = b.pair("limit", three);
        let one = b.list(&[entry]);
        assert_eq!(Limit::from_options(proc, one), Count(3));
        let (first, second) = (b.pair("limit", three), b.pair("limit", ten));
        let twice = b.list(&[first, second]);
        assert_eq!(Limit::from_options(proc, twice), Count(10), "the last limit wins");
        let entry = b.pair("limit", infinity);
        let unbounded = b.list(&[entry]);
        assert_eq!(Limit::from_options(proc, unbounded), Infinity);
    }
}
