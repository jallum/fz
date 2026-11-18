# Differential test: the OtpJSON port in fixtures/01860 against OTP's :json on
# the BEAM. Every outcome is compared with ===, including raw iodata
# structure, the raised class and term, and the error_info annotation of the
# top stack frame. Run from the repository root:
#
#     elixir tools/otp_json/difftest.exs
#
fixture = Path.wildcard("fixtures/01860_*.fz") |> hd()
fixture |> File.read!() |> String.replace(~r/\nMain\.main\(\)\s*\z/, "\n") |> Code.compile_string(fixture)

defmodule Diff do
  def init, do: :persistent_term.put(:dt, {:counters.new(1, []), :counters.new(1, [])})

  def run(label, f_otp, f_ref) do
    {total, _} = :persistent_term.get(:dt); :counters.add(total, 1, 1)
    a = outcome(f_otp)
    b = outcome(f_ref)
    if a !== b do
      {_, fl} = :persistent_term.get(:dt); :counters.add(fl, 1, 1)
      if :counters.get(fl, 1) <= 15 do
        IO.puts("MISMATCH #{inspect(label, limit: 8, printable_limit: 80)}\n  otp: #{inspect(a, limit: 30, printable_limit: 200)}\n  ref: #{inspect(b, limit: 30, printable_limit: 200)}")
      end
    end
    :ok
  end

  def outcome(f) do
    try do
      {:ok, f.()}
    catch
      k, r -> {:raised, k, r, info(__STACKTRACE__)}
    end
  end

  defp info([{_m, _f, _a, loc} | _]) when is_list(loc), do: Keyword.get(loc, :error_info)
  defp info([{_m, _f, _a, loc} | _]), do: loc
  defp info(_), do: nil

  def totals, do: (fn {t, f} -> {:counters.get(t, 1), :counters.get(f, 1)} end).(:persistent_term.get(:dt))
end

defmodule DiffGen do
  import Bitwise
  def num(0), do: Enum.random(["0", "-0", "1", "-1", "10", "123456789", "-98765", "0.5", "-0.0", "1.5e10", "2E-3", "3e+7", "0e0", "1.0E5", "12345678901234567890123", "-170141183460469231731687303715884105728", "0.000001", "1e400", "-1e400", "1.7976931348623157e308", "5e-324", "1E2", "0E+1"])
  def str(0), do: Enum.random(["\"\"", "\"a\"", "\"hello world 12345678 abcdefgh\"", "\"\\n\\t\\\"\\\\\\/\\b\\f\\r\"", "\"\\u00e9\\u20ac\"", "\"\\ud83d\\ude00\"", "\"é€😀日本語\"", "\"\\u0000\"", "\"plain 8bytes+ and more text here\"", "\"x\\u0041y\""])
  def val(depth) do
    cond do
      depth <= 0 -> leaf()
      true ->
        case :rand.uniform(6) do
          1 -> leaf()
          2 -> leaf()
          3 -> "[" <> join(for _ <- 1..:rand.uniform(4), do: ws() <> val(depth - 1) <> ws()) <> "]"
          4 -> "{" <> join(for _ <- 1..:rand.uniform(4), do: ws() <> str(0) <> ws() <> ":" <> ws() <> val(depth - 1) <> ws()) <> "}"
          5 -> "[" <> ws() <> "]"
          6 -> "{" <> ws() <> "}"
        end
    end
  end
  defp leaf do
    case :rand.uniform(5) do
      1 -> num(0)
      2 -> str(0)
      3 -> Enum.random(["true", "false", "null"])
      4 -> num(0)
      5 -> str(0)
    end
  end
  defp join(l), do: Enum.join(l, ",")
  defp ws, do: Enum.random(["", "", " ", "\n", "\t ", "\r\n"])

  # random terms to encode
  def term(depth) do
    case :rand.uniform(if depth <= 0, do: 7, else: 10) do
      1 -> :rand.uniform(1000) - 500
      2 -> Enum.random([0.0, 1.5, -2.25, 1.0e10, 1.0e-10, 123.456, 1.0e22, 5.0e-324, 1.7976931348623157e308])
      3 -> Enum.random([true, false, :null, :foo, :bar_baz, :"é"])
      4 -> Enum.random(["", "abc", "hello world 12345678 abcdefgh", "q\"uote\\back\nnl\ttab", "é€😀日本語", <<0, 1, 31, 127>>, String.duplicate("a", 40) <> "\"" <> String.duplicate("b", 17)])
      5 -> Enum.random([1 <<< 70, -(1 <<< 80)])
      6 -> Enum.random(["", "k", "key with space"])
      7 -> :rand.uniform(9)
      8 -> for _ <- 1..:rand.uniform(4), do: term(depth - 1)
      9 -> Map.new(for(_ <- 1..:rand.uniform(5), do: {key(), term(depth - 1)}))
      10 -> []
    end
  end
  def key, do: Enum.random(["a", "b", "key", :x, :yy, 1, 22, 1.5, "é", "ab\"c", :"é"])
end

import Bitwise
:rand.seed(:exsss, {1, 2, 3})
Diff.init()
d = &Diff.run/3

# ---- decode/1 on fixed edge inputs
edge = [
  "", " ", "1", "-", "-1", "0", "01", "0.", "0.1", "0e", "0e+", "0E5", "1e", "1e+", "1.e1", "1.5", "1.5e", "1.5e+", "1.5e5", "1.5e+5x", "123abc",
  "-0", "-01", "--1", "+1", ".5", "1.5.5", "1e5e5",
  "t", "tr", "tru", "true", "truee", "trux", "f", "fals", "false", "n", "nul", "null", "nulll", "nan",
  "\"", "\"a", "\"abc", "\"abc\"", "\"abc\"x", "\"\\", "\"\\u", "\"\\u1", "\"\\u12", "\"\\u123", "\"\\u1234\"", "\"\\u12G4\"", "\"\\uzzzz\"",
  "\"\\ud800\"", "\"\\ud800\\u", "\"\\ud800\\udc00\"", "\"\\ud800\\u0041\"", "\"\\udc00\"", "\"\\ud800x\"", "\"\\ud83d\\ude00\"", "\"\\ud83d\\ude0", "\"\\uDBFF\\uDFFF\"", "\"\\uD800\\uDBFF\"", "\"\\u0000\\u001f\"",
  "\"\\x\"", "\"\\q\"", "\"\\/\"", "\"a\\nb\"", "\"\n\"", "\"\t\"", "\"\x01\"", "\"\x7f\"",
  "\"é\"", <<"\"", 0xC3>>, <<"\"", 0xC3, 0x28, "\"">>, <<"\"", 0xE2, 0x82>>, <<"\"", 0xE2, 0x82, 0xAC, "\"">>, <<"\"", 0xF0, 0x9F, 0x98>>, <<"\"", 0xF0, 0x9F, 0x98, 0x80, "\"">>,
  <<"\"", 0xC0, 0x80, "\"">>, <<"\"", 0xED, 0xA0, 0x80, "\"">>, <<"\"", 0xF4, 0x90, 0x80, 0x80, "\"">>, <<"\"", 0x80, "\"">>, <<"\"", 0xFF, "\"">>, <<"\"", 0xF8, 0x88, 0x80, 0x80, 0x80, "\"">>,
  <<"\"abcdefgh", 0xC3, 0xA9, "ijklmnopq\"">>, <<"\"abcdefgh\\n", 0xC3, 0xA9, "ijklmnopq", 0xC3>>, <<"\"abcdefgh\\n", 0xC3>>,
  "[", "[]", "[ ]", "[1", "[1,", "[1,]", "[1 2]", "[,1]", "[1,2]", "[1]x", "[[]]", "[[[", "[1,[2,[3,[]]]]", "[1 ", "[1 ,", "[ 1 , 2 ]",
  "{", "{}", "{ }", "{\"a\"", "{\"a\":", "{\"a\":1", "{\"a\":1,", "{\"a\":1,}", "{\"a\" 1}", "{a:1}", "{\"a\":1}", "{\"a\":1,\"a\":2}", "{\"a\":{\"b\":[1,{\"c\":null}]}}", "{1:2}", "{\"a\":1 \"b\":2}", "{\"a\" :", "{\"a\": 1 , ", "{ \"k\" : [ ] }",
  "\u00a0", "\ufeff1", "1 2", "1 ", " 1", "\n1\n", "1\x00", "\x00", "}", "]", ",", ":", "x", "[x]", "{\"a\":x}", "[1,x]", "[tru", "[nul]", "{\"a\":tr", "[\"abc", "[\"abc\\", "[\"abc\\u00", "[\"\\ud800", "{\"a\\u12\"",
  String.duplicate("[", 1000) <> String.duplicate("]", 1000),
  String.duplicate("[", 1000),
  String.duplicate("{\"a\":", 300) <> "1" <> String.duplicate("}", 300),
  "12345678901234567890123456789012345678901234567890", "-12345678901234567890123456789012345678901234567890",
  "1.7976931348623157e309", "1e999", "[1e999]", "-1e999", "1.5e999", "0.1e-999",
  String.duplicate("a", 1000), "\"" <> String.duplicate("a", 1000) <> "\"", "\"" <> String.duplicate("é", 500) <> "\"",
  "\"" <> String.duplicate("a", 7) <> "\\n" <> String.duplicate("b", 9) <> "\"",
  "\"" <> String.duplicate("a", 8) <> "\\u00e9" <> String.duplicate("b", 8) <> "\\ud83d\\ude00\""
]
for i <- edge do
  d.({:decode1, i}, fn -> OtpJSON.decode(i) end, fn -> :json.decode(i) end)
  # decode/3 with defaults, and with every decoder
  d.({:decode3, i}, fn -> OtpJSON.decode(i, :acc0, %{}) end, fn -> :json.decode(i, :acc0, %{}) end)
  decs = %{
    array_start: fn a -> [{:as, a}] end,
    array_push: fn v, acc -> [v | acc] end,
    array_finish: fn acc, old -> {{:arr, :lists.reverse(acc)}, old} end,
    object_start: fn a -> [{:os, a}] end,
    object_push: fn k, v, acc -> [{k, v} | acc] end,
    object_finish: fn acc, old -> {{:obj, :lists.reverse(acc)}, old} end,
    float: fn b -> {:f, b} end,
    integer: fn b -> {:i, b} end,
    string: fn b -> {:s, b} end,
    null: :NULL
  }
  d.({:decode3_all, i}, fn -> OtpJSON.decode(i, 0, decs) end, fn -> :json.decode(i, 0, decs) end)
  d.({:decode3_bad_float, i}, fn -> OtpJSON.decode(i, 0, %{float: fn _ -> raise "x" end}) end, fn -> :json.decode(i, 0, %{float: fn _ -> raise "x" end}) end)
  # every proper prefix
  if byte_size(i) < 120 do
    for n <- 0..byte_size(i) do
      p = binary_part(i, 0, n)
      d.({:prefix, p}, fn -> OtpJSON.decode(p) end, fn -> :json.decode(p) end)
      d.({:prefix3, p}, fn -> OtpJSON.decode(p, :a, %{}) end, fn -> :json.decode(p, :a, %{}) end)
    end
  end
end

# ---- non-binary input
for bad <- [nil, :a, 1, ~c"abc", [1]] do
  d.({:nonbin, bad}, fn -> OtpJSON.decode(bad) end, fn -> :json.decode(bad) end)
  d.({:nonbin3, bad}, fn -> OtpJSON.decode(bad, 0, %{}) end, fn -> :json.decode(bad, 0, %{}) end)
end
# bad decoder arities
for dec <- [%{array_start: fn -> 1 end}, %{bogus: 1}, %{float: :notfun}] do
  d.({:baddec, dec}, fn -> OtpJSON.decode("[1]", 0, dec) end, fn -> :json.decode("[1]", 0, dec) end)
end

# ---- random valid docs, mutations, chunking
for _ <- 1..3000 do
  doc = DiffGen.val(4)
  d.({:rand, doc}, fn -> OtpJSON.decode(doc) end, fn -> :json.decode(doc) end)
  d.({:rand3, doc}, fn -> OtpJSON.decode(doc <> "  trailing", :acc, %{}) end, fn -> :json.decode(doc <> "  trailing", :acc, %{}) end)
  # byte mutations
  if byte_size(doc) > 0 do
    for _ <- 1..3 do
      pos = :rand.uniform(byte_size(doc)) - 1
      b = :rand.uniform(256) - 1
      <<h::binary-size(pos), _, t::binary>> = doc
      m = <<h::binary, b, t::binary>>
      d.({:mut, m}, fn -> OtpJSON.decode(m) end, fn -> :json.decode(m) end)
      d.({:mut3, m}, fn -> OtpJSON.decode(m, :a, %{}) end, fn -> :json.decode(m, :a, %{}) end)
    end
  end
end

# decode_start / decode_continue chunking: all single splits and a few triple splits, states compared raw
chunk = fn mod ->
  fn doc, cuts ->
    pieces = for {a, b} <- Enum.zip([0 | cuts], cuts ++ [byte_size(doc)]), do: binary_part(doc, a, b - a)
    go = fn
      _go, [], st -> mod.decode_continue(:end_of_input, st)
      go, [p | rest], st ->
        case mod.decode_continue(p, st) do
          {:continue, st2} -> go.(go, rest, st2)
          other -> {other, rest}
        end
    end
    [first | more] = pieces
    case mod.decode_start(first, :a, %{}) do
      {:continue, st} -> go.(go, more, st)
      other -> {other, more}
    end
  end
end
co = chunk.(OtpJSON)
cr = chunk.(:json)
docs = Enum.take(edge, 200) |> Enum.filter(&(byte_size(&1) < 200)) |> Kernel.++(for _ <- 1..300, do: DiffGen.val(3))
for doc <- docs, c <- 0..byte_size(doc) do
  d.({:split1, doc, c}, fn -> co.(doc, [c]) end, fn -> cr.(doc, [c]) end)
  d.({:start_state, doc, c}, fn -> OtpJSON.decode_start(binary_part(doc, 0, c), :a, %{}) end, fn -> :json.decode_start(binary_part(doc, 0, c), :a, %{}) end)
end
for doc <- Enum.take(docs, 150) |> Enum.filter(&(byte_size(&1) > 4)), _ <- 1..20 do
  n = byte_size(doc)
  cuts = Enum.sort([:rand.uniform(n), :rand.uniform(n), :rand.uniform(n)])
  d.({:split3, doc, cuts}, fn -> co.(doc, cuts) end, fn -> cr.(doc, cuts) end)
  # byte-at-a-time
  cuts1 = Enum.to_list(1..(n - 1))
  d.({:bytewise, doc}, fn -> co.(doc, cuts1) end, fn -> cr.(doc, cuts1) end)
end
for st <- [:bogus, {1, 2}, nil] do
  d.({:badstate, st}, fn -> OtpJSON.decode_continue("1", st) end, fn -> :json.decode_continue("1", st) end)
  d.({:badstate_eoi, st}, fn -> OtpJSON.decode_continue(:end_of_input, st) end, fn -> :json.decode_continue(:end_of_input, st) end)
end

# ---- encode
e_cases = fn t ->
  d.({:encode, t}, fn -> OtpJSON.encode(t) end, fn -> :json.encode(t) end)
  d.({:format1, t}, fn -> OtpJSON.format(t) end, fn -> :json.format(t) end)
  d.({:format2, t}, fn -> OtpJSON.format(t, %{indent: 4}) end, fn -> :json.format(t, %{indent: 4}) end)
  d.({:format2b, t}, fn -> OtpJSON.format(t, %{max: 10, indent: 3}) end, fn -> :json.format(t, %{max: 10, indent: 3}) end)
  d.({:format3, t}, fn -> OtpJSON.format(t, &OtpJSON.format_value/3, %{indent: 1}) end, fn -> :json.format(t, &:json.format_value/3, %{indent: 1}) end)
  d.({:encode_value, t}, fn -> OtpJSON.encode_value(t, &OtpJSON.encode_value/2) end, fn -> :json.encode_value(t, &:json.encode_value/2) end)
  d.({:encode_list, t}, fn -> OtpJSON.encode_list(t, &OtpJSON.encode_value/2) end, fn -> :json.encode_list(t, &:json.encode_value/2) end)
  d.({:encode_map, t}, fn -> OtpJSON.encode_map(t, &OtpJSON.encode_value/2) end, fn -> :json.encode_map(t, &:json.encode_value/2) end)
  d.({:encode_map_checked, t}, fn -> OtpJSON.encode_map_checked(t, &OtpJSON.encode_value/2) end, fn -> :json.encode_map_checked(t, &:json.encode_value/2) end)
  d.({:encode_atom, t}, fn -> OtpJSON.encode_atom(t, &OtpJSON.encode_value/2) end, fn -> :json.encode_atom(t, &:json.encode_value/2) end)
  d.({:encode_integer, t}, fn -> OtpJSON.encode_integer(t) end, fn -> :json.encode_integer(t) end)
  d.({:encode_float, t}, fn -> OtpJSON.encode_float(t) end, fn -> :json.encode_float(t) end)
  d.({:encode_binary, t}, fn -> OtpJSON.encode_binary(t) end, fn -> :json.encode_binary(t) end)
  d.({:encode_binary_all, t}, fn -> OtpJSON.encode_binary_escape_all(t) end, fn -> :json.encode_binary_escape_all(t) end)
  d.({:kv, t}, fn -> OtpJSON.encode_key_value_list(t, &OtpJSON.encode_value/2) end, fn -> :json.encode_key_value_list(t, &:json.encode_value/2) end)
  d.({:kv_checked, t}, fn -> OtpJSON.encode_key_value_list_checked(t, &OtpJSON.encode_value/2) end, fn -> :json.encode_key_value_list_checked(t, &:json.encode_value/2) end)
  d.({:fmt_kv, t}, fn -> OtpJSON.format_key_value_list(t, &OtpJSON.format_value/3, %{level: 0, col: 0, indent: 2, max: 100}) end, fn -> :json.format_key_value_list(t, &:json.format_value/3, %{level: 0, col: 0, indent: 2, max: 100}) end)
  d.({:fmt_kv_checked, t}, fn -> OtpJSON.format_key_value_list_checked(t, &OtpJSON.format_value/3, %{level: 0, col: 0, indent: 2, max: 100}) end, fn -> :json.format_key_value_list_checked(t, &:json.format_value/3, %{level: 0, col: 0, indent: 2, max: 100}) end)
  d.({:fmt_all, t}, fn -> OtpJSON.format(t, &(OtpJSON.format_value(&1, &2, &3)), %{}) end, fn -> :json.format(t, &(:json.format_value(&1, &2, &3)), %{}) end)
end

bins = [<<>>, "a", "abcdefgh", "abcdefghi", "abcdefg\"h", "q\"uote\\back\nnl\ttab\x00\x1f", "é", "é€😀", "日本語 text 1234567 日本語", <<0xC3>>, <<0xC3, 0x28>>, <<"abcdefgh", 0xE2, 0x82>>, <<0xFF>>, <<"abc", 0xF0, 0x9F, 0x98>>, <<0xED, 0xA0, 0x80>>, <<0xC0, 0x80>>, <<"abcdefgh12345678", 0x80>>, <<"é", 0xFF, "x">>, String.duplicate("a", 100) <> "\n" <> String.duplicate("é", 30), "\u007f", "\u0080", "\u07ff", "\u0800", "\uffff", "\u{10000}", "\u{10ffff}", "\u00ff", "\u0100", "\u0fff", "\u1000", String.duplicate("😀", 5), <<"a", 0xE2>>, <<0xF4, 0x90, 0x80, 0x80>>, <<0xF8, 0x88, 0x80, 0x80, 0x80>>]
for b <- bins, do: e_cases.(b)
for _ <- 1..3000, do: e_cases.(DiffGen.term(3))
for t <- [[], %{}, [[]], [%{}], %{"a" => []}, %{"a" => %{}}, [1, [2, [3]]], %{1 => 2, 2.5 => 3, "b" => 5, a: 4}, [{:a, 1}, {:b, [1, 2]}], [{:a, 1}, {:a, 2}], [{"a", 1}, {:a, 2}], [{1, 1}, {"1", 2}], [1, :sym, "s", nil, 1.0, {1, 2}], {:tuple}, self(), make_ref(), fn -> 1 end, :foo, :null, :true, 1.0e100, ~c"abc", [?a | ?b], [1 | 2], [{:a, 1} | :x], %{{1, 2} => 3}, %{[1] => 3}, [{[1], 2}], [1, 2, 3 | []], :lists.seq(1, 200), for(i <- 1..150, do: "elem#{i}"), for(i <- 1..40, into: %{}, do: {"k#{i}", i}), [%{"a" => [1, 2, 3, %{"b" => String.duplicate("x", 120)}]}, [String.duplicate("y", 200), 2], 3, 4]] do
  e_cases.(t)
end
for ch <- [0xFF, 0x100, 0x7FF, 0x800, 0xFFF, 0x1000, 0xFFFF, 0x10000, 0x10FFFF, 0x41, 0xE9, 0x20AC, 0x1F600] do
  d.({:escall, ch}, fn -> OtpJSON.encode_binary_escape_all(<<ch::utf8>>) end, fn -> :json.encode_binary_escape_all(<<ch::utf8>>) end)
  d.({:escall2, ch}, fn -> OtpJSON.encode_binary_escape_all("abcdefgh" <> <<ch::utf8>> <> "ij") end, fn -> :json.encode_binary_escape_all("abcdefgh" <> <<ch::utf8>> <> "ij") end)
end
# custom encoder callbacks
custom = fn mod ->
  fn t -> mod.encode(t, fn
    {:ts, n}, _enc -> ["\"t", Integer.to_string(n), "\""]
    [{_, _} | _] = kv, enc -> mod.encode_key_value_list(kv, enc)
    other, enc -> mod.encode_value(other, enc)
  end) end
end
for t <- [{:ts, 5}, [{:a, {:ts, 1}}, {:b, 2}], [[{:a, 1}], [{:b, 2}]], %{"x" => {:ts, 9}}] do
  d.({:custom, t}, fn -> custom.(OtpJSON).(t) end, fn -> custom.(:json).(t) end)
end
for bad <- [nil, :a, 1] do
  d.({:enc_nofun, bad}, fn -> OtpJSON.encode(1, bad) end, fn -> :json.encode(1, bad) end)
  d.({:fmt_nofun, bad}, fn -> OtpJSON.format(1, bad) end, fn -> :json.format(1, bad) end)
end

# round trip: decode of random docs then encode
for _ <- 1..1000 do
  doc = DiffGen.val(4)
  d.({:roundtrip, doc}, fn -> OtpJSON.decode(doc) |> OtpJSON.encode() end, fn -> :json.decode(doc) |> :json.encode() end)
  d.({:roundtrip_fmt, doc}, fn -> OtpJSON.decode(doc) |> OtpJSON.format() end, fn -> :json.decode(doc) |> :json.format() end)
end

{total, fails} = Diff.totals()
IO.puts("differential cases: #{total}, mismatches: #{fails}")
if fails > 0, do: System.halt(1)
