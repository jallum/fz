defmodule Probe do
  def bitstring_guard(x) when is_bitstring(x), do: :bitstring
  def bitstring_guard(_), do: :other

  def binary_guard(x) when is_binary(x), do: :binary
  def binary_guard(_), do: :other

  def in_body(x), do: {is_bitstring(x), is_binary(x)}

  def binary_clause(b) when is_binary(b), do: :binary_clause
  def binary_clause(_), do: :other

  def build(n), do: <<n::size(n)>>

  def launder(x) do
    send(self(), x)

    receive do
      message -> message
    end
  end

  def after_bits(<<_::3, rest::binary>>), do: {:matched, rest}
  def after_bits(_), do: :no_match

  def after_byte(<<_::8, rest::binary>>), do: {:matched, rest}
  def after_byte(_), do: :no_match

  def walk_three(<<_::3, rest::bitstring>>), do: {is_binary(rest), is_bitstring(rest), byte_size(rest)}
  def walk_three(_), do: :no_match

  def walk_four(<<_::4, rest::bitstring>>), do: {is_binary(rest), is_bitstring(rest), byte_size(rest)}
  def walk_four(_), do: :no_match

  def upcase(x) do
    String.upcase(x)
  rescue
    FunctionClauseError -> :function_clause_error
  end
end

samples = [
  {:text, "abc"},
  {:bytes, <<1, 2, 3>>},
  {:empty, <<>>},
  {:sixteen_bits, <<1::16>>},
  {:three_bits, <<1::3>>},
  {:one_bit, <<1::1>>},
  {:byte_and_four_bits, <<255, 1::4>>},
  {:atom, :atom},
  {:integer, 42},
  {:list, [1, 2]},
  {:tuple, {1, 2}}
]

Enum.each(samples, fn {label, value} ->
  IO.inspect({label, Probe.bitstring_guard(value), Probe.binary_guard(value), Probe.in_body(value)})
end)

IO.inspect(Enum.map([<<1::3>>, "ab", <<1, 2::4>>], fn x -> Probe.binary_clause(Probe.launder(x)) end))

built = Probe.build(3)
IO.inspect({is_binary(built), is_bitstring(built), byte_size(built)})
IO.inspect({byte_size(<<1::3>>), byte_size(<<1, 2::4>>), byte_size(<<1, 2>>), byte_size(<<>>)})

IO.inspect(Probe.after_bits(<<1, 2>>))
IO.inspect(Probe.after_bits(<<1, 2, 3::5>>))
IO.inspect(Probe.after_byte(<<1, 2::3>>))
IO.inspect(Probe.after_byte(<<1, 2>>))

IO.inspect(Probe.walk_three(<<1, 2>>))
IO.inspect(Probe.walk_three(<<1, 2::3>>))
IO.inspect(Probe.walk_four(<<255, 1::4>>))
IO.inspect(Probe.walk_four(<<1, 2>>))

IO.inspect(Probe.upcase(Probe.launder(<<1::3>>)))
IO.inspect(Probe.upcase(Probe.launder("abc")))
