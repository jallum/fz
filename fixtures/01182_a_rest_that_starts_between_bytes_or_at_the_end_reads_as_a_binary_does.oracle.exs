defmodule Bits do
  # Three bits at a time, so every position after the first is not a byte.
  def triples(<<a :: 3, rest :: bitstring>>), do: [a | triples(rest)]
  def triples(_), do: []

  # A byte read at a position that is not a multiple of eight.
  def shifted(<<_ :: 3, byte, rest :: bitstring>>), do: {byte, rest}
  def shifted(_), do: :short

  def walk(<<_ :: 5, rest :: bitstring>>, n), do: walk(rest, n + 1)
  def walk(<<>>, n), do: {:even, n}
  def walk(rest, n), do: {:left, rest, n}

  def empty(<<_, rest :: binary>>), do: rest
  def empty(_), do: :none

  def tail_size(<<_, rest :: binary>>), do: byte_size(rest)
  def tail_size(<<>>), do: :done
end

IO.inspect(Bits.triples(<<0b101_110_011_000_111_010_001_100 :: 24>>))
IO.inspect(Bits.triples(<<1, 2>>))
IO.inspect(Bits.shifted(<<0b101_00110_011_00000 :: 16>>))
IO.inspect(Bits.shifted(<<255>>))
IO.inspect(Bits.walk(<<1, 2, 3, 4, 5>>, 0))
IO.inspect(Bits.walk(<<1, 2, 3, 4, 5, 6>>, 0))
IO.inspect(Bits.empty("a"))
IO.inspect(Bits.empty("a") === "")
IO.inspect(Bits.empty(""))
IO.inspect(Bits.tail_size("a"))
IO.inspect(Bits.tail_size(""))
IO.inspect(Bits.tail_size("hello"))
