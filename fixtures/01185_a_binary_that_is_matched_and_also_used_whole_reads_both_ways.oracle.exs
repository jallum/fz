defmodule Cold do
  # The hot clause takes the binary apart; the cold clause keeps it whole.
  def scan(<<0, rest :: binary>>, n), do: scan(rest, n + 1)
  def scan(<<_, rest :: binary>> = whole, n) when n > 3, do: {:stopped, whole, rest}
  def scan(<<_, rest :: binary>>, n), do: scan(rest, n + 1)
  def scan(<<>>, n), do: {:end, n}

  # One value, two shapes: a tuple read by field and a binary read by match.
  def kind({a, _}), do: {:pair, a}
  def kind(<<a, _ :: binary>>), do: {:bytes, a}
  def kind(other), do: {:other, other}

  # A value matched and then stored whole.
  def stash(<<a, rest :: binary>> = bytes), do: {a, bytes, rest}

  # A matched binary handed to a function that does not match it.
  def measure(<<_, rest :: binary>>), do: byte_size(rest) + String.length(rest)
end

IO.inspect(Cold.scan("000000", 0))
IO.inspect(Cold.scan("0123456789", 0))
IO.inspect(Cold.scan("12", 0))
IO.inspect(Cold.scan("", 0))
IO.inspect(Cold.kind({1, 2}))
IO.inspect(Cold.kind("xyz"))
IO.inspect(Cold.kind(7))
IO.inspect(Cold.stash("abc"))
IO.inspect(Cold.measure("hello"))
