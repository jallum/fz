defmodule Extent do
  def remaining(<<_, rest :: binary>>, acc), do: remaining(rest, [byte_size(rest) | acc])
  def remaining(<<>>, acc), do: Enum.reverse(acc)

  def after_bits(<<_ :: 4, _ :: 4, _ :: 8, rest :: binary>>), do: byte_size(rest)
  def after_bits(_), do: :short

  def off_byte(<<_ :: 3, rest :: binary>>), do: byte_size(rest)
  def off_byte(_), do: :short

  def kept(<<_, rest :: binary>>), do: {byte_size(rest), rest}
  def kept(<<>>), do: :empty

  def tail_of(<<_, _, rest :: binary>>), do: rest
  def tail_of(_), do: :short

  def total(bytes), do: total(bytes, 0)
  defp total(<<_, rest :: binary>>, acc), do: total(rest, acc + byte_size(rest))
  defp total(<<>>, acc), do: acc
end

IO.inspect(Extent.remaining("hello", []))
IO.inspect(Extent.remaining("", []))
IO.inspect(Extent.after_bits("abcdef"))
IO.inspect(Extent.after_bits("ab"))
IO.inspect(Extent.off_byte(<<5 :: 3, 2, 3>>))
IO.inspect(Extent.kept("abc"))
IO.inspect(Extent.kept(""))
IO.inspect(byte_size(Extent.tail_of("abcdefg")))
IO.inspect(Extent.tail_of("ab") == "")
IO.inspect(Extent.total(String.duplicate("a", 1000)))
IO.inspect(byte_size(String.duplicate("xy", 500)))
IO.inspect(byte_size(<<1, 2, 3>>))
