defmodule Mid do
  def drop(<<_, rest :: binary>>, n) when n > 0, do: drop(rest, n - 1)
  def drop(bytes, 0), do: bytes
  def drop(_bytes, _n), do: :short

  def same(<<_, _ :: binary>> = bytes), do: bytes
  def same(other), do: other

  def keep(<<head, rest :: binary>>), do: {head, rest, [rest, rest]}
  def keep(<<>>), do: :empty

  def keep_after(<<_, rest :: binary>>, 0), do: keep(rest)
  def keep_after(<<_, rest :: binary>>, n), do: keep_after(rest, n - 1)

  def heads(<<head, rest :: binary>>), do: [head | heads(rest)]
  def heads(<<>>), do: []

  def rematch(bytes) do
    case drop(bytes, 2) do
      <<a, b, tail :: binary>> -> {a, b, tail, byte_size(tail)}
      other -> other
    end
  end
end

bytes = "abcdefghij"
IO.inspect(Mid.drop(bytes, 3))
IO.inspect(Mid.drop(bytes, 0) === bytes)
IO.inspect(Mid.drop(bytes, 10))
IO.inspect(Mid.drop(bytes, 11))
IO.inspect(Mid.same(bytes) === bytes)
IO.inspect(Mid.same(:not_a_binary))
IO.inspect(Mid.keep(bytes))
IO.inspect(Mid.keep_after(bytes, 4))
IO.inspect(Mid.keep_after("xyz", 1))
IO.inspect(Mid.keep(""))
IO.inspect(Mid.heads("hello"))
IO.inspect(Mid.rematch(bytes))
IO.inspect(Mid.rematch("ab"))
IO.inspect(Mid.drop(String.duplicate("z", 300), 250) === String.duplicate("z", 50))
IO.inspect(byte_size(Mid.drop(String.duplicate("z", 300), 250)))
