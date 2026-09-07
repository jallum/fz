defmodule M do
  def go do
    IO.inspect(head_byte("hello"))
    IO.inspect(head_byte(""))
    IO.inspect(head_byte(:not_a_binary))

    IO.inspect(framed(<<3, 1, 2, 3, 255>>))
    IO.inspect(framed(<<0, 42>>))

    IO.inspect(first_two("abc"))
    IO.inspect(first_two("a"))

    IO.inspect(words("the quick brown fox", "", []))
    IO.inspect(byte_count("hello", 0))
  end

  defp head_byte(<<b, rest::binary>>), do: {b, rest}
  defp head_byte(<<>>), do: :empty
  defp head_byte(_other), do: :not_a_binary

  defp framed(<<len, payload::binary-size(len), rest::binary>>), do: {len, payload, rest}
  defp framed(_other), do: :unframed

  defp first_two(bytes) do
    case bytes do
      <<a, b, rest::binary>> -> {a, b, rest}
      <<a>> -> {:one, a}
      <<>> -> :none
    end
  end

  defp words(<<>>, current, acc), do: reverse([current | acc], [])
  defp words(<<32, rest::binary>>, current, acc), do: words(rest, "", [current | acc])
  defp words(<<c, rest::binary>>, current, acc), do: words(rest, current <> <<c>>, acc)

  defp byte_count(<<>>, n), do: n
  defp byte_count(<<_c, rest::binary>>, n), do: byte_count(rest, n + 1)

  defp reverse([], acc), do: acc
  defp reverse([head | tail], acc), do: reverse(tail, [head | acc])
end

M.go()
