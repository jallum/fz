defmodule Oracle do
  def window(b, at) do
    <<_ :: binary-size(at), part :: binary-size(12), _ :: binary>> = b
    part
  end

  def run() do
    big = String.duplicate("abcdefghij", 2_000_001)
    IO.inspect({byte_size(big), window(big, 0), window(big, 9_999_995), window(big, 20_000_010 - 12)})
    IO.inspect(big == String.duplicate(String.duplicate("abcdefghij", 3), 666_667))

    IO.inspect(Enum.map(0..5, fn n -> String.duplicate("ab", n) end))
    IO.inspect({String.duplicate("", 1_000), String.duplicate("x", 1), String.duplicate("é", 3)})
    IO.inspect(Enum.all?(1..300, fn n -> byte_size(String.duplicate("abc", n)) == 3 * n end))
  end
end

Oracle.run()
