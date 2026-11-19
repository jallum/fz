# <<rest::binary>> = b, the whole binary taken as the rest at position 0
# target: byte_size
defmodule Main do
  def loop(0, _b, s), do: s
  def loop(n, b, s) do
    <<rest::binary>> = b
    loop(n - 1, b, s + byte_size(rest))
  end

  def main() do
    n = String.to_integer(hd(System.argv()))
    b = :binary.copy("x", 22)
    IO.inspect(loop(n, b, 0))
  end
end

Main.main()
