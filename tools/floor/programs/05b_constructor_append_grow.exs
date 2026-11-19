# <<acc::binary, x::binary>> where acc is the growing result
# n: 20000 60000
# target: append
defmodule Main do
  def loop(0, acc, _x), do: acc
  def loop(n, acc, x), do: loop(n - 1, <<acc::binary, x::binary>>, x)

  def main() do
    n = String.to_integer(hd(System.argv()))
    x = :binary.copy("y", 2)
    IO.inspect(byte_size(loop(n, "", x)))
  end
end

Main.main()
