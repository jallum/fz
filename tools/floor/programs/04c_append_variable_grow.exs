# acc <> x where acc is the growing result
# n: 10000000 30000000
# target: append
defmodule Main do
  def loop(0, acc, _x), do: acc
  def loop(n, acc, x), do: loop(n - 1, acc <> x, x)

  def main() do
    n = String.to_integer(hd(System.argv()))
    x = :binary.copy("y", 2)
    IO.inspect(byte_size(loop(n, "", x)))
  end
end

Main.main()
