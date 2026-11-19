# acc <> x, both variables, 10-byte acc
# target: concat
defmodule Main do
  def loop(0, _acc, _x, s), do: s
  def loop(n, acc, x, s) do
    r = acc <> x
    loop(n - 1, acc, x, s + byte_size(r))
  end

  def main() do
    n = String.to_integer(hd(System.argv()))
    acc = :binary.copy("x", 10)
    x = :binary.copy("y", 2)
    IO.inspect(loop(n, acc, x, 0))
  end
end

Main.main()
