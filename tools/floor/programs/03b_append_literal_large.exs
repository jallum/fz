# acc <> "ab", 200-byte acc
defmodule Main do
  def loop(0, _acc, s), do: s
  def loop(n, acc, s) do
    r = acc <> "ab"
    loop(n - 1, acc, s + byte_size(r))
  end

  def main() do
    n = String.to_integer(hd(System.argv()))
    acc = :binary.copy("x", 200)
    IO.inspect(loop(n, acc, 0))
  end
end

Main.main()
