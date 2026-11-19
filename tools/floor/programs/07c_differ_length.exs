# a == b, lengths differ
# target: eqw_length
defmodule Main do
  def loop(0, _a, _b, s), do: s
  def loop(n, a, b, s) do
    loop(n - 1, a, b, if(a == b, do: s + 1, else: s))
  end

  def main() do
    n = String.to_integer(hd(System.argv()))
    a = :binary.copy("x", 10) <> "q"
    b = :binary.copy("x", 11) <> "q"
    IO.inspect(loop(n, a, b, 0))
  end
end

Main.main()
