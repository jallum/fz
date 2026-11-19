# <<_c, rest::binary>> in a self tail call, over a 1000-byte binary
# target: match_tail
defmodule Main do
  def eat(<<>>), do: 0
  def eat(<<_c, rest::binary>>), do: eat(rest)

  def loop(0, _b, s), do: s
  def loop(k, b, s), do: loop(k - 1, b, s + eat(b))

  def main() do
    n = String.to_integer(hd(System.argv()))
    b = :binary.copy("x", 1000)
    IO.inspect(loop(div(n, 1000), b, 0))
  end
end

Main.main()
