# <<c, rest::binary>> where the byte is used and the call is not a tail call, over a 1000-byte binary
# target: match_sum
defmodule Main do
  def sum(<<>>), do: 0
  def sum(<<c, rest::binary>>), do: c + sum(rest)

  def loop(0, _b, s), do: s
  def loop(k, b, s), do: loop(k - 1, b, s + sum(b))

  def main() do
    n = String.to_integer(hd(System.argv()))
    b = :binary.copy("x", 1000)
    IO.inspect(loop(div(n, 1000), b, 0))
  end
end

Main.main()
