# <<_c, rest::binary>> in a self tail call whose first clause takes the binary whole
defmodule Main do
  def eat(_b, 0), do: 0
  def eat(<<_c, rest::binary>>, n), do: eat(rest, n - 1)

  def loop(0, _b, s), do: s
  def loop(k, b, s), do: loop(k - 1, b, s + eat(b, 1000))

  def main() do
    n = String.to_integer(hd(System.argv()))
    b = :binary.copy("x", 1000)
    IO.inspect(loop(div(n, 1000), b, 0))
  end
end

Main.main()
