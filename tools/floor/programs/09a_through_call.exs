# a binary passed to a function and returned
# target: through_call
defmodule Main do
  def id(b), do: b
  def loop(0, _b, s), do: s
  def loop(n, b, s) do
    loop(n - 1, b, s + byte_size(id(b)))
  end

  def main() do
    n = String.to_integer(hd(System.argv()))
    b = :binary.copy("x", 20) <> "yz"
    IO.inspect(loop(n, b, 0))
  end
end

Main.main()
