# byte_size of a 22-byte binary
# target: byte_size
defmodule Main do
  def loop(0, _b, s), do: s
  def loop(n, b, s) do
    loop(n - 1, b, s + byte_size(b))
  end

  def main() do
    n = String.to_integer(hd(System.argv()))
    b = :binary.copy("x", 20) <> "yz"
    IO.inspect(loop(n, b, 0))
  end
end

Main.main()
