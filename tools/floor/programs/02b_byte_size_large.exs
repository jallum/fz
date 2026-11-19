# byte_size of a 202-byte binary
# target: byte_size_view
defmodule Main do
  def loop(0, _b, s), do: s
  def loop(n, b, s) do
    loop(n - 1, b, s + byte_size(b))
  end

  def main() do
    n = String.to_integer(hd(System.argv()))
    b = :binary.copy("x", 200) <> "yz"
    IO.inspect(loop(n, b, 0))
  end
end

Main.main()
