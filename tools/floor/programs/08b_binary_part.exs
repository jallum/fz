# binary_part(b, 3, 4)
defmodule Main do
  def loop(0, _b, s), do: s
  def loop(n, b, s) do
    part = binary_part(b, 3, 4)
    loop(n - 1, b, s + byte_size(part))
  end

  def main() do
    n = String.to_integer(hd(System.argv()))
    b = :binary.copy("x", 200) <> "yz"
    IO.inspect(loop(n, b, 0))
  end
end

Main.main()
