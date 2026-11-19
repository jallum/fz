# IO.iodata_to_binary([a, "-", b])
defmodule Main do
  def loop(0, _a, _b, s), do: s
  def loop(n, a, b, s) do
    r = IO.iodata_to_binary([a, "-", b])
    loop(n - 1, a, b, s + byte_size(r))
  end

  def main() do
    n = String.to_integer(hd(System.argv()))
    a = :binary.copy("x", 10)
    b = :binary.copy("y", 2)
    IO.inspect(loop(n, a, b, 0))
  end
end

Main.main()
