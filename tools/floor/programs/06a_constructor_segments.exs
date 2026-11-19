# <<a::8, b::16, c::binary>>
# target: ctor_segments
defmodule Main do
  def loop(0, _c, s), do: s
  def loop(n, c, s) do
    r = <<rem(n, 256)::8, n::16, c::binary>>
    loop(n - 1, c, s + byte_size(r))
  end

  def main() do
    n = String.to_integer(hd(System.argv()))
    c = :binary.copy("y", 10)
    IO.inspect(loop(n, c, 0))
  end
end

Main.main()
