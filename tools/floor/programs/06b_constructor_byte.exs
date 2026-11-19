# <<byte>> alone
# target: ctor_byte
defmodule Main do
  def loop(0, s), do: s
  def loop(n, s) do
    r = <<rem(n, 256)>>
    loop(n - 1, s + byte_size(r))
  end

  def main() do
    n = String.to_integer(hd(System.argv()))
    IO.inspect(loop(n, 0))
  end
end

Main.main()
