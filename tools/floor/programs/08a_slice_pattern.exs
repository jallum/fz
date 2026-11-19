# <<_::binary-size(3), part::binary-size(4), _::binary>> = b
# target: slice
defmodule Main do
  def loop(0, _b, s), do: s
  def loop(n, b, s) do
    <<_::binary-size(3), part::binary-size(4), _::binary>> = b
    loop(n - 1, b, s + byte_size(part))
  end

  def main() do
    n = String.to_integer(hd(System.argv()))
    b = :binary.copy("x", 200) <> "yz"
    IO.inspect(loop(n, b, 0))
  end
end

Main.main()
