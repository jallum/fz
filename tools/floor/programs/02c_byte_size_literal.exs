# byte_size of a literal
# target: empty
defmodule Main do
  def loop(0, s), do: s
  def loop(n, s), do: loop(n - 1, s + byte_size("hello world"))

  def main() do
    n = String.to_integer(hd(System.argv()))
    IO.inspect(loop(n, 0))
  end
end

Main.main()
