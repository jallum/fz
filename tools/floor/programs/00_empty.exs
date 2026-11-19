# the loop every other example is wrapped in
# target: empty
defmodule Main do
  def loop(0, s), do: s
  def loop(n, s), do: loop(n - 1, s + 1)

  def main() do
    n = String.to_integer(hd(System.argv()))
    IO.inspect(loop(n, 0))
  end
end

Main.main()
