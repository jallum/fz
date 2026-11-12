defmodule Oracle do
  def go([], a), do: a
  def go([x | rest], a), do: go(rest, [x | a])

  def tell(:a), do: "atom"
  def tell(x), do: x

  def main() do
    [h1 | _] = go([1, 2], [:a])
    [h2 | _] = go([1, 2], ["x"])
    IO.inspect(tell(h1))
    IO.inspect(tell(h2))
    IO.inspect(go([3], [:a]))
    IO.inspect(go([3], ["x"]))
  end
end

Oracle.main()
