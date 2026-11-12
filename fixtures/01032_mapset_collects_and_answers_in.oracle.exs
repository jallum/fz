defmodule Oracle do
  def sorted(set), do: Enum.sort(MapSet.to_list(set))

  def main() do
    into = Enum.into([2, 1, 2], MapSet.new())
    IO.inspect(sorted(into))
    grown = Enum.into([5, 1], MapSet.new([1, 9]))
    IO.inspect(sorted(grown))
    comp = for x <- ["x", "y", "x"], into: MapSet.new(), do: x
    IO.inspect(sorted(comp))
    IO.inspect("x" in comp)
    IO.inspect("z" in comp)
    IO.inspect(2 in into)
  end
end

Oracle.main()
