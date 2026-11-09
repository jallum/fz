defmodule Oracle do
  def sorted(set), do: Enum.sort(MapSet.to_list(set))

  def main() do
    empty = MapSet.new()
    IO.inspect(MapSet.size(empty))
    IO.inspect(sorted(empty))
    set = MapSet.new([3, 1, 3, 2, 1])
    IO.inspect(MapSet.size(set))
    IO.inspect(sorted(set))
    IO.inspect(MapSet.size(MapSet.put(set, 2)))
    IO.inspect(sorted(MapSet.put(set, 9)))
    IO.inspect(MapSet.member?(set, 1))
    IO.inspect(MapSet.member?(set, 7))
    IO.inspect(sorted(MapSet.delete(set, 1)))
    IO.inspect(sorted(MapSet.delete(set, 7)))
    IO.inspect(MapSet.size(MapSet.delete(empty, 1)))
  end
end

Oracle.main()
