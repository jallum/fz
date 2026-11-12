defmodule Oracle do
  def main() do
    set = MapSet.new([4, 2, 4, 6])
    IO.inspect(Enum.count(set))
    IO.inspect(Enum.sort(Enum.map(set, fn x -> x * 10 end)))
    IO.inspect(Enum.reduce(set, 0, fn x, acc -> x + acc end))
    IO.inspect(Enum.count(MapSet.new()))
    IO.inspect(Enum.member?(set, 6))
  end
end

Oracle.main()
