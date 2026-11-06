defmodule Oracle do
  def unwrap({v, false}), do: v
  def unwrap({v, true}), do: v + 1

  def first([h | _]), do: h

  def run() do
    IO.inspect(Enum.map([1, 2, 3], fn n -> unwrap({n, n == 2}) end))
    IO.inspect(first(Enum.map([4, 5], fn n -> n * 2 end)))
    IO.inspect(Enum.map([[1], [2, 3]], fn l -> first(l) end))
  end
end

Oracle.run()
