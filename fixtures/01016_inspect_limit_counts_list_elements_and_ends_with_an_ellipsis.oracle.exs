defmodule Oracle do
  def main() do
    IO.inspect(inspect([1, 2, 3, 4, 5], limit: 3))
    IO.inspect(inspect([1, 2, 3, 4, 5], limit: 1))
    IO.inspect(inspect([1, 2, 3], limit: 3))
    IO.inspect(inspect([1, 2, 3], limit: 10))
    IO.inspect(inspect([[1, 2, 3], [4]], limit: 4))
    IO.inspect(inspect([[], []], limit: 1))
    IO.inspect(inspect(["a", "b", "c"], limit: 2))
    IO.inspect(inspect([[1, [2, [3, [4]]]]], limit: 3))
  end
end

Oracle.main()
