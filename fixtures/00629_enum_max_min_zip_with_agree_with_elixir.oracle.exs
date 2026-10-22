defmodule Oracle do
  def run() do
    IO.inspect([Enum.max([3, 1, 2]), Enum.min([3, 1, 2])])
    IO.inspect([Enum.max([3, 1, 2], fn -> 0 end), Enum.min([3, 1, 2], fn -> 0 end)])
    IO.inspect([Enum.max([], fn -> 0 end), Enum.min([], fn -> 99 end), Enum.max([], fn -> :none end)])
    IO.inspect([Enum.max_by(["a", "abc", "ab"], fn s -> byte_size(s) end), Enum.min_by(["abc", "a", "ab"], fn s -> byte_size(s) end)])

    IO.inspect(Enum.zip_with([[1, 2, 3], [4, 5, 6]], fn [a, b] -> a + b end))
    IO.inspect(Enum.zip_with([[1, 2, 3], [1000, 2000]], fn [a, b] -> a * b end))
    IO.inspect(Enum.zip_with([[1, 2], [3, 4], [5, 6]], fn col -> Enum.max(col) end))
    IO.inspect(Enum.zip_with([["a", "bcd"], ["ef", "g"]], fn col -> Enum.max(Enum.map(col, fn s -> byte_size(s) end)) end))
    IO.inspect(Enum.zip_with([[1, 2, 3], []], fn [a, b] -> a + b end))
    IO.inspect(Enum.zip_with([1..3, [10, 20, 30]], fn [a, b] -> a + b end))
    IO.inspect(Enum.zip_with([[1, 2, 3]], fn col -> col end))
    IO.inspect(Enum.zip([1, 2, 3], [:a, :b]))
  end
end

Oracle.run()
