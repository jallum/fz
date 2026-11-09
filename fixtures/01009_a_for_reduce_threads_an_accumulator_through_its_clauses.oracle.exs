defmodule Oracle do
  def main() do
    IO.inspect(for x <- [1, 2, 3, 4, 5], reduce: {0, 0} do
      {big, small} when x > 3 -> {big + x, small}
      {big, small} -> {big, small + x}
    end)
  end
end

Oracle.main()
