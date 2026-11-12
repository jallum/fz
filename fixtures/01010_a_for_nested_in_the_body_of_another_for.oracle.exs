defmodule Oracle do
  def main() do
    IO.inspect(for x <- [1, 2, 3], do: (for y <- [x, x * 10], do: y + 1))
  end
end

Oracle.main()
