defmodule Oracle do
  def main() do
    IO.inspect(for x <- [1, 2], y <- [10, 20, 30], do: x + y)
  end
end

Oracle.main()
