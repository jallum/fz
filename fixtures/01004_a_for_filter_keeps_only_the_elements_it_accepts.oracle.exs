defmodule Oracle do
  def main() do
    IO.inspect(for x <- [1, 2, 3, 4, 5, 6], rem(x, 2) == 0, do: x)
  end
end

Oracle.main()
