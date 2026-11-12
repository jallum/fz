defmodule Oracle do
  def half(x) do
    if rem(x, 2) == 0, do: div(x, 2), else: nil
  end

  def main() do
    IO.inspect(for x <- [1, 2, 3, 4], y = half(x), y > 1, do: {x, y})
  end
end

Oracle.main()
