defmodule Oracle do
  def go([], a1, a2, a3), do: {Enum.reverse(a1), Enum.reverse(a2), Enum.reverse(a3)}
  def go([x | rest], a1, a2, a3) when x > 4, do: go(rest, [x | a1], a2, a3)
  def go([x | rest], a1, a2, a3) when x > 2, do: go(rest, a1, [x | a2], a3)
  def go([x | rest], a1, a2, a3), do: go(rest, a1, a2, [x | a3])

  def main() do
    IO.inspect(go([1, 2, 3, 4, 5, 6], [], [], []))
  end
end

Oracle.main()
