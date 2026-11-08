defmodule Oracle do
  def kind(%{} = m, _tag) when map_size(m) == 0, do: :empty
  def kind(%{name: "a"} = m, tag), do: {:a, Map.get(m, :v), tag}
  def kind(m = %{name: "b"}, tag), do: {:b, Map.get(m, :v), tag}
  def kind(_m, _tag), do: :other

  def pair({a, _} = {_, b}), do: {a, b}

  def heads([h | _] = [_, x | _] = l), do: {h, x, length(l)}

  def main() do
    IO.inspect(kind(%{}, 0))
    IO.inspect(kind(%{name: "a", v: 1}, 1))
    IO.inspect(kind(%{name: "b", v: 2}, 2))
    IO.inspect(kind(%{name: "c", v: 3}, 3))
    IO.inspect(pair({1, 2}))
    IO.inspect(heads([5, 6, 7]))
  end
end

Oracle.main()
