defmodule Oracle do
  defp at(x), do: Enum.at([x], 0)

  defp sorted(map), do: Enum.sort(Map.to_list(map))

  def main() do
    IO.inspect(sorted(Map.update(at(%{a: 1, b: 2}), :a, 0, fn v -> v + 10 end)))
    IO.inspect(sorted(Map.update(at(%{a: 1}), :b, 0, fn v -> v + 10 end)))
    IO.inspect(Map.update(at(%{}), :a, 7, fn v -> v + 10 end))
    IO.inspect(sorted(Map.update(at(%{a: 1}), :b, :default, fn _ -> raise "the function must not be called" end)))
    IO.inspect(Map.update(at(%{"x" => 1}), "x", 0, fn v -> v * 5 end))
    IO.inspect(Map.update(at(%{"x" => 1}), "y", 0, fn v -> v * 5 end))
    pairs = [{"a", 1}, {"b", 2}, {"a", 3}, {"c", 4}, {"b", 5}]
    IO.inspect(Enum.reduce(pairs, %{}, fn {k, n}, acc -> Map.update(acc, k, n, &(&1 + n)) end))
  end
end

Oracle.main()
