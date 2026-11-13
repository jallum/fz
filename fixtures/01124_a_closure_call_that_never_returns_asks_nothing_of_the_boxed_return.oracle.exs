defmodule M do
  def main(args) do
    spans = spans(args)
    by_name(spans, 20)
  end

  defp spans(records) do
    starts = for r <- records, into: %{}, do: {r, %{id: r, parent: 0, name: "n", inclusive: 0, self: 0}}
    with_stops = Enum.reduce(records, starts, fn id, acc -> Map.update!(acc, id, &%{&1 | inclusive: 5, self: 5}) end)
    Enum.reduce(with_stops, with_stops, fn {_id, span}, acc ->
      case Map.fetch(acc, span.parent) do
        {:ok, parent} -> Map.put(acc, parent.id, %{parent | self: parent.self - span.inclusive})
        :error -> acc
      end
    end)
  end

  defp by_name(spans, top) do
    spans
    |> Map.values()
    |> Enum.group_by(& &1.name)
    |> Enum.map(fn {name, ss} -> {name, length(ss), sum(ss, :inclusive), sum(ss, :self)} end)
    |> Enum.sort_by(fn {_, _, inc, _} -> -inc end)
    |> Enum.take(top)
  end

  defp sum(spans, key), do: spans |> Enum.map(&Map.fetch!(&1, key)) |> Enum.sum()
end
defmodule Oracle do
  def main() do
    IO.inspect(M.main([1, 2, 3]))
  end
end

Oracle.main()
