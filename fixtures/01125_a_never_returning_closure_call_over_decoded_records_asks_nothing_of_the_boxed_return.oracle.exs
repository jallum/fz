defmodule P do
  def main(lines) do
    records = lines |> Enum.map(&JSON.decode!/1)
    starts = for %{"kind" => "span_start", "span_id" => id} = r <- records, into: %{}, do: {id, %{parent: r["parent_span_id"], inclusive: 0}}
    out =
      Enum.reduce(starts, starts, fn {_id, span}, acc ->
        case Map.fetch(acc, span.parent) do
          {:ok, parent} -> Map.put(acc, span.parent, %{parent | inclusive: parent.inclusive - span.inclusive})
          :error -> acc
        end
      end)
    IO.inspect(map_size(out))
  end
end
defmodule Oracle do
  def main() do
    P.main([
      "{\"kind\": \"span_start\", \"span_id\": 1, \"parent_span_id\": 0}",
      "{\"kind\": \"span_start\", \"span_id\": 2, \"parent_span_id\": 1}"
    ])
  end
end

Oracle.main()
