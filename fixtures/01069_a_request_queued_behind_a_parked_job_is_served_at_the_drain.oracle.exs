defmodule Oracle do
  def spans() do
    %{
      "parse" => [%{inclusive: 12, self: 5}, %{inclusive: 8, self: 3}],
      "plan" => [%{inclusive: 40, self: 31}]
    }
  end

  def by_name(spans) do
    spans
    |> Enum.map(fn {name, ss} ->
      {name, "#{length(ss)}", "#{sum(ss, :inclusive)}", "#{sum(ss, :self)}"}
    end)
    |> table()
  end

  def sum(spans, key), do: spans |> Enum.map(&Map.fetch!(&1, key)) |> Enum.sum()

  def table(rows) do
    rows
    |> Enum.map(fn r -> r |> Tuple.to_list() |> Enum.map(&cell/1) end)
    |> Enum.zip_with(fn col -> col |> Enum.map(&String.length/1) |> Enum.max() end)
  end

  def cell(v) when is_binary(v), do: String.slice(v, 0, 70)

  def main() do
    IO.inspect(by_name(spans()))
  end
end

Oracle.main()
