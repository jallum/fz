defmodule Oracle do
  def main() do
    records = ["{\"metadata\": {\"session\": {\"work_starts\": [1, 2, 3]}}}"] |> Stream.map(&JSON.decode!/1) |> Enum.to_list()
    [v | _] = for %{"metadata" => %{"session" => %{"work_starts" => s}}} <- records, do: s
    x = Enum.reduce(v, 0, fn _e, acc -> acc + 1 end)
    y = Enum.reduce(v, %{}, fn e, acc -> Map.put(acc, :k, e) end)
    IO.inspect({x, y})
  end
end

Oracle.main()
