defmodule Oracle do
  def main() do
    spans = %{1 => %{name: "a", v: 1}, 2 => %{name: "b", v: 2}, 3 => %{name: "a", v: 3}}
    r = Enum.reduce(spans, [], fn x, acc ->
      case x do
        {_id, %{name: "a"} = s} -> [Map.get(s, :v) + 1 | acc]
        _ -> acc
      end
    end)
    IO.inspect(Enum.reverse(r))
  end
end

Oracle.main()
