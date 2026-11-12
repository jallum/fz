defmodule Oracle do
  def main() do
    spans = %{1 => %{name: "x", v: 1}, 2 => %{name: "y", v: 2}, 3 => %{name: "x", v: 3}}
    jobs = for {_id, %{name: "x"} = s} <- spans, do: s
    IO.inspect(Enum.sort(Enum.map(jobs, fn s -> Map.get(s, :v) end)))
  end
end

Oracle.main()
