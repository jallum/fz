defmodule Oracle do
  def main() do
    m = for x <- [1, 2, 3], into: %{}, do: {x, x * x}
    IO.inspect(Enum.sort(Map.to_list(m)))
  end
end

Oracle.main()
