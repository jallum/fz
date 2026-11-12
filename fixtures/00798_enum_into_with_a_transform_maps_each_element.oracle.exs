defmodule Oracle do
  def main() do
    m = Enum.into([1, 2, 3], %{}, fn x -> {x, x * 10} end)
    IO.inspect(Enum.sort(Map.to_list(m)))
  end
end

Oracle.main()
