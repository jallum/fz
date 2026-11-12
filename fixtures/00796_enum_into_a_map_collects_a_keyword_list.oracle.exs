defmodule Oracle do
  def main() do
    m = Enum.into([a: 1, b: 2], %{})
    IO.inspect(Enum.sort(Map.to_list(m)))
  end
end

Oracle.main()
