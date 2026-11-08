defmodule Oracle do
  def main() do
    m = Enum.into([{1, :a}, {2, :b}, {3, :c}], %{})
    IO.inspect(Enum.sort(Map.to_list(m)))
  end
end

Oracle.main()
