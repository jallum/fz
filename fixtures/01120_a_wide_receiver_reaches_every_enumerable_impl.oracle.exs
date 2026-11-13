defmodule Oracle do
  def main() do
    IO.inspect(Enum.to_list(Stream.map(Map.put(%{}, 1, 1), & &1)))
    IO.inspect(Enum.to_list([2]))
  end
end

Oracle.main()
