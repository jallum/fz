defmodule Oracle do
  def main() do
    IO.inspect(Enum.sort(Enum.into(%{1 => 10, 2 => 20}, [])))
  end
end

Oracle.main()
