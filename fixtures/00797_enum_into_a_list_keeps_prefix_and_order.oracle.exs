defmodule Oracle do
  def main() do
    IO.inspect(Enum.into([3, 4, 5], [1, 2]))
    IO.inspect(Enum.into(1..4, []))
  end
end

Oracle.main()
