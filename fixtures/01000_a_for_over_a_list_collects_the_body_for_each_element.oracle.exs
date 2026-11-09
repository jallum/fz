defmodule Oracle do
  def main() do
    IO.inspect(for x <- [1, 2, 3], do: x * 2)
  end
end

Oracle.main()
