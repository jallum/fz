defmodule Oracle do
  def main() do
    IO.inspect(for x <- [2, 3], into: [1], do: x)
  end
end

Oracle.main()
