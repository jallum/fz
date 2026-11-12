defmodule Oracle do
  def main() do
    IO.inspect(for x <- 1..4, do: x * x)
  end
end

Oracle.main()
