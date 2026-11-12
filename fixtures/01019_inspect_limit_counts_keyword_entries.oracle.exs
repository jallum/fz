defmodule Oracle do
  def main() do
    IO.inspect(inspect([a: 1, b: 2, c: 3], limit: 2))
    IO.inspect(inspect([a: 1, b: 2, c: 3], limit: 3))
    IO.inspect(inspect(["foo bar": 1, b: [1, 2, 3]], limit: 3))
    IO.inspect(inspect([{:a, 1}, {"b", 2}], limit: 1))
    IO.inspect(inspect([a: [x: 1, y: 2], b: 2], limit: 3))
  end
end

Oracle.main()
