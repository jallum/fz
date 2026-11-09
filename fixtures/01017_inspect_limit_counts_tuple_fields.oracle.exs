defmodule Oracle do
  def main() do
    IO.inspect(inspect({1, 2, 3}, limit: 2))
    IO.inspect(inspect({1, {2, 3}, 4}, limit: 2))
    IO.inspect(inspect({1, {2, 3}, 4}, limit: 3))
    IO.inspect(inspect({1, 2}, limit: 2))
    IO.inspect(inspect({}, limit: 0))
    IO.inspect(inspect({1}, limit: 0))
  end
end

Oracle.main()
