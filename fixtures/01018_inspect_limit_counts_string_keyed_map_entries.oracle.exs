defmodule Oracle do
  def main() do
    IO.inspect(inspect(%{"a" => 1, "b" => 2, "c" => 3}, limit: 2))
    IO.inspect(inspect(%{"a" => 1, "b" => 2, "c" => 3}, limit: 1))
    IO.inspect(inspect(%{"a" => 1, "b" => 2, "c" => 3}, limit: 3))
    IO.inspect(inspect(%{[1, 2, 3] => [4, 5, 6]}, limit: 4))
    IO.inspect(inspect(%{[1, 2, 3] => [4, 5, 6]}, limit: 3))
    IO.inspect(inspect(%{"a" => [1, 2, 3], "b" => 2}, limit: 3))
  end
end

Oracle.main()
