defmodule Oracle do
  def main() do
    IO.inspect(inspect(%{"metadata" => %{"a" => 1, "b" => 2, "c" => 3, "d" => 4, "e" => 5, "f" => 6}, "x" => 1}, limit: 6))
    IO.inspect(inspect(%{"m" => %{"a" => 1, "b" => 2}, "n" => %{"c" => 3}}, limit: 4))
    IO.inspect(inspect(%{"m" => %{"a" => 1, "b" => 2}, "n" => %{"c" => 3}}, limit: 100))
    IO.inspect(inspect(%{"m" => %{}}, limit: 1))
  end
end

Oracle.main()
