defmodule Oracle do
  def main() do
    IO.inspect(inspect([1], limit: 0))
    IO.inspect(inspect([], limit: 0))
    IO.inspect(inspect(%{"a" => 1}, limit: 0))
    IO.inspect(inspect(%{}, limit: 0))
    IO.inspect(inspect({1}, limit: 0))
    IO.inspect(inspect(<<1>>, limit: 0))
    IO.inspect(inspect("str", limit: 0))
    IO.inspect(inspect(1, limit: 0))
    IO.inspect(inspect(:ok, limit: 0))
    IO.inspect(inspect(Enum.to_list(1..150), limit: :infinity))
    IO.inspect(inspect(Enum.to_list(1..150), limit: 120))
    IO.inspect(inspect(Enum.to_list(1..150)))
  end
end

Oracle.main()
