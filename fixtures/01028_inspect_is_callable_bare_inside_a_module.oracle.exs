defmodule Shape do
  def show(value), do: inspect(value)
  def show(value, limit), do: inspect(value, limit: limit)
end
defmodule Oracle do
  def main() do
    IO.inspect(Shape.show(%{"a" => [1, 2]}))
    IO.inspect(Shape.show([1, 2, 3], 2))
    IO.inspect(Shape.show({:ok, "v"}, :infinity))
  end
end

Oracle.main()
