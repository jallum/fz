defmodule Pt do
  defstruct [:x, :y]
end

defmodule Oracle do
  def kind(v) when is_map(v), do: :map
  def kind(_), do: :other

  def x_of(v) do
    case v do
      %{x: x} -> x
      _ -> :none
    end
  end

  def run do
    p = %Pt{x: 1, y: 2}
    IO.inspect(is_map(p))
    IO.inspect(kind(p))
    IO.inspect(kind({1, 2}))
    IO.inspect(map_size(p))
    IO.inspect(x_of(p))
    IO.inspect(x_of(%{x: 7}))
    IO.inspect(x_of(%{y: 7}))
    IO.inspect(x_of({1, 2}))
    IO.inspect(Map.get(p, :__struct__))
    IO.inspect(p.__struct__)
    IO.inspect(Map.get(p, :x))
    IO.inspect(Map.get(p, :x, :none))
    IO.inspect(Map.get(p, :z, :none))
    IO.inspect(Map.get(%Pt{x: :left, y: 2}, :x))
    IO.inspect(Map.get(%{x: :left}, :x))
    IO.inspect(Map.has_key?(p, :x))
    IO.inspect(Map.has_key?(p, :z))
    IO.inspect(Map.has_key?(p, :__struct__))
    IO.inspect(Map.merge(p, %{x: 9}).x)
    IO.inspect(Map.put(p, :y, 5))
    IO.inspect(Map.fetch(p, :y))
    send(self(), p)

    receive do
      %{y: y} -> IO.inspect({:map, y})
    end
  end
end

Oracle.run()
