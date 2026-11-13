defmodule Pt do
  defstruct [:x, :y]
end

defmodule Size do
  defstruct [:w]
end

defprotocol Describe do
  def describe(value)
end

defimpl Describe, for: Map do
  def describe(_map), do: :map
end

defimpl Describe, for: Pt do
  def describe(p), do: {:pt, p.x}
end

defimpl Describe, for: Size do
  def describe(_size), do: :size
end

defmodule Oracle do
  def through(v), do: Describe.describe(v)

  def run do
    p = %Pt{x: 1, y: 2}
    IO.inspect(Describe.describe(p))
    IO.inspect(Describe.describe(%Size{w: 3}))
    IO.inspect(Describe.describe(%{x: 1}))
    IO.inspect(Describe.describe(%{}))
    IO.inspect(through(p))
    IO.inspect(through(%{x: 1}))
    IO.inspect(through(Map.put(p, :z, 3)))
    IO.inspect(through(Map.put(%{x: 1}, :z, 3)))
    IO.inspect(through(%{__struct__: Pt, x: 5, y: 6}))
    IO.inspect(through(Map.put(p, :__struct__, Size)))
    IO.inspect(Describe.describe(Map.put(p, :z, 3)))
    IO.inspect(Describe.describe(Map.merge(p, %{x: 8})))
    IO.inspect(Enum.to_list(MapSet.new([3, 1, 2])))
    IO.inspect(Enum.to_list(%{a: 1}))
    IO.inspect(Enum.to_list(1..3))
  end
end

Oracle.run()
