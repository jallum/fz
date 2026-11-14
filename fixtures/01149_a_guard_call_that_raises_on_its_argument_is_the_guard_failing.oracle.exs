defmodule Oracle do
  def shape(x) when map_size(x) == 0, do: :empty_map
  def shape(x) when tuple_size(x) == 2, do: :pair
  def shape(x) when length(x) == 1, do: :singleton
  def shape(x) when hd(x) == :first, do: :headed
  def shape(_), do: :other

  def run() do
    IO.inspect(shape(%{}))
    IO.inspect(shape(%{a: 1}))
    IO.inspect(shape({1, 2}))
    IO.inspect(shape({1, 2, 3}))
    IO.inspect(shape([:only]))
    IO.inspect(shape([:first, :second]))
    IO.inspect(shape([]))
    IO.inspect(shape(:atom))
    IO.inspect(shape("text"))
    IO.inspect(shape(7))
  end
end

Oracle.run()
