defmodule Point do
  defstruct x: 0
end

defmodule Oracle do
  def typed(t) when is_tuple(t), do: :tuple
  def typed(_), do: :other

  def guarded(t) when is_tuple(t), do: :tuple
  def guarded(_), do: :other

  def run do
    IO.inspect([typed({}), typed({1}), typed({1, 2, 3})])
    IO.inspect([typed(5), typed([1, 2]), typed(%{a: 1}), typed(%Point{x: 1})])
    IO.inspect([guarded({}), guarded({1}), guarded({1, 2, 3})])
    IO.inspect([guarded(5), guarded([1, 2]), guarded(%{a: 1}), guarded(%Point{x: 1})])
    IO.inspect([is_tuple({}), is_tuple({:a, :b}), is_tuple(5), is_tuple(%Point{x: 1})])
  end
end

Oracle.run()
