defmodule Tagged do
  def tag({:cont, n}) when is_integer(n), do: 1
  def tag({:halt, n}) when is_integer(n), do: 2

  def gat({:halt, n}) when is_integer(n), do: 2
  def gat({:cont, n}) when is_integer(n), do: 1

  def pick(n) do
    if n > 0 do
      {:cont, n}
    else
      {:halt, n}
    end
  end
end

IO.inspect(Tagged.tag(Tagged.pick(1)))
IO.inspect(Tagged.tag(Tagged.pick(0)))
IO.inspect(Tagged.gat(Tagged.pick(1)))
IO.inspect(Tagged.gat(Tagged.pick(0)))
