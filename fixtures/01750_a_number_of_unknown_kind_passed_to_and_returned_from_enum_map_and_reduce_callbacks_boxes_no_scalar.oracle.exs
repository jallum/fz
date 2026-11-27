defmodule P do
  def opaque(x) do
    send(self(), x)

    receive do
      value -> value
    end
  end

  def bump(list, up) do
    Enum.map(list, if(up, do: fn x -> x + 1 end, else: fn x -> x - 1 end))
  end

  def total(list, up) do
    Enum.reduce(list, 0, if(up, do: fn x, acc -> acc + x end, else: fn x, acc -> acc - x end))
  end

  def repeat(0, _list, acc), do: acc

  def repeat(n, list, acc) do
    repeat(n - 1, list, acc + length(bump(list, P.opaque(true))) + total(list, P.opaque(true)))
  end
end

list = [1, 2.5, 3, 4.5]
IO.inspect(P.bump(list, P.opaque(true)))
IO.inspect(P.bump(list, P.opaque(false)))
IO.inspect(P.total(list, P.opaque(true)))
IO.inspect(P.total(list, P.opaque(false)))

IO.inspect(P.repeat(1000, list, 0))
