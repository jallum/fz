defmodule My do
  def rev([], tail), do: tail
  def rev([h | t], acc), do: rev(t, [h | acc])
end

acc = Enum.reverse([1, 2, 3], [])
IO.inspect(acc)
IO.inspect(Enum.reverse(acc, []))
IO.inspect(Enum.reverse(Enum.reverse([4, 5, 6], []), []))

mine = My.rev([1, 2, 3], [])
IO.inspect(mine)
IO.inspect(My.rev(mine, []))
