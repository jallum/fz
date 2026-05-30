defmodule M do
  def double(x), do: x * 2
  def sum3(a, b, c), do: a + b + c
end

x = M.double(21)
IO.inspect(x)
y = M.sum3(1, 2, 3)
IO.inspect(y)
