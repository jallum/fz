defmodule P do
  def twice(f, x), do: f.(f.(x))
  def run(f, x), do: twice(f, x)
  def mk(c), do: fn n -> n + c end
end

a = 1
b = 0.5

IO.inspect(P.run(P.mk(a), 10))
IO.inspect(P.run(P.mk(b), 10))
IO.inspect(P.run(P.mk(1), 10))
IO.inspect(P.run(P.mk(0.5), 10))
