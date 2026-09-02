defmodule P do
  def twice(f, x, _t), do: f.(f.(x))
  def run(f, x, t), do: twice(f, x, t)
end

IO.inspect(P.run(fn n -> n + 1 end, 10, :a))
IO.inspect(P.run(fn n -> n * 3 end, 10, :b))
IO.inspect(P.run(fn n -> n + 1 end, 10, :b))
IO.inspect(P.run(fn n -> n * 3 end, 10, :a))
