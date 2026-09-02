defmodule P do
  def twice(f, x), do: f.(f.(x))
  def run(f, x), do: twice(f, x)
  def mk(c), do: fn n -> n + c end
end

defmodule Q do
  def twice(f, x), do: f.(f.(x))
  def run(f, x), do: twice(f, x)
  def mk(c), do: fn n -> n + c end
end

IO.inspect(P.run(P.mk(1), 10))
IO.inspect(P.run(P.mk(0.5), 10))
IO.inspect(Q.run(Q.mk(0.5), 10))
IO.inspect(Q.run(Q.mk(1), 10))
