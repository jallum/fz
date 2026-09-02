defmodule P do
  def twice(f, x), do: f.(f.(x))
  def run(f, x), do: twice(f, x)
  def mk(c), do: fn n -> n + c end
end

send(self(), 1)
a = receive do v -> v end

f = case a > 0 do
  true -> P.mk(a)
  _ -> P.mk(0.5)
end
IO.inspect(P.run(f, 10))
