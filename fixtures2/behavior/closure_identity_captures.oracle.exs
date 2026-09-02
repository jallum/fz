defmodule Pipeline do
  def apply_twice(f, x), do: f.(f.(x))
  def run(f, x), do: apply_twice(f, x)
end

a = 1
b = 100
IO.inspect(Pipeline.run(fn n -> n + a end, 10))
IO.inspect(Pipeline.run(fn n -> n + b end, 10))
