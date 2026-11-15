defmodule Wrap do
  def f(x, 0), do: x
  def f(x, n), do: f({x}, n - 1)
end

IO.inspect(Wrap.f(1, 3))
