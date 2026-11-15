defmodule Wrap do
  def g(acc, 0), do: acc
  def g(acc, n), do: g([acc], n - 1)
end

IO.inspect(Wrap.g([], 3))
