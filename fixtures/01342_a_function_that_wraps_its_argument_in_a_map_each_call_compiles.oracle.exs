defmodule Wrap do
  def m(acc, 0), do: acc
  def m(acc, n), do: m(%{k: acc}, n - 1)
end

IO.inspect(Wrap.m(1, 3))
