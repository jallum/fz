defmodule Accumulator do
  def build(0, acc), do: acc
  def build(n, acc), do: build(n - 1, {n, acc})
end

IO.inspect(Accumulator.build(3, :start))
