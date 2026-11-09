defprotocol Sz do
  def sz(x)
end

defimpl Sz, for: List do
  def sz(list), do: length(list)
end

defimpl Sz, for: Map do
  def sz(map), do: map_size(map)
end

defmodule Measure do
  @spec c(Sz.t()) :: integer
  def c(x), do: Sz.sz(x)
end

decoded = JSON.decode!("[\"fz\",\"x\"]")

IO.inspect(Enum.count(decoded))
IO.inspect(Enum.map(decoded, fn word -> word <> "!" end))
IO.inspect(Measure.c(decoded))
IO.inspect(Measure.c([1, 2, 3]))
