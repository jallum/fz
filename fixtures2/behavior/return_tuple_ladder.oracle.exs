defmodule Ladder do
  def build(0), do: :start
  def build(n), do: {n, build(n - 1)}
end

IO.inspect(Ladder.build(3))
