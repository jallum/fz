defmodule Oracle do
  def naïve(x), do: x * 2
end

IO.inspect(Oracle.naïve(21))
