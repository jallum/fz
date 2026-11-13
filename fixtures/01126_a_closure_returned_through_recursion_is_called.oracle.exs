defmodule M do
  def h(0), do: fn x -> x end
  def h(n), do: h(n - 1).(1)
end
IO.inspect(M.h(1))
