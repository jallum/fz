defmodule M do
  def go(a), do: IO.inspect(a)
end

M.go(1)
IO.inspect(:between)
M.go(2)
