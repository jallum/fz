defmodule M do
  @spec f(integer) :: integer
  def f(x) when is_integer(x), do: x + 1
end

IO.inspect(M.f(hd([1, "x"])))
