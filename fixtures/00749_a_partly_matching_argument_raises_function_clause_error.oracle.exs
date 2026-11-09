defmodule M do
  @spec f(integer, integer) :: integer
  def f(x, y) when is_integer(x) and is_integer(y), do: x + y
end

try do
  M.f(Enum.at([1], 5), hd([1]))
  raise "no exception was raised"
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
