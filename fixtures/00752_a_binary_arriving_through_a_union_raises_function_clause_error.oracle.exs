defmodule M do
  @spec f(integer) :: integer
  def f(x) when is_integer(x), do: x + 1
end

try do
  M.f(hd(["x", 1]))
  raise "no exception was raised"
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
