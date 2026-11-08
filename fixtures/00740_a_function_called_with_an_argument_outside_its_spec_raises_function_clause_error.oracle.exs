defmodule M do
  @spec f(integer) :: integer
  @spec f(float) :: integer
  def f(x) when is_integer(x), do: x + 1
  def f(x) when is_float(x), do: 0
end

try do
  M.f(hd(["s"]))
  raise "no exception was raised"
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
