defmodule Oracle do
  def depth(0), do: raise "deep"
  def depth(n), do: depth(n - 1) + 1

  def run() do
    IO.inspect(depth(5))
    IO.inspect(:never_printed)
  end
end

try do
  Oracle.run()
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
