defmodule Oracle do
  def run() do
    IO.inspect(:before)
    [a, b] = Enum.take([1, 2], 1)
    IO.inspect({a, b})
  end
end

try do
  Oracle.run()
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
