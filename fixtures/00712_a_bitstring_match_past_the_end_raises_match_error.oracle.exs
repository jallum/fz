defmodule Oracle do
  def run() do
    IO.inspect(:before)
    <<a::8>> = String.slice("x", 1, 1)
    IO.inspect(a)
  end
end

try do
  Oracle.run()
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
