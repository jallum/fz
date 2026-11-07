defmodule Oracle do
  def run() do
    raise ArgumentError, "bad"
  end
end

try do
  Oracle.run()
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
