defmodule Oracle do
  def run() do
    IO.inspect(:before)
    raise "boom"
    IO.inspect(:never_printed)
  end
end

try do
  Oracle.run()
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
