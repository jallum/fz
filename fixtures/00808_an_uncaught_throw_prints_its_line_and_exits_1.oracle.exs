defmodule Oracle do
  def run() do
    IO.inspect(:before)
    throw({:ball, 1})
  end
end

try do
  Oracle.run()
catch
  kind, value -> IO.puts(Exception.format_banner(kind, value, __STACKTRACE__))
end
