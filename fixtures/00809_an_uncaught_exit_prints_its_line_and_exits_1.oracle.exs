defmodule Oracle do
  def run() do
    IO.inspect(:before)
    exit({:bad, :reason})
  end
end

try do
  Oracle.run()
catch
  kind, value -> IO.puts(Exception.format_banner(kind, value, __STACKTRACE__))
end
