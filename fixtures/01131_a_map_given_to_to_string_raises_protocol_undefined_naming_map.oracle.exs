defmodule Oracle do
  def run() do
    IO.puts(to_string(Map.put(%{}, "a", 1)))
  end
end

try do
  Oracle.run()
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
