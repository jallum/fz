defmodule Oracle do
  def run() do
    :erlang.error({:stop, [1, 2]})
  end
end

try do
  Oracle.run()
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
