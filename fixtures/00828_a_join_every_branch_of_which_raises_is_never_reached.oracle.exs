defmodule Oracle do
  def pick(x) do
    v = if x > 0 do
      raise ArgumentError, "positive"
    else
      raise ArgumentError, "not positive"
    end
    IO.inspect(v)
  end
end

try do
  Oracle.pick(0)
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
