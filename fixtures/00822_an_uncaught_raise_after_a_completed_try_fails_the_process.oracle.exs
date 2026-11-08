defmodule Oracle do
  def run() do
    result = try do
      raise ArgumentError, "caught"
    rescue
      e in ArgumentError -> e.message
    end
    IO.inspect(result)
    raise ArgumentError, "uncaught"
  end
end

try do
  Oracle.run()
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
