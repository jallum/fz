defmodule Oracle do
  def run() do
    try do
      :unexpected
    rescue
      _ -> :inner_rescue
    else
      :expected -> :ok
    end
  end
end

try do
  Oracle.run()
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
