defmodule Oracle do
  defp five(), do: Enum.at([5], 0)

  def run(), do: IO.inspect(five() and true)
end

try do
  Oracle.run()
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
