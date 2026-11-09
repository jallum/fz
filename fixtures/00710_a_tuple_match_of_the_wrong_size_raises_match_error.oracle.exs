defmodule Oracle do
  defp pair(), do: Enum.at([{1, 2}], 0)

  def run() do
    IO.inspect(:before)
    {only} = pair()
    IO.inspect(only)
  end
end

try do
  Oracle.run()
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
