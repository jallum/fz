defmodule Oracle do
  defp fetch(), do: Enum.at([{:bad, 1}], 0)

  def run() do
    result = with {:ok, v} <- fetch() do
      v
    else
      :error -> :e
    end
    IO.inspect(result)
  end
end

try do
  Oracle.run()
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
