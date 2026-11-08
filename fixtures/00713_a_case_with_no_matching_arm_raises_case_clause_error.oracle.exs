defmodule Oracle do
  defp fetch(), do: Enum.at([{:error, 2}], 0)

  def run() do
    result = case fetch() do
      {:ok, n} -> n
    end
    IO.inspect(result)
  end
end

try do
  Oracle.run()
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
