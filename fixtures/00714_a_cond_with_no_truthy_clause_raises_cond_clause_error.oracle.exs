defmodule Oracle do
  defp two(), do: Enum.at([2], 0)

  def run() do
    x = two()
    result = cond do
      x == 1 -> :one
      x > 5 -> :many
    end
    IO.inspect(result)
  end
end

try do
  Oracle.run()
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
