defmodule Shapes do
  def sides(:triangle), do: 3
  def sides(:square), do: 4
end

defmodule Oracle do
  def run() do
    IO.inspect(Shapes.sides(:square))
    IO.inspect(Shapes.sides(String.to_atom("circle")))
    IO.inspect(:never_printed)
  end
end

try do
  Oracle.run()
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
