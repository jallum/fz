defmodule Oracle do
  def add(x, y) when is_integer(x) and is_integer(y), do: x + y
end

send(self(), 1.5)

receive do
  x ->
    try do
      IO.inspect(Oracle.add(x, 1))
    rescue
      e -> IO.inspect(e.__struct__)
    end
end
