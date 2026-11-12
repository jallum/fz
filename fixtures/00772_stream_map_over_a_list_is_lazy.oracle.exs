defmodule Oracle do
  def run() do
    stream = Stream.map([1, 2, 3], fn x -> IO.inspect(x) end)
    IO.inspect(:built)
    IO.inspect(Enum.take(stream, 1))
  end
end

Oracle.run()
