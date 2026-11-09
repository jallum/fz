defmodule Oracle do
  def run() do
  IO.inspect(System.argv())
  IO.inspect(Enum.map(System.argv(), fn arg -> byte_size(arg) end))
  end
end

Oracle.run()
