defmodule Oracle do
  def run() do
    IO.inspect(IO.puts("x"))
    IO.inspect(IO.write("y\n"))
    IO.inspect(IO.inspect([1, "s"]))
    IO.inspect(IO.inspect(1))
    IO.inspect(IO.inspect({:a, 2.5}))
  end
end

Oracle.run()
