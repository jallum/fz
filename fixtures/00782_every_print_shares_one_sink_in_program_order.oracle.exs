defmodule Oracle do
  def run() do
    IO.puts("one")
    IO.write("two ")
    IO.inspect(:three)
    IO.inspect("four")
    IO.write("five")
    IO.puts("")
    IO.inspect({:six, 6})
    IO.puts("seven")
    IO.inspect([8, 9.5])
  end
end

Oracle.run()
