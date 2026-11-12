defmodule Oracle do
  def run() do
    IO.puts("")
    IO.puts("a\nb")
    IO.write("a")
    IO.write("b\n")
    IO.write("")
    IO.puts("end")
  end
end

Oracle.run()
