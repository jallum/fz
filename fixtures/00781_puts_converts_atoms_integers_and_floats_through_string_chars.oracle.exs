defmodule Oracle do
  def run() do
    IO.puts(:atom)
    IO.puts(1)
    IO.puts(1.5)
    IO.puts(-0.25)
    IO.puts(nil)
    IO.puts(true)
    IO.write(:w)
    IO.write(42)
    IO.write("\n")
  end
end

Oracle.run()
