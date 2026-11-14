defmodule Oracle do
  @spec f(integer) :: integer
  def f(x), do: x

  def run do
    IO.inspect(f(3) + 1)
    send(self(), 1.5)

    receive do
      x -> IO.inspect(f(x) + 1)
    end
  end
end

Oracle.run()
