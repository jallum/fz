defmodule Oracle do
  @spec f(integer) :: integer
  def f(x), do: x

  def run do
    send(self(), 1.5)

    receive do
      x -> IO.inspect(f(x))
    end
  end
end

Oracle.run()
