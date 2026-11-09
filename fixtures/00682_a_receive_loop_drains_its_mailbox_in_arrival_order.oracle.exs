defmodule Oracle do
  def drain(0, acc), do: acc
  def drain(n, acc) do
    m = receive do
      x -> x
    end
    drain(n - 1, [m | acc])
  end

  def run() do
    me = self()
    spawn(fn -> send(me, :c1) end)
    spawn(fn -> send(me, :c2) end)
    send(me, :p1)
    send(me, :p2)
    IO.inspect(drain(4, []))
  end
end

Oracle.run()
