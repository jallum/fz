defmodule Oracle do
  def run() do
    me = self()
    spawn(fn -> send(me, :c1) end)
    spawn(fn -> send(me, :c2) end)
    send(me, :p)
    a = receive do
      x -> x
    end
    b = receive do
      x -> x
    end
    c = receive do
      x -> x
    end
    IO.inspect({a, b, c})
  end
end

Oracle.run()
