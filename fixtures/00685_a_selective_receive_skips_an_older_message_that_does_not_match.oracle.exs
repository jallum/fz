defmodule Oracle do
  def run() do
    me = self()
    spawn(fn -> send(me, :child) end)
    send(me, :x)
    send(me, :y)
    a = receive do
      :y -> :y
    end
    b = receive do
      :x -> :x
    end
    c = receive do
      :child -> :child
    end
    IO.inspect({a, b, c})
  end
end

Oracle.run()
