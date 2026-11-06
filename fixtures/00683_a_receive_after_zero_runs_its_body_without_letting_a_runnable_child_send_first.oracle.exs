defmodule Oracle do
  def run() do
    me = self()
    spawn(fn -> send(me, :child) end)
    receive do
      :never -> :ok
    after 0 -> send(me, :parent)
    end
    a = receive do
      x -> x
    end
    b = receive do
      x -> x
    end
    IO.inspect({a, b})
  end
end

Oracle.run()
