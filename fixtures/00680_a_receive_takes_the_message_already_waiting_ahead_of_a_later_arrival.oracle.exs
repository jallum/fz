defmodule Oracle do
  def run() do
    me = self()
    spawn(fn -> send(me, :child) end)
    send(me, :parent)
    v = receive do
      :child -> :got_child
      :parent -> :got_parent
    end
    IO.inspect(v)
  end
end

Oracle.run()
