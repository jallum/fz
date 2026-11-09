defmodule Oracle do
  def run() do
    parent = self()
    spawn(fn -> send(parent, :hello) end)
    receive do
      :hello -> IO.inspect(:hello)
    after
      200 -> IO.inspect(:timeout)
    end
    IO.inspect(:end)
  end
end

Oracle.run()
