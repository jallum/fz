defmodule Oracle do
  def run() do
    parent = self()
    spawn(fn ->
      receive do
        :never -> :ok
      after
        2 -> send(parent, :slow)
      end
    end)
    spawn(fn ->
      receive do
        :never -> :ok
      after
        1 -> send(parent, :fast)
      end
    end)
    receive do
      :fast -> IO.inspect(:fast)
    end
    receive do
      :slow -> IO.inspect(:slow)
    end
  end
end

Oracle.run()
