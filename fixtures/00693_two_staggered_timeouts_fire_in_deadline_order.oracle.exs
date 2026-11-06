defmodule Oracle do
  def run() do
    parent = self()
    spawn(fn ->
      receive do
        :never -> :ok
      after
        80 -> send(parent, :slow)
      end
    end)
    spawn(fn ->
      receive do
        :never -> :ok
      after
        20 -> send(parent, :fast)
      end
    end)
    receive do
      first -> IO.inspect(first)
    end
    receive do
      second -> IO.inspect(second)
    end
  end
end

Oracle.run()
