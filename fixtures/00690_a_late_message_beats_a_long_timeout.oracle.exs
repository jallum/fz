defmodule Oracle do
  def run() do
    parent = self()
    spawn(fn ->
      receive do
        :never -> :ok
      after
        30 -> send(parent, :late)
      end
    end)
    receive do
      :late -> IO.inspect(:late)
    after
      2000 -> IO.inspect(:timeout)
    end
    IO.inspect(:end)
  end
end

Oracle.run()
