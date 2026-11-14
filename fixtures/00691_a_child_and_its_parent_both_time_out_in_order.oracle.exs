defmodule Oracle do
  def run() do
    parent = self()
    spawn(fn ->
      receive do
        :never -> :ok
      after
        1 ->
          IO.inspect(:child_timeout)
          send(parent, :child_done)
      end
    end)
    timed_out = receive do
      :never -> false
    after
      2 -> true
    end
    receive do
      :child_done -> IO.inspect(:joined)
    end
    IO.inspect({:main_timeout, timed_out})
  end
end

Oracle.run()
