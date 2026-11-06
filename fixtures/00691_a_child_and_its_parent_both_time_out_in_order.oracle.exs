defmodule Oracle do
  def run() do
    parent = self()
    spawn(fn ->
      receive do
        :never -> :ok
      after
        20 ->
          IO.inspect(:child_timeout)
          send(parent, :child_done)
      end
    end)
    receive do
      :never -> IO.inspect(:got)
    after
      80 -> IO.inspect(:main_timeout)
    end
    receive do
      :child_done -> IO.inspect(:joined)
    end
  end
end

Oracle.run()
