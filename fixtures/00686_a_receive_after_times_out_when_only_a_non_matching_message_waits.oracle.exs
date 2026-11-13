defmodule Oracle do
  def run() do
    send(self(), :other)
    receive do
      :never -> IO.inspect(:got)
    after
      1 -> IO.inspect(:timeout)
    end
    IO.inspect(:end)
  end
end

Oracle.run()
