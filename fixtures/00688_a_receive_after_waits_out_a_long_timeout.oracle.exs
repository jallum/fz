defmodule Oracle do
  def run() do
    receive do
      :never -> IO.inspect(:got)
    after
      1500 -> IO.inspect(:timeout)
    end
    IO.inspect(:end)
  end
end

Oracle.run()
