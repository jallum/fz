defmodule Oracle do
  def wait_for(ms) do
    receive do
      :never -> :got
    after
      ms -> :timeout
    end
  end

  def run() do
    IO.inspect(wait_for(2 * 5))
    IO.inspect(:end)
  end
end

Oracle.run()
