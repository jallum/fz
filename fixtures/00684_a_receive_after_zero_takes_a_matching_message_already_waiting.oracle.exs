defmodule Oracle do
  def run() do
    send(self(), :here)
    v = receive do
      :here -> :got
    after 0 -> :after
    end
    IO.inspect(v)
  end
end

Oracle.run()
