defmodule Oracle do
  def run() do
    send(self(), {:plain, 7})
    receive do
      {:plain, n} -> IO.inspect(n)
    end
    send(self(), "--hi")
    receive do
      "--" <> r -> IO.inspect(r)
    end
  end
end

Oracle.run()
