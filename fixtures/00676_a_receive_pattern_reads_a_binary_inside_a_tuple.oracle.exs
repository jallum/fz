defmodule Oracle do
  def run() do
    send(self(), {:m, "xyz"})
    receive do
      {:m, <<a, r::binary>>} -> IO.inspect({a, r})
    end
  end
end

Oracle.run()
