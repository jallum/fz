defmodule Oracle do
  def run() do
    send(self(), "ahi")
    receive do
      <<a, r::binary>> when a == 98 -> IO.inspect({:b, r})
      <<a, r::binary>> when a == 97 -> IO.inspect({:a, r})
    end
  end
end

Oracle.run()
