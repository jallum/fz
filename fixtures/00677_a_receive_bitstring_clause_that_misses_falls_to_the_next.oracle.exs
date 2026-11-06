defmodule Oracle do
  def run() do
    send(self(), "xyz")
    receive do
      <<45, 45, r::binary>> -> IO.inspect({:dashes, r})
      other -> IO.inspect({:other, other})
    end
  end
end

Oracle.run()
