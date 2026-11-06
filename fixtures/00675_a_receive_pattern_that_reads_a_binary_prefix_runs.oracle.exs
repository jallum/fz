defmodule Oracle do
  def run() do
    send(self(), "--hi")
    receive do
      <<45, 45, r::binary>> -> IO.inspect(r)
    end
    send(self(), "--hi")
    receive do
      <<"--", r::binary>> -> IO.inspect(r)
    end
    send(self(), "--hi")
    receive do
      "--" <> r -> IO.inspect(r)
    end
  end
end

Oracle.run()
