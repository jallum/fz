defmodule Oracle do
  defguardp first(l) when hd(l)

  def run do
    send(self(), [3])
    send(self(), :no)
    send(self(), [])
    send(self(), [4])

    receive do
      l when first(l) == 3 -> IO.inspect(:a)
    end

    for _ <- 1..3 do
      receive do
        l when first(l) == 3 -> IO.inspect(:a)
        _ -> IO.inspect(:b)
      end
    end
  end
end

Oracle.run()
