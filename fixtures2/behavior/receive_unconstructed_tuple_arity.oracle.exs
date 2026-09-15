defmodule M do
  def go do
    send(self(), {:a, 1})

    x =
      receive do
        {:a, n} -> n
        {:b, p, q, r} -> p + q + r
      end

    IO.inspect(x)
  end
end

M.go()
