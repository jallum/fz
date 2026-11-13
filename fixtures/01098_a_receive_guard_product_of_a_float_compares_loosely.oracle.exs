defmodule Oracle do
  def entry(n) when n * 2 == 3, do: :a
  def entry(_), do: :b

  def receive_product(m) do
    send(self(), m)

    receive do
      n when n * 2 == 3 -> :a
      _ -> :b
    end
  end
end

IO.inspect([Oracle.entry(1.5), Oracle.entry(2), Oracle.receive_product(1.5), Oracle.receive_product(2)])
