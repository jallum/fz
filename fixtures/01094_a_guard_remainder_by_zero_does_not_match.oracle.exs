defmodule Oracle do
  def entry_by_zero(n) when rem(n, 0) == 1, do: :a
  def entry_by_zero(_), do: :b

  def entry_by_two(n) when rem(n, 2) == 1, do: :a
  def entry_by_two(_), do: :b

  def receive_by_zero(m) do
    send(self(), m)

    receive do
      n when rem(n, 0) == 1 -> :a
      _ -> :b
    end
  end

  def receive_by_two(m) do
    send(self(), m)

    receive do
      n when rem(n, 2) == 1 -> :a
      _ -> :b
    end
  end
end

IO.inspect([Oracle.entry_by_zero(5), Oracle.entry_by_two(5), Oracle.receive_by_zero(5), Oracle.receive_by_two(5)])
