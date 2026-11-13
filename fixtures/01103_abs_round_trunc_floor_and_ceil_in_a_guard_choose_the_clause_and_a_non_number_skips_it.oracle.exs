defmodule Oracle do
  def entry_abs(n) when abs(n) > 2, do: :a
  def entry_abs(_), do: :b

  def receive_abs(m) do
    send(self(), m)
    receive do
      n when abs(n) > 2 -> :a
      _ -> :b
    end
  end

  def entry_round(n) when round(n) == 3, do: :a
  def entry_round(_), do: :b

  def receive_round(m) do
    send(self(), m)
    receive do
      n when round(n) == 3 -> :a
      _ -> :b
    end
  end

  def entry_trunc(n) when trunc(n) == -2, do: :a
  def entry_trunc(_), do: :b

  def receive_trunc(m) do
    send(self(), m)
    receive do
      n when trunc(n) == -2 -> :a
      _ -> :b
    end
  end

  def entry_floor(n) when floor(n) == -3, do: :a
  def entry_floor(_), do: :b

  def receive_floor(m) do
    send(self(), m)
    receive do
      n when floor(n) == -3 -> :a
      _ -> :b
    end
  end

  def entry_ceil(n) when ceil(n) == -2, do: :a
  def entry_ceil(_), do: :b

  def receive_ceil(m) do
    send(self(), m)
    receive do
      n when ceil(n) == -2 -> :a
      _ -> :b
    end
  end
end

IO.inspect([Oracle.entry_abs(-3), Oracle.entry_abs(2), Oracle.entry_abs(-2.5), Oracle.entry_abs(2.0), Oracle.entry_abs(:x), Oracle.entry_abs("s")])
IO.inspect([Oracle.receive_abs(-3), Oracle.receive_abs(2), Oracle.receive_abs(-2.5), Oracle.receive_abs(2.0), Oracle.receive_abs(:x), Oracle.receive_abs("s")])
IO.inspect([Oracle.entry_round(2.5), Oracle.entry_round(3), Oracle.entry_round(2.4), Oracle.entry_round(3.4999), Oracle.entry_round(-2.5), Oracle.entry_round(:x)])
IO.inspect([Oracle.receive_round(2.5), Oracle.receive_round(3), Oracle.receive_round(2.4), Oracle.receive_round(3.4999), Oracle.receive_round(-2.5), Oracle.receive_round(:x)])
IO.inspect([Oracle.entry_trunc(-2.7), Oracle.entry_trunc(-2), Oracle.entry_trunc(-2.0), Oracle.entry_trunc(-1.9), Oracle.entry_trunc(-3.5), Oracle.entry_trunc(:x)])
IO.inspect([Oracle.receive_trunc(-2.7), Oracle.receive_trunc(-2), Oracle.receive_trunc(-2.0), Oracle.receive_trunc(-1.9), Oracle.receive_trunc(-3.5), Oracle.receive_trunc(:x)])
IO.inspect([Oracle.entry_floor(-2.5), Oracle.entry_floor(-3), Oracle.entry_floor(-2.9), Oracle.entry_floor(-3.0), Oracle.entry_floor(-2), Oracle.entry_floor(:x)])
IO.inspect([Oracle.receive_floor(-2.5), Oracle.receive_floor(-3), Oracle.receive_floor(-2.9), Oracle.receive_floor(-3.0), Oracle.receive_floor(-2), Oracle.receive_floor(:x)])
IO.inspect([Oracle.entry_ceil(-2.5), Oracle.entry_ceil(-2), Oracle.entry_ceil(-1.9), Oracle.entry_ceil(-2.0), Oracle.entry_ceil(-3), Oracle.entry_ceil(:x)])
IO.inspect([Oracle.receive_ceil(-2.5), Oracle.receive_ceil(-2), Oracle.receive_ceil(-1.9), Oracle.receive_ceil(-2.0), Oracle.receive_ceil(-3), Oracle.receive_ceil(:x)])
