defmodule Oracle do
  def refused(f) do
    try do
      f.()
    rescue
      e in ArgumentError -> e.message
    end
  end

  def entry_hd(l) when hd(l) == 1, do: :a
  def entry_hd(_), do: :b

  def entry_tl(l) when length(tl(l)) == 1, do: :a
  def entry_tl(_), do: :b

  def entry_hd_tl(l) when hd(tl(l)) == 2, do: :a
  def entry_hd_tl(_), do: :b

  def receive_hd(m) do
    send(self(), m)
    receive do
      l when hd(l) == 1 -> :a
      _ -> :b
    end
  end

  def receive_tl(m) do
    send(self(), m)
    receive do
      l when length(tl(l)) == 1 -> :a
      _ -> :b
    end
  end
end

IO.inspect([hd([1, 2]), hd([[3]]), hd([:a, :b]), tl([1, 2]), tl([1]), tl([[1, 2]])])
IO.inspect(Oracle.refused(fn -> hd([]) end))
IO.inspect(Oracle.refused(fn -> hd("s") end))
IO.inspect(Oracle.refused(fn -> tl([]) end))
IO.inspect(Oracle.refused(fn -> tl(5) end))
IO.inspect([Oracle.entry_hd([1]), Oracle.entry_hd([2]), Oracle.entry_hd([]), Oracle.entry_hd(5)])
IO.inspect([Oracle.entry_tl([1, 2]), Oracle.entry_tl([1]), Oracle.entry_tl([]), Oracle.entry_tl(:x)])
IO.inspect([Oracle.entry_hd_tl([1, 2]), Oracle.entry_hd_tl([1, 3]), Oracle.entry_hd_tl([1]), Oracle.entry_hd_tl([])])
IO.inspect([Oracle.receive_hd([1]), Oracle.receive_hd([2]), Oracle.receive_hd([]), Oracle.receive_hd(5)])
IO.inspect([Oracle.receive_tl([1, 2]), Oracle.receive_tl([1]), Oracle.receive_tl([]), Oracle.receive_tl(:x)])
