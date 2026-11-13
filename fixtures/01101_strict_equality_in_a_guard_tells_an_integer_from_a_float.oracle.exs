defmodule Oracle do
  def same_as_one(n) when n === 1, do: :a
  def same_as_one(_), do: :b

  def differs_from_one(n) when n !== 1, do: :a
  def differs_from_one(_), do: :b

  def same_as_float(n) when n === 1.0, do: :a
  def same_as_float(_), do: :b

  def same_as_zero(n) when n === 0.0, do: :a
  def same_as_zero(_), do: :b

  def same_as_atom(n) when n === :x, do: :a
  def same_as_atom(_), do: :b

  def pair_same(a, b) when a === b, do: :a
  def pair_same(_, _), do: :b

  def pair_differs(a, b) when a !== b, do: :a
  def pair_differs(_, _), do: :b

  def receive_same(m) do
    send(self(), m)
    receive do
      n when n === 1 -> :a
      _ -> :b
    end
  end

  def receive_differs(m) do
    send(self(), m)
    receive do
      n when n !== 1 -> :a
      _ -> :b
    end
  end

  def receive_pair(m, k) do
    send(self(), m)
    receive do
      n when n === k -> :a
      _ -> :b
    end
  end

  def receive_float(m) do
    send(self(), m)
    receive do
      n when n === 1.0 -> :a
      _ -> :b
    end
  end
end

IO.inspect([Oracle.same_as_one(1), Oracle.same_as_one(1.0), Oracle.same_as_one(:x), Oracle.same_as_one([1])])
IO.inspect([Oracle.differs_from_one(1), Oracle.differs_from_one(1.0), Oracle.differs_from_one(:x), Oracle.differs_from_one([1])])
IO.inspect([Oracle.same_as_float(1), Oracle.same_as_float(1.0), Oracle.same_as_float(:x)])
IO.inspect([Oracle.same_as_zero(0.0), Oracle.same_as_zero(-0.0), Oracle.same_as_zero(0)])
IO.inspect([Oracle.same_as_atom(:x), Oracle.same_as_atom(:y), Oracle.same_as_atom(1)])
IO.inspect([Oracle.pair_same(1, 1), Oracle.pair_same(1, 1.0), Oracle.pair_same(:x, :x), Oracle.pair_same([1, 2], [1, 2]), Oracle.pair_same([1, 2], [1.0, 2])])
IO.inspect([Oracle.pair_differs(1, 1), Oracle.pair_differs(1, 1.0), Oracle.pair_differs([1, 2], [1, 2]), Oracle.pair_differs([1, 2], [1.0, 2])])
IO.inspect([Oracle.receive_same(1), Oracle.receive_same(1.0), Oracle.receive_same(:x)])
IO.inspect([Oracle.receive_differs(1), Oracle.receive_differs(1.0), Oracle.receive_differs(:x)])
IO.inspect([Oracle.receive_pair([1, 2], [1, 2]), Oracle.receive_pair([1, 2], [1.0, 2]), Oracle.receive_pair(1, 1.0), Oracle.receive_pair(:x, :x)])
IO.inspect([Oracle.receive_float(1.0), Oracle.receive_float(1), Oracle.receive_float(:x)])
