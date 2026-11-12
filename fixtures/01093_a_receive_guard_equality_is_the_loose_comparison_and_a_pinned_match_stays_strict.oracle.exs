defmodule Oracle do
  def int_eq_float(n) when n == 1.0, do: :a
  def int_eq_float(_), do: :b
  def float_eq_int(n) when n == 1, do: :a
  def float_eq_int(_), do: :b
  def float_neq_int(n) when n != 1, do: :a
  def float_neq_int(_), do: :b
  def zero_eq_negative_zero(n) when n == 0.0, do: :a
  def zero_eq_negative_zero(_), do: :b
  def pair_eq({a, b}) when a == b, do: :a
  def pair_eq(_), do: :b
  def pinned(pin, m) do
    case m do
      ^pin -> :a
      _ -> :b
    end
  end
end

IO.inspect([
  Oracle.int_eq_float(1),
  Oracle.int_eq_float(2),
  Oracle.float_eq_int(1.0),
  Oracle.float_neq_int(1.0),
  Oracle.float_neq_int(2.0),
  Oracle.zero_eq_negative_zero(-0.0),
  Oracle.pair_eq({1, 1.0}),
  Oracle.pair_eq({1, 2.0}),
  Oracle.pinned(1, 1.0),
  Oracle.pinned(1.0, 1),
  Oracle.pinned(1, 1),
  1 === 1.0,
  1 == 1.0
])
