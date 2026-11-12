defmodule Oracle do
  def float_over_float(n) when n > 1.5, do: :a
  def float_over_float(_), do: :b
  def int_at_least_float(n) when n >= 1.0, do: :a
  def int_at_least_float(_), do: :b
  def float_at_most_int(n) when n <= 2, do: :a
  def float_at_most_int(_), do: :b
  def int_below_atom(n) when n < :b, do: :a
  def int_below_atom(_), do: :b
  def atom_over_int(n) when n > 3, do: :a
  def atom_over_int(_), do: :b
  def int_over_int(n) when n > 1, do: :a
  def int_over_int(_), do: :b
end

IO.inspect([
  Oracle.float_over_float(2.0),
  Oracle.float_over_float(1.0),
  Oracle.int_at_least_float(1),
  Oracle.int_at_least_float(0),
  Oracle.float_at_most_int(2.5),
  Oracle.float_at_most_int(1.5),
  Oracle.int_below_atom(1),
  Oracle.atom_over_int(:x),
  Oracle.int_over_int(2),
  Oracle.int_over_int(1)
])
