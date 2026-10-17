defmodule Oracle do
  defguard isint(v) when is_integer(v)
  defguard isb(v) when is_binary(v)
  defguard isf(v) when is_float(v)
  defguard pair_of_ints(a, b) when is_integer(a) and is_integer(b)
  defguard islist(v) when v == [] or is_list(v)

  def int_cell(v) when isint(v), do: "int"
  def int_cell(_), do: "other"

  def bin_cell(v) when isb(v), do: "binary"
  def bin_cell(_), do: "other"

  def float_cell(v) when isf(v), do: "float"
  def float_cell(_), do: "other"

  def pair_cell(a, b) when pair_of_ints(a, b), do: "ints"
  def pair_cell(_, _), do: "other"

  def list_cell(v) when islist(v), do: "list"
  def list_cell(_), do: "other"

  def run do
    IO.inspect([isint(1), isint("x"), isint(1.5), isint(nil)])
    IO.inspect([int_cell(1), int_cell("x"), int_cell(:a), int_cell(1.5)])

    IO.inspect([isb("x"), isb(1), isb([1]), isb(nil)])
    IO.inspect([bin_cell("x"), bin_cell(1), bin_cell([1]), bin_cell(nil)])

    IO.inspect([isf(1.5), isf(1), isf("x")])
    IO.inspect([float_cell(1.5), float_cell(1), float_cell("x")])

    IO.inspect([pair_of_ints(1, 2), pair_of_ints(1, "x"), pair_of_ints("x", 2)])
    IO.inspect([pair_cell(1, 2), pair_cell(1, "x"), pair_cell("x", 2), pair_cell("x", "y")])

    IO.inspect([islist([]), islist([1]), islist(1)])
    IO.inspect([list_cell([]), list_cell([1]), list_cell(1)])
  end
end

Oracle.run()
