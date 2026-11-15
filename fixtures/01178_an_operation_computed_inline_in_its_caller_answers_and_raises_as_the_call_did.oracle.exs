defmodule Inline do
  def sum_then_double(a, b), do: double(a + b)
  def double(x), do: x * 2 + 1

  def integer_plus_float(a, b), do: wrap(a + b)
  def float_plus_integer(a, b), do: wrap(a + b)
  def wrap(x), do: {:sum, x}

  def sizes(bin, map), do: pair(byte_size(bin), map_size(map))
  def pair(a, b), do: {a, b}

  def quotient(a, b), do: double(div(a, b))

  def attempt(a, b) do
    try do
      quotient(a, b)
    rescue
      e in ArithmeticError -> {:rescued, e.message}
    end
  end
end

IO.inspect(Inline.sum_then_double(3, 4))
IO.inspect(Inline.integer_plus_float(1, 2.5))
IO.inspect(Inline.float_plus_integer(2.5, 1))
IO.inspect(Inline.sizes("héllo", %{a: 1, b: 2}))
IO.inspect(Inline.attempt(7, 2))
IO.inspect(Inline.attempt(7, 0))
