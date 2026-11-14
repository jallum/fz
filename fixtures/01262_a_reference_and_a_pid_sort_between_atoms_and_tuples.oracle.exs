defmodule Oracle do
  def word(x) when is_integer(x), do: :integer
  def word(x) when is_float(x), do: :float
  def word(x) when is_atom(x), do: :atom
  def word(x) when is_reference(x), do: :reference
  def word(x) when is_function(x), do: :function
  def word(x) when is_pid(x), do: :pid
  def word(x) when is_tuple(x), do: :tuple
  def word(x) when is_map(x), do: :map
  def word(x) when is_list(x), do: :list
  def word(x) when is_binary(x), do: :bitstring

  def main() do
    values = [self(), "b", [1], %{a: 1}, {1}, fn -> 1 end, make_ref(), :a, 2.5, 1]
    IO.puts(values |> Enum.sort() |> Enum.map(&word/1) |> Enum.join(" "))
    IO.puts(values |> Enum.sort(fn a, b -> a >= b end) |> Enum.map(&word/1) |> Enum.join(" "))
    r = make_ref()
    f = fn -> 1 end
    p = self()
    IO.inspect({1 < r, :z < r, r < f, f < p, r < p, p < {1}, p > r, r > :z, r > 2.5, p < [], p < "b"})
  end
end

Oracle.main()
