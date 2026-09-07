defmodule M do
  def go do
    IO.inspect({1 < 1.0, 1 <= 1.0, 1 > 1.0, 1 >= 1.0, 1 == 1.0, 1 != 1.0})
    IO.inspect({2 < 1.0, 2 <= 1.0, 2 > 1.0, 2 >= 1.0, 2 == 1.0, 2 != 1.0})
    IO.inspect({1 < 2.0, 1 <= 2.0, 1 > 2.0, 1 >= 2.0, 1 == 2.0, 1 != 2.0})

    IO.inspect({1.0 < 1, 1.0 <= 1, 1.0 > 1, 1.0 >= 1, 1.0 == 1, 1.0 != 1})
    IO.inspect({1.0 < 2, 1.0 <= 2, 1.0 > 2, 1.0 >= 2, 1.0 == 2, 1.0 != 2})
    IO.inspect({2.0 < 1, 2.0 <= 1, 2.0 > 1, 2.0 >= 1, 2.0 == 1, 2.0 != 1})

    IO.inspect({1 > 0.5, 1 < 0.5, 0 >= 0.0, 0 <= 0.0, 0 == 0.0})

    one = launder(1)
    two = launder(2)
    one_float = launder(1.0)
    two_float = launder(2.0)

    IO.inspect(
      {one < one_float, one <= one_float, one > one_float, one >= one_float, one == one_float,
       one != one_float}
    )

    IO.inspect(
      {two < one_float, two <= one_float, two > one_float, two >= one_float, two == one_float,
       two != one_float}
    )

    IO.inspect(
      {one < two_float, one <= two_float, one > two_float, one >= two_float, one == two_float,
       one != two_float}
    )

    IO.inspect(
      {one_float < one, one_float <= one, one_float > one, one_float >= one, one_float == one,
       one_float != one}
    )

    IO.inspect(
      {two_float < one, two_float <= one, two_float > one, two_float >= one, two_float == one,
       two_float != one}
    )

    IO.inspect({1 == 1, 1.0 == 1.0, 2 > 1, 2.0 > 1.0})
    IO.inspect({:a == :a, :a == :b, "x" == "x", [1, 2] == [1, 2], {1} == {1}})

    IO.inspect({ordering(one, one_float), ordering(two, one_float), ordering(one, two_float)})
    IO.inspect({ordering(one_float, one), ordering(two_float, one), ordering(one, two)})

    IO.inspect(Enum.sort(["pear", "apple", "fig", "Fig", ""]))
    IO.inspect({"apple" < "pear", "a" < "ab", "Z" < "a", "" < "a", "abc" <= "abd"})

    IO.inspect({literal(1), literal(1.0), literal(2)})
  end

  defp ordering(a, b) when a < b, do: :lt
  defp ordering(a, b) when a > b, do: :gt
  defp ordering(_a, _b), do: :eq

  defp literal(1), do: :int_one
  defp literal(1.0), do: :float_one
  defp literal(_other), do: :other

  defp launder(value) do
    send(self(), value)

    receive do
      received -> received
    end
  end
end

M.go()
