defmodule M do
  def go do
    big = launder(9_007_199_254_740_993)
    smaller = launder(9_007_199_254_740_992)
    IO.inspect({big == smaller, big != smaller, big > smaller, smaller < big})

    one = launder(1)
    one_float = launder(1.0)

    IO.inspect({one == one_float, one != one_float, 1 == 1.0, 1.0 == 1, 2 == 1.0})

    IO.inspect(pinned_against(one, one_float))
    IO.inspect(pinned_against(one_float, one_float))
    IO.inspect(pinned_self(one))
    IO.inspect(pinned_origin_lists())

    IO.inspect({Enum.member?([1, 2, 3], 1.0), Enum.member?([1.0], 1), Enum.member?([1, 2, 3], 2)})
    IO.inspect({[1, 2, 3] -- [1.0], [1, 2, 3] -- [2]})

    IO.inspect({[1] == [1.0], {1} == {1.0}, %{a: 1} == %{a: 1.0}})
    IO.inspect({[1, [2]] == [1.0, [2.0]], {1, {2}} == {1.0, {2.0}}})

    IO.inspect({%{1 => :a} == %{1.0 => :a}, 1 == 1.5, [1] == [1.5]})
    IO.inspect({[1] == [1.0, 2.0], [1, 2] == [1.0], %{a: 1} == %{a: 1, b: 2}})

    IO.inspect({literal(one), literal(one_float), literal(launder(2))})

    IO.inspect({one === one_float, one !== one_float, one === launder(1), 1 === 1, 1.0 === 1.0})
    IO.inspect({[1] === [1.0], [1] === [1], {1} === {1.0}, %{a: 1} === %{a: 1.0}})
    IO.inspect({:a === :a, :a === :b, "x" === "x", "x" === "y"})

    negative_zero = 0.0 * (0 - 1.0)
    IO.inspect({0.0 == negative_zero, 0.0 === negative_zero, 0.0 !== negative_zero})

    IO.inspect({Enum.member?(1..5, 3), Enum.member?(1..5, 3.0)})

    IO.inspect(Enum.reverse([1, 2], 3..4))

    IO.inspect({Enum.member?(%{1 => :a}, {1, :a}), Enum.member?(%{1 => :a}, {1.0, :a})})
  end

  defp pinned_against(subject, pin) do
    case subject do
      ^pin -> :same
      _other -> :different
    end
  end

  defp pinned_self(value) do
    ^value = value
    value
  end

  defp pinned_origin_lists do
    first = [1, 2]
    second = [1, 2]
    ^first = second

    changed =
      case first do
        [head | _tail] -> [head | [9]]
        _other -> []
      end

    {changed, second}
  end

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
