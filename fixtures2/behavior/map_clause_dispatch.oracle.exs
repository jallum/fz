defmodule M do
  def go do
    IO.inspect(kind(%{tag: :a, value: 7}))
    IO.inspect(kind(%{tag: :b}))
    IO.inspect(kind(%{tag: :b, extra: 1}))
    IO.inspect(kind(%{other: 1}))
    IO.inspect(kind(%{}))
    IO.inspect(kind(42))
    IO.inspect(kind([1, 2]))

    IO.inspect(lookup(%{"name" => "ada", "age" => 36}))
    IO.inspect(lookup(%{"age" => 36}))

    IO.inspect(described(%{tag: :a, value: 9}))
    IO.inspect(described(%{value: 9}))
    IO.inspect(described(:not_a_map))
  end

  defp kind(%{tag: :a, value: v}), do: {:a, v}
  defp kind(%{tag: :b}), do: :b
  defp kind(%{}), do: :some_map
  defp kind(_other), do: :not_a_map

  defp lookup(%{"name" => name}), do: {:named, name}
  defp lookup(%{}), do: :anonymous

  defp described(subject) do
    case subject do
      %{tag: :a, value: v} -> {:case_a, v}
      %{value: v} -> {:case_value, v}
      %{} -> :case_map
      _other -> :case_other
    end
  end
end

M.go()
