defmodule P do
  defstruct [:x]
end

defmodule Q do
  defstruct [:x]
end

defmodule Main do
  def kind(v) when is_struct(v, P), do: :p
  def kind(v) when is_struct(v), do: :other_struct
  def kind(v) when is_map(v), do: :map
  def kind(_), do: :neither

  def case_kind(v) do
    case v do
      s when is_struct(s, Q) -> :q
      s when is_struct(s) -> :struct
      _ -> :no
    end
  end

  def guarded(v), do: match?({:ok, n} when n > 0, v)

  def main() do
    values = [%P{x: 1}, %Q{x: 1}, %{x: 1}, %{__struct__: "P"}, [x: 1], :a, 7]
    Enum.each(values, fn v ->
      IO.puts("#{is_struct(v)} #{is_struct(v, P)} #{is_struct(v, Q)}")
    end)
    Enum.each(values, fn v -> IO.puts("#{kind(v)} #{case_kind(v)}") end)

    x = 5
    IO.inspect(match?({:ok, _}, {:ok, 1}))
    IO.inspect(match?({:ok, _}, {:error, 1}))
    IO.inspect(match?([1, _ | _], [1, 2, 3]))
    IO.inspect(match?([_ | _], []))
    IO.inspect(match?(%P{}, %P{x: 1}))
    IO.inspect(match?(%P{}, %Q{x: 1}))
    IO.inspect(match?(%P{x: 2}, %P{x: 1}))
    IO.inspect(match?(%{x: 1}, %P{x: 1}))
    IO.inspect(match?(%{y: 1}, %{x: 1}))
    IO.inspect(match?({:ok, ^x}, {:ok, 5}))
    IO.inspect(match?({:ok, ^x}, {:ok, 6}))
    IO.inspect(Enum.map([{:ok, 1}, {:ok, -1}, {:ok, 0}, :error], &guarded/1))
    pairs = [{:a, 1}, {:b, 2}, {:a, 3}]
  IO.inspect(Enum.filter(pairs, fn t -> match?({:a, _}, t) end))
    IO.inspect(match?(y when is_integer(y), 3))
    IO.inspect(x)
  end

end

Main.main()
