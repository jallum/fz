defmodule W do
  defstruct [:enum]
end

defimpl Enumerable, for: W do
  def reduce(%W{enum: enum}, acc, reducer), do: Enumerable.reduce(enum, acc, fn e, a -> reducer.(e, a) end)
  def count(_w), do: {:error, __MODULE__}
  def member?(_w, _value), do: {:error, __MODULE__}
  def slice(_w), do: {:error, __MODULE__}
end

defmodule P do
  def main() do
    %{"a" => v} = JSON.decode!("{\"a\": {\"b\": 1}}")
    x = Enum.reduce(v, 0, fn _e, acc -> acc + 1 end)
    y = Enum.reduce(v, %{}, fn e, acc -> Map.put(acc, :k, e) end)
    IO.inspect({x, y})
  end
end
P.main()
