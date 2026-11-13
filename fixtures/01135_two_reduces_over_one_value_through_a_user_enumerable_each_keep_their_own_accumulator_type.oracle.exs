defmodule W do
  defstruct [:enum, :funs]

  def wrap(enum, fun), do: %W{enum: enum, funs: [fun]}

  def compose(funs, reducer), do: fn entry, acc -> reducer.(apply_funs(funs, entry), acc) end

  defp apply_funs([], entry), do: entry
  defp apply_funs([fun | earlier], entry), do: fun.(apply_funs(earlier, entry))
end

defimpl Enumerable, for: W do
  def reduce(%W{enum: enum, funs: funs}, acc, reducer), do: Enumerable.reduce(enum, acc, W.compose(funs, reducer))
  def count(_w), do: {:error, __MODULE__}
  def member?(_w, _value), do: {:error, __MODULE__}
  def slice(_w), do: {:error, __MODULE__}
end

defmodule P do
  def main() do
    items = Enum.to_list(W.wrap(["{\"a\": {\"b\": 1}}"], &JSON.decode!/1))
    [%{"a" => v} | _] = items
    x = Enum.reduce(v, 0, fn _e, acc -> acc + 1 end)
    y = Enum.reduce(v, %{}, fn e, acc -> Map.put(acc, :k, e) end)
    IO.inspect({x, y})
  end
end
P.main()
