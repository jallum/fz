defmodule RetainedCellRekey do
  def head([value | _rest]), do: value
  def classify(value) when is_atom(value), do: {:atom, {:atom_payload, value}}
  def classify({value}), do: {:tuple, {:tuple_payload, {value}}}
  def build(0, values), do: classify(head(values))
  def build(n, values) do
    earlier = classify(head(values))
    {earlier, build(n - 1, [{:later} | values])}
  end
end

IO.inspect(RetainedCellRekey.build(1, [:seed]), limit: :infinity)
