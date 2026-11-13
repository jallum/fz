defmodule P do
  def main() do
    v = [1, 2, 3]
    a = Enum.reduce(v, [], fn e, acc ->
      case acc do
        [] -> [e]
        [h | _] -> [h + e | acc]
      end
    end)
    b = Enum.reduce(v, [], fn e, acc -> [{e, 6} | acc] end)
    IO.inspect({a, b})
  end
end
P.main()
