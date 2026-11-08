defmodule Oracle do
  def main() do
    %{} = m = %{a: 1}
    m2 = %{} = %{b: 2}
    {a, _} = {_, b} = {10, 20}
    [h | _] = [_, x | _] = l = [1, 2, 3]
    IO.inspect({Map.get(m, :a), Map.get(m2, :b), a, b, h, x, l})
  end
end

Oracle.main()
