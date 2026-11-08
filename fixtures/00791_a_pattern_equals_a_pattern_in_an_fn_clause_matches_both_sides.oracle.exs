defmodule Oracle do
  def main() do
    f = fn %{} = m -> map_size(m) end
    g = fn {a, _} = {_, b} -> a + b end
    h = fn [h | _] = [_, x | _] = l -> {h, x, length(l)} end
    IO.inspect(f.(%{a: 1, b: 2}))
    IO.inspect(g.({3, 4}))
    IO.inspect(h.([7, 8, 9]))
  end
end

Oracle.main()
