defmodule Oracle do
  def main() do
    h = Map.new(Enum.map(1..40, fn i -> {i, i * i} end))
    IO.inspect({map_size(h), Map.get(h, 1), Map.get(h, 40), Map.get(h, 41)})
    a = Map.new(Enum.map(0..39, fn i -> {String.to_atom("k#{i}"), i} end))
    b = Map.new(Enum.map(0..39, fn i -> {String.to_atom("k#{i}"), i} end))
    IO.inspect({map_size(a), map_size(b), a == b, Map.get(a, :k0), Map.get(b, :k39), Map.get(a, :k40)})
  end
end

Oracle.main()
