defmodule Oracle do
  def note(v) do
    IO.inspect(v)
    v
  end

  def keyed(k), do: %{k => note(:late), :b => note(:b), k => note(:later)}

  def run do
    m = %{d: note(4), b: note(2), a: note(1), b: note(20), c: note([3])}
    IO.inspect(m.a)
    IO.inspect(m.b)
    IO.inspect(m.c)
    IO.inspect(m.d)
    IO.inspect(map_size(m))
    IO.inspect(m == Map.put(Map.put(Map.put(Map.put(%{}, :a, 1), :b, 20), :c, [3]), :d, 4))
    IO.inspect(Enum.sort(Map.keys(%{zz: 1, z: 2, a: 3, aa: 4})))
    IO.inspect(%{y: 1.5, x: "s"})
    IO.inspect(%{only: {1, 2}})
    IO.inspect(%{})
    k = keyed(:a)
    IO.inspect(k.a)
    IO.inspect(k.b)
    IO.inspect(map_size(keyed(:b)))
  end
end

Oracle.run()
