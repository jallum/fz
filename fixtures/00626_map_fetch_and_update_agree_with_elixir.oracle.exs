defmodule Oracle do
  def run() do
    m = %{1 => "one", 2 => "two", 3 => nil}
    b = %{"x" => 10, "y" => 20}

    IO.inspect([Map.fetch(m, 1), Map.fetch(m, 3), Map.fetch(m, 4), Map.fetch(%{}, 1)])
    IO.inspect([Map.fetch(b, "y"), Map.fetch(b, "z")])
    IO.inspect([Map.fetch!(m, 2), Map.fetch!(m, 3), Map.fetch!(b, "x")])

    IO.inspect(Map.update!(b, "x", fn v -> v + 1 end))
    IO.inspect(Map.update!(m, 3, fn v -> {v, :seen} end))
    IO.inspect(Map.update!(%{1 => 1.5}, 1, fn v -> v * 2.0 end))

    IO.inspect(Map.new([1, 2, 3], fn n -> {n, n * n} end))
    IO.inspect(Map.new(["a", "b", "a"], fn s -> {s, byte_size(s)} end))
    IO.inspect(Map.new([], fn n -> {n, n} end))
    IO.inspect(Map.new(b, fn {k, v} -> {v, k} end))
    IO.inspect(Map.new(1..3, fn n -> {n, n + 1} end))

    IO.inspect([Map.get(m, 1, :d), Map.get(m, 3, :d), Map.get(m, 4, :d), Map.get(m, 4), Map.get(m, 3)])
  end
end

Oracle.run()
