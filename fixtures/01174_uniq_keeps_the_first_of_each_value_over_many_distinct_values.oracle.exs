defmodule Oracle do
  def word(i), do: "job-" <> Integer.to_string(rem(i * 7919, 5_000))

  def run() do
    words = Enum.map(1..20_000, &word/1)
    firsts = Enum.uniq(words)
    IO.inspect({length(words), length(firsts)})
    IO.inspect({Enum.take(firsts, 4), Enum.take(firsts, -2)})
    IO.inspect(firsts == Enum.map(1..5_000, &word/1))

    by = Enum.uniq_by(1..20_000, fn i -> rem(i, 3_000) end)
    IO.inspect({length(by), Enum.take(by, 3), Enum.take(by, -3)})

    IO.inspect(Enum.uniq([1, 1.0, 1, 2, 2.0, 1.0, :a, "a", :a, {1, 2}, {1, 2}, {1, 2.0}, [1], [1], %{k: 1}, %{k: 1}, %{k: 1.0}]))
    IO.inspect(Enum.uniq_by([{1, :x}, {1.0, :y}, {1, :z}, {2, :w}], fn {k, _} -> k end))
    IO.inspect(Enum.uniq(Enum.map(1..100, fn i -> if rem(i, 2) == 0, do: i, else: i * 1.0 end)) |> length())
    IO.inspect({Enum.uniq([]), Enum.uniq(%{a: 1, b: 1}), Enum.uniq_by(%{a: 1, b: 1}, fn {_, v} -> v end)})
  end
end

Oracle.run()
