defmodule Oracle do
  def grown(n), do: Enum.reduce(1..n, %{}, fn i, m -> Map.put(m, i * 7, i) end)

  def bumped(m, n), do: Enum.reduce(1..n, m, fn i, acc -> %{acc | i * 7 => i + 1} end)

  def thinned(m, n), do: Enum.reduce(1..n, m, fn i, acc -> if rem(i, 2) == 1, do: Map.delete(acc, i * 7), else: acc end)

  def summary(m) do
    entries = Enum.sort(Map.to_list(m))
    {map_size(m), Enum.take(entries, 3), Enum.take(entries, -3), Enum.reduce(entries, 0, fn {k, v}, a -> a + k + v end)}
  end

  def word(i), do: "k" <> Integer.to_string(i)

  # fz prints a term on one line however long it is; Elixir wraps at 80 columns.
  def show(term), do: IO.inspect(term, width: :infinity)

  def main() do
    n = 10_000
    m = grown(n)
    show(summary(m))
    show({Map.get(m, 7), Map.get(m, 70_000), Map.get(m, 35_000), Map.get(m, 8), Map.get(m, 0)})

    up = bumped(m, n)
    show(summary(up))
    show({map_size(m), Map.get(m, 7), Map.get(up, 7)})

    half = thinned(up, n)
    show(summary(half))
    show({Map.has_key?(half, 7), Map.has_key?(half, 14), Map.has_key?(half, 69_993), Map.has_key?(half, 70_000)})
    show(Enum.all?(2..n//2, fn i -> Map.fetch(half, i * 7) == {:ok, i + 1} end))
    show(Enum.all?(1..n//2, fn i -> not Map.has_key?(half, i * 7) end))
    show(Map.delete(half, 7) == half)

    shrunk = Enum.reduce(Map.keys(half), half, fn k, acc -> if rem(div(k, 7), 4) == 0, do: acc, else: Map.delete(acc, k) end)
    show(summary(shrunk))
    show(Enum.reduce(1..40, shrunk, fn i, acc -> Map.put(acc, -i, i) end) |> map_size())

    words = Enum.reduce(1..2_000, %{}, fn i, acc -> Map.put(acc, word(i), i) end)
    show({map_size(words), Map.get(words, "k1"), Map.get(words, "k2000"), Map.get(words, "k2001")})
    fewer = Enum.reduce(1..1_990, words, fn i, acc -> Map.delete(acc, word(i)) end)
    show({map_size(fewer), Enum.sort(Map.to_list(fewer))})
  end
end

Oracle.main()
