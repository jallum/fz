defmodule Oracle do
  def make(n), do: {n, n + 1, n + 2, n + 3, n + 4, n + 5, n + 6, n + 7, n + 8, n + 9, n + 10, n + 11}

  def pair(n), do: {n, n * 2}

  def last({_, _, _, _, _, _, _, _, _, _, _, z}), do: z

  def sum({a, b, c, d, e, f, g, h, i, j, k, l}), do: a + b + c + d + e + f + g + h + i + j + k + l

  def run do
    t = make(7)
    IO.inspect(t)
    IO.inspect(tuple_size(t))
    IO.inspect(elem(t, 0))
    IO.inspect(elem(t, 11))
    IO.inspect(last(t))
    IO.inspect(sum(t))
    {a, _, _, _, _, _, _, _, _, _, _, l} = t
    IO.inspect(a + l)
    IO.inspect({pair(3), t, pair(4)})
  end
end

Oracle.run()
