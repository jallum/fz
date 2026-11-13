defmodule Oracle do
  def fns(k) do
    {fn x -> x + k end, fn x -> x * k end, fn x -> x - k end, fn x -> x + 1 end, fn x -> x + 2 end,
     fn x -> x + 3 end, fn x -> x + 4 end, fn x -> x + 5 end, fn x -> x + 6 end, fn _ -> k end}
  end

  def all({a, b, c, d, e, f, g, h, i, j}, x) do
    a.(x) + b.(x) + c.(x) + d.(x) + e.(x) + f.(x) + g.(x) + h.(x) + i.(x) + j.(x)
  end

  def run do
    t = fns(3)
    IO.inspect(all(t, 10))
    {_, mul, _, _, _, _, _, _, _, last} = t
    IO.inspect(mul.(5))
    IO.inspect(last.(5))
    IO.inspect(tuple_size(t))
    IO.inspect(elem(t, 2).(10))
  end
end

Oracle.run()
