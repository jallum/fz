defmodule M do
  def run(a, opts) do
    IO.inspect(a)
    [{k1, v1}, {k2, v2}] = opts
    IO.inspect(k1)
    IO.inspect(v1)
    IO.inspect(k2)
    IO.inspect(v2)
  end

  def only_opts(opts) do
    [{k, v}] = opts
    IO.inspect(k)
    IO.inspect(v)
  end
end

M.run(1, b: 2, c: 3)
M.only_opts(x: 9)
