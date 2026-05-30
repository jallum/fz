defmodule M do
  def run(a, opts) do
    IO.inspect(a)
    [{k, v}] = opts
    IO.inspect(k)
    IO.inspect(v)
  end

  def only_block(opts) do
    [{k, v}] = opts
    IO.inspect(k)
    IO.inspect(v)
  end
end

M.run 1 do
  2
end

M.only_block do
  42
end
