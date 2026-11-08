defmodule Oracle do
  def run() do
    IO.inspect(Keyword.update([a: 1, b: 2], :a, 0, fn x -> x + 1 end))
    IO.inspect(Keyword.update([a: 1, b: 2], :b, 0, fn x -> x + 1 end))
    IO.inspect(Keyword.update([a: 1, b: 2], :z, 0, fn x -> x + 1 end))
    IO.inspect(Keyword.update([], :z, 0, fn x -> x + 1 end))
    IO.inspect(Keyword.update([a: 1, b: 2, a: 3], :a, 0, fn x -> x + 10 end))
    IO.inspect(Keyword.update!([a: 1, b: 2], :a, fn x -> x + 1 end))
    IO.inspect(Keyword.update!([b: 2, a: 1, c: 3, a: 4], :a, fn x -> x + 1 end))
    IO.inspect(Keyword.update!([a: 1, b: 2], :b, fn x -> x * 5 end))
  end
end

Oracle.run()
