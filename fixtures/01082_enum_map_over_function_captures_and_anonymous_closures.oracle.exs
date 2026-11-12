defmodule M do
  def id(x), do: x
  def inc(x), do: x + 1
  def go([]), do: []
  def go([h | t]), do: [h.(3) | go(t)]
end

defmodule Main do
def main() do
  IO.inspect(Enum.map([&M.id/1, &M.inc/1], fn h -> h.(3) end))
  IO.inspect(Enum.map([&M.id/1, &M.id/1, &M.id/1], fn h -> h.(3) end))
  IO.inspect(M.go([&M.id/1, &M.id/1]))
  fs = [fn x -> x end, fn x -> x end]
  IO.inspect(Enum.map(fs, fn h -> h.(3) end))
  IO.inspect(Enum.count([&M.id/1, &M.id/1]))
end
end
Main.main()
