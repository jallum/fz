defmodule M do
  def ml([], _), do: 0
  def ml([h | t], f), do: f.(h) + ml(t, f)
end
defmodule Main do
def main() do
  l = [fn x -> x end]
  IO.inspect(M.ml(l, fn h -> h.(3) end))
  IO.inspect(M.ml(l, fn h -> h.(4) end))
end
end
Main.main()
