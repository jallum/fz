defmodule M do
  defmacro twice(x), do: quote(do: unquote(x) * 2)
  def f(), do: 7
end

defmodule N do
  require M
  def g(), do: M.twice(M.f())
end

IO.inspect(N.g())
