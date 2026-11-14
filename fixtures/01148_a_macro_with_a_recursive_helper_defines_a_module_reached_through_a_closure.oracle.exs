defmodule M do
  defmacro mk(fields) do
    if flag?(fields) do
      quote do: defstruct([])
    else
      quote do: defstruct(unquote(fields))
    end
  end

  defp flag?([]), do: false
  defp flag?([:a | _]), do: true
  defp flag?([_ | rest]), do: flag?(rest)
end

defmodule Probe do
  import M
  mk [:a]
  def make(x), do: x
end

defmodule Lazy do
  def a(x), do: Enum.map(x, fn v -> Probe.make(v) end)
end

IO.inspect(Lazy.a([3, 1, 2]))

try do
  Map.fetch!(%{a: 1}, :b)
rescue
  _ in KeyError -> IO.puts("no :b")
end
