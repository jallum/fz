defmodule Defaults do
  defmacro defaults() do
    [
      quote do
        def message(x), do: "default #{x}"
      end,
      quote do
        defoverridable message: 1
      end
    ]
  end

  defmacro from_super(x) do
    quote do
      super(unquote(x))
    end
  end
end

defmodule Chain do
  def g(x), do: x + 1
  defoverridable g: 1
  def g(x), do: super(x) * 10
  defoverridable g: 1
  def g(x), do: super(x) + 1000
end

defmodule Mine do
  import Defaults
  defaults()
  def message(x), do: "mine, " <> super(x)
end

defmodule Written do
  import Defaults
  def g(x), do: x + 1
  defoverridable g: 1
  def g(x), do: from_super(x) * 2
end

defmodule Nested do
  def g(x), do: x + 1
  defoverridable g: 1
  def g(x), do: Enum.map([x, x + 1], fn y -> super(y) end)
end

defmodule Hidden do
  def g(x), do: {:default, x}
  defoverridable g: 1
  defp g(x), do: {:private, super(x)}
  def reach(x), do: g(x)
end

defmodule Recurse do
  def count(0), do: [:done]
  def count(n), do: [n | count(n - 1)]
  defoverridable count: 1
  def count(n), do: [:mine | super(n)]
end

defmodule Oracle do
  def run() do
    IO.inspect(Chain.g(1))
    IO.inspect(Mine.message(3))
    IO.inspect(Written.g(1))
    IO.inspect(Nested.g(1))
    IO.inspect(Hidden.reach(4))
    IO.inspect(Recurse.count(2))
  end
end

Oracle.run()
