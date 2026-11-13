defmodule Defaults do
  defmacro defaults() do
    [
      quote do
        def message(_e), do: "default"
      end,
      quote do
        defoverridable message: 1
      end
    ]
  end
end

defmodule Stands do
  def g(x), do: {:default, x}
  defoverridable g: 1
end

defmodule Replaced do
  def caller(x), do: g(x)
  def g(x), do: {:default, x}
  defoverridable g: 1
  def g(x), do: {:mine, x}
end

defmodule Hidden do
  def g(x), do: {:default, x}
  defoverridable g: 1
  defp g(x), do: {:private, x}
  def reach(x), do: g(x)
end

defmodule Plain do
  import Defaults
  defaults()
end

defmodule Mine do
  import Defaults
  defaults()
  def message(_e), do: "mine"
end

defmodule Oracle do
  def run() do
    IO.inspect(Stands.g(1))
    IO.inspect(Replaced.g(2))
    IO.inspect(Replaced.caller(3))
    IO.inspect(Hidden.reach(4))
    IO.inspect(Plain.message(5))
    IO.inspect(Mine.message(6))
  end
end

Oracle.run()
