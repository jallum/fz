defmodule Twice do
  defmacro twice(x) do
    quote do: unquote(x) + unquote(x)
  end

  defmacro thrice(x) do
    quote do: unquote(x) * 3
  end
end

defmodule ImportsAll do
  import Twice

  def run(), do: {Twice.twice(4), twice(4)}
end

defmodule ImportsOne do
  import Twice, only: [twice: 1]

  def run(), do: {Twice.thrice(4), twice(4)}
end

IO.inspect(Kernel.apply(Kernel, :abs, [-2]))
IO.inspect(apply(Kernel, :abs, [-2]))
IO.inspect(Kernel.apply(Kernel, :+, [1, 2]))
IO.inspect(apply(Kernel, :+, [1, 2]))
IO.inspect(Kernel.&&(true, 3))
IO.inspect(true && 3)
IO.inspect(Kernel.&&(nil, 3))
IO.inspect(Kernel.||(nil, 3))
IO.inspect(nil || 3)
IO.inspect(Kernel.!(nil))
IO.inspect(!nil)
IO.inspect(ImportsAll.run())
IO.inspect(ImportsOne.run())
