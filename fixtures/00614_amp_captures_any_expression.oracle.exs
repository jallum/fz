defmodule Twice do
  def double(x), do: x * 2
end

defmodule Capture do
  def inc(x), do: x + 1

  def run do
    maps = [%{inclusive: 1}, %{inclusive: 2}]

    IO.inspect(Enum.map(maps, & &1.inclusive))
    IO.inspect(Enum.map([1, 2, 3], & &1 + 1))
    IO.inspect(Enum.map([1, 2], &{&1, 10}))
    IO.inspect(Enum.map([1, 2], &[&1]))
    IO.inspect(Enum.map([1, 2], &"n=#{&1}"))
    IO.inspect(Enum.map([1, 2], &Twice.double/1))
    IO.inspect(Enum.map([1, 2], &inc/1))
    IO.inspect(Enum.reduce([1, 2, 3], 0, &+/2))
    IO.inspect(Enum.map([1, 2, 3], &(&1 * 2)))
    IO.inspect((&{&1, &2}).(:a, :b))
  end
end

Capture.run()
