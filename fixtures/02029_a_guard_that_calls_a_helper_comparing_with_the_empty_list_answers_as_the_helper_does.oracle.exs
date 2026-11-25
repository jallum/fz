defmodule Main do
  defguardp empty?(c) when c === []

  def f(c) when empty?(c), do: :empty
  def f(c), do: {:set, c}

  def g(c) when empty?([]), do: {:always, c}

  def main(), do: IO.inspect({f([]), f(1), f([2]), g(3)})
end

Main.main()
