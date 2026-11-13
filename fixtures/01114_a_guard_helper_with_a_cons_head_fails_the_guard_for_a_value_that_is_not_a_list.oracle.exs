defmodule Oracle do
  defguardp first(l) when hd(l)

  def f(l) when first(l) > 0, do: :a
  def f(_), do: :b

  def run do
    IO.inspect([f([1]), f([]), f(7), f(:x)])
    IO.inspect([f([-1]), f(1.5), f({1, 2}), f("abc"), f(%{k: 1})])
  end
end

Oracle.run()
