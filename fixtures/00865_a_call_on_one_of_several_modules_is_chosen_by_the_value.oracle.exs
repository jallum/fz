defmodule Overdrawn do
  def exception(attrs), do: {:overdrawn, attrs}
  def scale(n), do: n * 2
  def count(_m, 0, acc), do: acc
  def count(m, n, acc), do: m.count(m, n - 1, acc + 1)
end

defmodule Frozen do
  def exception(attrs), do: {:frozen, attrs}
  def scale(n), do: n + 100
  def count(_m, 0, acc), do: acc
  def count(m, n, acc), do: m.count(m, n - 1, acc + 2)
end

defmodule Oracle do
  def choose(n) do
    if n > 1, do: Overdrawn, else: Frozen
  end

  def pick(m), do: m.exception([])

  def scaled(m, xs), do: Enum.map(xs, fn x -> m.scale(x) end)

  def run() do
    IO.inspect(pick(choose(1)))
    IO.inspect(pick(choose(2)))
    m = choose(2)
    IO.inspect(m.scale(5))
    IO.inspect(choose(0).scale(5))
    IO.inspect(Enum.map([Overdrawn, Frozen, Overdrawn], fn m -> m.exception(:each) end))
    IO.inspect(scaled(choose(1), [1, 2]))
    IO.inspect(scaled(choose(2), [1, 2]))
    IO.inspect(choose(1).count(choose(1), 4, 0))
    IO.inspect(choose(2).count(choose(1), 4, 0))
    IO.inspect(choose(2).count(choose(2), 1000, 0))
  end
end

Oracle.run()
