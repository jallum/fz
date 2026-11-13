defmodule Pt do
  defstruct [:x, :y]
end

defmodule Box do
  defstruct [:count, :ratio, :tag, :items]
end

defmodule Card do
  defstruct [:name, :corner, :pair, :extra]
end

defmodule Oracle do
  def retag(b, tag), do: %{b | tag: tag}

  def step(b, 0), do: b
  def step(b, n), do: step(%{b | count: b.count + n, items: [n | b.items]}, n - 1)

  def run do
    b = %Box{count: 1, ratio: 1.5, tag: :new, items: [1, 2]}
    IO.inspect(%{b | count: 2})
    IO.inspect(%{b | items: [3], count: 3})
    IO.inspect(%{b | count: 9, ratio: 9.5, tag: :all, items: []})
    IO.inspect(retag(b, :any))
    IO.inspect(retag(%{b | ratio: 0.5}, nil))
    IO.inspect(step(b, 5))
    IO.inspect(%{b | tag: :last}.__struct__)
    IO.inspect(b)
    c = %Card{name: "ace", corner: %Pt{x: 1, y: 2}, pair: {:a, 1}, extra: %{k: 1}}
    IO.inspect(%{c | name: "king"})
    IO.inspect(%{c | corner: %{c.corner | y: 20}, pair: {:b, 2}})
    IO.inspect(%{c | extra: %{j: 3}, name: ""})
    IO.inspect(%{c | name: "two", corner: %Pt{x: 9, y: 9}, pair: {}, extra: %{}})
    IO.inspect(c)
  end
end

Oracle.run()
