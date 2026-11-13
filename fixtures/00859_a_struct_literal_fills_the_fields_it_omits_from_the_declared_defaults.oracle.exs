defmodule Card do
  defstruct [:name, suit: :spades, rank: 1, ratio: 0.5, tags: [:a, :b]]
end

defmodule Conf do
  defstruct path: nil, modes: [:raw, :binary], label: "none", pair: {:ok, 1}
end

defmodule Nest do
  defstruct meta: %{k: [1, 2]}, flag: true, none: nil, empty: []
end

defmodule Oracle do
  def suit(%Card{suit: suit}), do: suit

  def run do
    IO.inspect(%Card{})
    IO.inspect(%Card{name: "ace", rank: 14})
    IO.inspect(%Card{tags: [], suit: :hearts})
    IO.inspect(suit(%Card{}))
    c = %Card{name: "two"}
    IO.inspect(%{c | ratio: 2.5})
    IO.inspect(c.tags)
    IO.inspect(%Conf{})
    IO.inspect(%Conf{path: "p", modes: []})
    IO.inspect(%Conf{}.label)
    IO.inspect(%Conf{}.pair)
    IO.inspect(%Nest{})
    IO.inspect(%Nest{meta: %{}})
    IO.inspect(%Nest{}.meta.k)
    IO.inspect(%Nest{} == %Nest{flag: true})
  end
end

Oracle.run()
