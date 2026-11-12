defmodule Sample do
  defstruct [:count, :ratio, :unit, :big, :none, :items, :empty, :label, :inner, :pair, :table, :fixed, :other]
end

defmodule Inner do
  defstruct [:depth]
end

defmodule Oracle do
  def opaque(v), do: v

  def sample(n) do
    %Sample{
      count: n * 3,
      ratio: n / 8,
      unit: if(rem(n, 2) == 0, do: :even, else: :odd),
      big: n > 2,
      none: nil,
      items: [n, n + 1, n + 2],
      empty: [],
      label: "n" <> Integer.to_string(n),
      inner: %Inner{depth: n + 100},
      pair: {n, :pair, fn x -> x + n end},
      table: %{n => "value"},
      fixed: {:always, "same", [1, 2]},
      other: opaque(n * 7)
    }
  end

  def tuple(n) do
    {n * 3, n / 8, n > 2, nil, [n, n + 1], [], "t" <> Integer.to_string(n), %Inner{depth: n}, {n}, opaque([n])}
  end

  def churn(0, kept), do: kept

  def churn(n, kept) do
    made = sample(n)
    churn(n - 1, if(rem(n, 5000) == 0, do: [made | kept], else: kept))
  end

  def show(s) do
    IO.inspect(s.count)
    IO.inspect(s.ratio)
    IO.inspect(s.unit)
    IO.inspect(s.big)
    IO.inspect(s.none)
    IO.inspect(s.items)
    IO.inspect(s.empty)
    IO.inspect(s.label)
    IO.inspect(s.inner)
    {first, tag, step} = s.pair
    IO.inspect({first, tag})
    IO.inspect(step.(1000))
    IO.inspect(s.table)
    IO.inspect(s.fixed)
    IO.inspect(s.other)
  end

  def run do
    show(sample(1))
    show(sample(4))
    IO.inspect(tuple(1))
    IO.inspect(tuple(6))
    kept = churn(20000, [])
    IO.inspect(length(kept))
    Enum.each(kept, fn s -> show(s) end)
  end
end

Oracle.run()
