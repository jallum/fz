defmodule Reading do
  defstruct [:count, :ratio, :unit, :label, :tags, :inner]
end

defmodule Inner do
  defstruct [:depth]
end

defmodule Other do
  defstruct [:label, :count]
end

defmodule Oracle do
  def count_of(r), do: r.count
  def label_of(v), do: v.label
  def pick(0), do: %Other{label: "other", count: 7}
  def pick(n), do: %Reading{count: n, ratio: 0.5, unit: :cm, label: "picked", tags: [], inner: nil}

  def build(n) do
    %Reading{count: n, ratio: n / 4, unit: :mm, label: "built", tags: [n, n + 1], inner: %Inner{depth: n * 2}}
  end

  def run do
    literal = %Reading{count: 3, ratio: 1.5, unit: :m, label: "literal", tags: [:a], inner: %Inner{depth: 9}}
    IO.inspect(literal.count)
    IO.inspect(literal.ratio)
    IO.inspect(literal.unit)
    IO.inspect(literal.label)
    IO.inspect(literal.tags)
    IO.inspect(literal.inner)
    IO.inspect(literal.inner.depth)

    built = build(4)
    IO.inspect(built.count + 1)
    IO.inspect(built.ratio * 2)
    IO.inspect(built.unit == :mm)
    IO.inspect(built.label <> "!")
    IO.inspect(built.tags)
    IO.inspect(built.inner.depth)
    IO.inspect(count_of(built) + count_of(literal))

    IO.inspect(label_of(pick(0)))
    IO.inspect(label_of(pick(1)))
    IO.inspect(pick(0).count + pick(5).count)
    IO.inspect(Enum.map([build(1), build(2), literal], fn r -> r.count end))
  end
end

Oracle.run()
