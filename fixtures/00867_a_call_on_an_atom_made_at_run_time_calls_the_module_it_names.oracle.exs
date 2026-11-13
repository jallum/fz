defmodule Circle do
  defstruct [:r]

  def area(c), do: 3 * c.r * c.r
  def sides(), do: 0
end

defmodule Square do
  defstruct [:s]

  def area(s), do: s.s * s.s
  def sides(), do: 4
end

defmodule Bank.Frozen do
  def sides(), do: :none
end

defmodule Oracle do
  def sides_of(name), do: String.to_atom(name).sides()

  def area_of(shape), do: shape.__struct__.area(shape)

  def run() do
    IO.inspect(sides_of("Elixir.Square"))
    IO.inspect(sides_of("Elixir.Circle"))
    IO.inspect(sides_of("Elixir.Bank.Frozen"))
    IO.inspect(area_of(%Circle{r: 2}))
    IO.inspect(area_of(%Square{s: 2}))
    IO.inspect(Enum.map(["Elixir.Circle", "Elixir.Square"], fn name -> String.to_atom(name).sides() end))
    m = String.to_atom("Elixir.Square")
    IO.inspect(m.area(%Square{s: 5}))
  end
end

Oracle.run()
