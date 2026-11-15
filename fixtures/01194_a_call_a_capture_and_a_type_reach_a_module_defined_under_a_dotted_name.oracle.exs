defmodule Geo.Pt do
  @type t :: integer

  def name(), do: :dotted
  def twice(x), do: x * 2
  def short(), do: Pt
end

defmodule Use do
  @spec stretch(Geo.Pt.t) :: integer
  def stretch(x), do: Geo.Pt.twice(x)
end

defmodule Oracle do
  def run() do
    IO.inspect(Geo.Pt.name())
    twice = &Geo.Pt.twice/1
    IO.inspect(twice.(4))
    IO.inspect(Use.stretch(5))
    IO.inspect(Geo.Pt.short())
  end
end

Oracle.run()
