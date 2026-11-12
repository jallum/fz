defmodule Pt do
  defstruct [:x, :y]
  def name(), do: :top
end

defmodule Geo.Pt do
  def name(), do: :dotted
end

defmodule M do
  defmodule H.T do
    def me(), do: :nested
  end

  def via_first_segment(), do: H.T.me()
end

defmodule Oracle do
  def run() do
    pt = %Pt{x: 1, y: 2}
    IO.inspect(Pt.name())
    IO.inspect(pt.x)
    IO.inspect(Pt)
    IO.inspect(Geo.Pt)
    IO.inspect(M.via_first_segment())
    IO.inspect(M.H.T.me())
  end
end

Oracle.run()
