defmodule Pt do
  defstruct [:x, :y]
end

defmodule Seg do
  defstruct [:a, :b]
end

defmodule Geo.Pt do
  defstruct [:lat, :lon]
end

defmodule Oracle do
  def run do
    IO.inspect(%Pt{x: 1, y: 2})
    IO.inspect(%Pt{y: 3})
    IO.inspect(%Seg{a: %Pt{x: 1, y: 2}, b: %Pt{y: 3}})
    IO.inspect([%Pt{x: 1, y: 2}, %Pt{x: 3, y: 4}])
    IO.inspect({%Pt{x: 1, y: 2}, :tag})
    IO.inspect(%Geo.Pt{lat: 1, lon: 2})
  end
end

Oracle.run()
