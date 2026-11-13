defmodule Pt do
  defstruct [:x, :y]
end

defmodule Oracle do
  def x_of(%Pt{} = p), do: p.x
  def x_of(_), do: :not_a_pt

  def moved(%Pt{} = p), do: %{p | x: p.x + 10}
  def moved(_), do: :not_a_pt

  def run do
    p = %Pt{x: 1, y: 2}
    grown = Map.put(p, :z, 3)
    IO.inspect(x_of(grown))
    IO.inspect(moved(grown).x)
    IO.inspect(Map.get(moved(grown), :z))
    IO.inspect(Map.get(moved(grown), :y))
    built = %{__struct__: Pt, x: 4, y: 5}
    IO.inspect(built.x)
    IO.inspect(x_of(built))
    IO.inspect(moved(built).x)
    IO.inspect(%{built | y: 50}.y)
    IO.inspect(x_of(%{x: 1, y: 2}))
    IO.inspect(moved(%{x: 1, y: 2}))
    IO.inspect(x_of(p))
    IO.inspect(moved(p))
    send(self(), grown)

    receive do
      %Pt{x: x} -> IO.inspect({:pt, x})
      _ -> IO.inspect(:other)
    end

    send(self(), %{x: 1, y: 2})

    receive do
      %Pt{x: x} -> IO.inspect({:pt, x})
      _ -> IO.inspect(:other)
    end
  end
end

Oracle.run()
