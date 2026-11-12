defmodule Pt do
  defstruct [:x, :y]
end

defmodule Oracle do
  def grow(v), do: %{v | z: 0}

  def run do
    m = Enum.into([a: 1], %{})
    try do
      %{m | b: 2}
    rescue
      e in KeyError -> IO.inspect(Exception.message(e))
    end
    try do
      %{m | a: 3, c: 4}
    rescue
      e in KeyError -> IO.inspect(Exception.message(e))
    end
    try do
      _ = %{m | d: 4}
      IO.inspect(:unreachable)
    rescue
      e in KeyError -> IO.inspect(Exception.message(e))
    end
    p = %Pt{x: 1, y: 2}
    try do
      grow(p)
    rescue
      e in KeyError -> IO.inspect(Exception.message(e))
    end
    try do
      %{p | __struct__: Pt, x: 3}
      |> IO.inspect()
    rescue
      e in KeyError -> IO.inspect(Exception.message(e))
    end
  end
end

Oracle.run()
