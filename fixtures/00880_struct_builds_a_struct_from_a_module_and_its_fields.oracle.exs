defmodule Pt do
  defstruct x: 0, y: 0
end

defmodule Named do
  defstruct [:name, kind: :plain]
end

defmodule Oracle do
  def message(f) do
    try do
      f.()
    rescue
      e in KeyError -> Exception.message(e)
    end
  end

  def pick(true), do: Pt
  def pick(false), do: Named

  def run() do
    IO.inspect(Pt.__struct__())
    IO.inspect(Named.__struct__())
    IO.inspect(struct(Pt))
    IO.inspect(struct(Pt, []))
    IO.inspect(struct(Pt, x: 1))
    IO.inspect(struct(Pt, x: 1, z: 9))
    IO.inspect(struct(Pt, %{y: 7}))
    IO.inspect(struct(%Pt{x: 5}, y: 6))
    IO.inspect(struct(%Pt{x: 5}, __struct__: Named, y: 6))
    IO.inspect(struct(Named, name: "a"))
    IO.inspect(struct(pick(true), x: 3))
    IO.inspect(struct(pick(false), name: "b", x: 3))
    IO.inspect(struct!(Pt, x: 1))
    IO.inspect(struct!(%Pt{x: 5}, y: 6))
    IO.inspect(struct!(%Pt{x: 5}, __struct__: Named, y: 6))
    IO.inspect(message(fn -> struct!(Pt, z: 9) end))
    IO.inspect(message(fn -> struct!(%Pt{}, z: 9) end))
    IO.inspect(Map.replace(Map.new(a: 1), :a, 2))
    IO.inspect(Map.replace(Map.new(a: 1), :b, 2))
    IO.inspect(Map.replace!(Map.new(a: 1), :a, 2))
    IO.inspect(message(fn -> Map.replace!(Map.new(a: 1), :b, 2) end))
  end
end

Oracle.run()
