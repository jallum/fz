defmodule Pt do
  defstruct [:x, :y]
end

defmodule Oracle do
  def put_all([], map), do: map
  def put_all([{key, value} | rest], map), do: put_all(rest, %{map | key => value})

  def missing(map) do
    try do
      put_all([z: 1], map)
    rescue
      e in KeyError -> Exception.message(%{e | term: nil})
    end
  end

  def run() do
    m = %{"b" => 2, c: 3}
    IO.inspect(%{m | :c => 10})
    IO.inspect(%{m | "b" => 20})
    IO.inspect(%{m | "b" => 20, c: 30})
    key = :c
    IO.inspect(%{m | key => 300})
    IO.inspect(put_all([{"b", 7}, {:c, 9}], m))
    IO.inspect(put_all([x: 1, y: 2], %Pt{}))
    IO.inspect(%{
      m
      | c: 5
    })
    IO.inspect(%{m |
      "b" => 6,
      c: 7
    })
    IO.inspect(missing(m))
  end
end

Oracle.run()
