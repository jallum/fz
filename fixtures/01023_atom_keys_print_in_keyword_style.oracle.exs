defmodule Oracle do
  def main() do
    IO.inspect(%{a: 1})
    IO.inspect(%{"foo bar": 1})
    IO.inspect(%{Foo => 1})
    IO.inspect(%{nil: 1})
    IO.inspect([a: 1])
    IO.inspect([a: 1, b: 2])
    IO.inspect(["foo bar": 1, b: 2])
    IO.inspect([{Foo, 1}])
    IO.inspect([{:a, 1}, {:b, 2}])
    IO.inspect([{:a, 1}, {1, 2}])
    IO.inspect([ok?: 1])
  end
end

Oracle.main()
