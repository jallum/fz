defmodule Oracle do
  def f() do
    IO.inspect({1, 2, 3, 4, 5, 6})
    {1, 2, 3, 4, 5, 6}
  end

  def main(), do: f()
end

Oracle.main()
