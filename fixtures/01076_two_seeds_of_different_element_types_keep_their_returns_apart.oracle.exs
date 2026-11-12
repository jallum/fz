defmodule Oracle do
  def keep(x), do: x
  def go([], acc), do: keep(acc)
  def go([x | rest], acc), do: go(rest, [x | acc])

  def main() do
    IO.inspect(go([1, 2], [:a]))
    IO.inspect(go([1, 2], ["b"]))
  end
end

Oracle.main()
