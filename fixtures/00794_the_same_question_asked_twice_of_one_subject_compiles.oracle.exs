defmodule Oracle do
  def same({_, _} = {_, _} = t), do: t

  def twice(t) do
    case t do
      {_, _} = {_, _} -> :pair
      _ -> :other
    end
  end

  def main() do
    IO.inspect(same({1, 2}))
    IO.inspect(twice({1, 2}))
    IO.inspect(twice(3))
  end
end

Oracle.main()
