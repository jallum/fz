defmodule Main do
  def one(f) when is_function(f, 1), do: :one
  def one(_), do: :other

  def either(f) when is_function(f, 1) or is_function(f, 2), do: :one_or_two
  def either(_), do: :other

  def pick(0), do: fn x -> x end
  def pick(1), do: fn x, y -> {x, y} end
  def pick(2), do: fn -> 0 end
  def pick(_), do: :not_a_function

  def next_of_two() do
    receive do
      f when is_function(f, 2) -> f.(1, 2)
    end
  end

  def main() do
    n = length(System.argv())
    picks = [n, n + 1, n + 2, n + 3]
    IO.inspect(Enum.map(picks, fn i -> one(pick(i)) end))
    IO.inspect(Enum.map(picks, fn i -> either(pick(i)) end))
    send(self(), fn x -> x end)
    send(self(), fn x, y -> {x, y} end)
    IO.inspect(next_of_two())
  end
end

Main.main()
