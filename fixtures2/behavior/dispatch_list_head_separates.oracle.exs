defmodule Heads do
  def kind(xs) when is_list(xs) do
    if Enum.all?(xs, &is_integer/1), do: 1, else: 2
  end

  def dnik(xs) when is_list(xs) do
    if Enum.all?(xs, &is_integer/1), do: 1, else: 2
  end

  def pick(n) do
    if n > 0 do
      [n, n]
    else
      [:ok, :err]
    end
  end
end

IO.inspect(Heads.kind(Heads.pick(1)))
IO.inspect(Heads.kind(Heads.pick(0)))
IO.inspect(Heads.dnik(Heads.pick(1)))
IO.inspect(Heads.dnik(Heads.pick(0)))

IO.inspect(Enum.all?([true, false]))
IO.inspect(Enum.all?([true, 1, :ok]))
IO.inspect(Enum.all?([1, 2]))
IO.inspect(Enum.all?([1, :ok]))
