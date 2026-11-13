defmodule :my_atom_mod do
  def f(x), do: x + 1
  def me(), do: __MODULE__
end

IO.puts(:my_atom_mod.f(1))
inspect(:my_atom_mod) |> IO.puts()
inspect(:my_atom_mod.me()) |> IO.puts()
m = :my_atom_mod
IO.puts(m.f(41))
IO.puts(:my_atom_mod.me() == m)
