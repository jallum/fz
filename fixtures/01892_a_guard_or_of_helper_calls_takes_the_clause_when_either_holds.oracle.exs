defmodule Main do
  defguardp number?(x) when is_integer(x) or is_float(x)
  defguardp text?(x) when is_binary(x) or is_atom(x)
  defguardp callable?(f) when is_function(f)

  def pick(x) when number?(x) or text?(x), do: {:scalar, x}
  def pick(x) when callable?(x) or is_list(x), do: :later
  def pick(_), do: :other

  def either(x, y) when number?(x) or number?(y), do: :one_number
  def either(_, _), do: :none

  def main() do
    IO.inspect(pick(1))
    IO.inspect(pick(2.5))
    IO.inspect(pick("s"))
    IO.inspect(pick(:a))
    IO.inspect(pick(fn -> :ok end))
    IO.inspect(pick([1]))
    IO.inspect(pick({1}))
    IO.inspect(either(1, :a))
    IO.inspect(either(:a, 2.5))
    IO.inspect(either(:a, :b))
  end
end

Main.main()
