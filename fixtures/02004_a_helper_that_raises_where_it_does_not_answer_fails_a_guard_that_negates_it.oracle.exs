defmodule Main do
  def kind(x) when not (abs(x) >= 0 and is_integer(x)), do: :not_int
  def kind(_), do: :other

  def main() do
    IO.inspect(Enum.map([1, 1.5, :z, "s"], &kind/1))
  end
end

Main.main()
