defmodule Oracle do
  def main() do
    list = [1, 2, 3, 4, 5, 6]
    widened = for a <- list, rem(a, 2) == 0, into: MapSet.new(), do: a
    IO.inspect(Enum.map(list, fn a -> if(a in widened, do: "yes", else: "-") end))
  end
end

Oracle.main()
