defmodule Oracle do
  def main() do
    IO.inspect(Enum.to_list(1..100), width: :infinity)
    IO.inspect(Enum.to_list(1..101), width: :infinity)
    IO.inspect(Enum.map(1..101, fn n -> "e" <> inspect(n) end), width: :infinity)
    IO.inspect([Enum.to_list(1..60), Enum.to_list(1..60)], width: :infinity)
  end
end

Oracle.main()
