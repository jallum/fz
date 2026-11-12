defmodule Main do
  def main() do
    fs = [fn x -> x + 1 end]
    IO.inspect(Enum.map(fs, fn f -> f.(5) end))
    mixed = [{:f, fn x -> x + 1 end}, {:v, 7}]
    IO.inspect(Enum.map(mixed, fn {k, m} -> if k == :f do m.(1) else m end end))
    IO.inspect(Enum.map(mixed, fn _ -> 0 end))
    floats = [{:f, fn x -> x + 1 end}, {:v, 7.5}]
    IO.inspect(Enum.map(floats, fn _ -> 0 end))
  end
end

Main.main()
