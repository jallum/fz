defmodule Oracle do
  def main() do
    IO.inspect([104, 105])
    IO.inspect([7, 104])
    IO.inspect([27])
    IO.inspect([10, 9])
    IO.inspect([34, 92])
    IO.inspect([35, 123])
    IO.inspect([32, 126])
    IO.inspect([])
    IO.inspect([0])
    IO.inspect([6])
    IO.inspect([14])
    IO.inspect([31])
    IO.inspect([127])
    IO.inspect([128])
    IO.inspect([233])
    IO.inspect([126, 127])
    IO.inspect([104, 105, 0])
    IO.inspect([[104, 105], 1])
    IO.inspect([104.0])
    IO.inspect([{104, 105}])
  end
end

Oracle.main()
