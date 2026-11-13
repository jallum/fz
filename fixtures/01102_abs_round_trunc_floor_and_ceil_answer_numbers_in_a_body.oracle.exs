defmodule Oracle do
  def refused(f) do
    try do
      f.()
    rescue
      e in ArgumentError -> e.message
    end
  end
end

IO.inspect([abs(-3), abs(3), abs(-2.5), abs(-0.0), abs(0.0), abs(-9223372036854775807)])
IO.inspect([round(2.5), round(-2.5), round(0.5), round(-0.5), round(2.4), round(-2.6), round(-0.0), round(7)])
IO.inspect([trunc(2.7), trunc(-2.7), trunc(-0.5), trunc(0.9), trunc(-0.0), trunc(7)])
IO.inspect([floor(2.5), floor(-2.5), floor(-0.0), floor(2.0), floor(-3), floor(7)])
IO.inspect([ceil(2.5), ceil(-2.5), ceil(-0.5), ceil(2.0), ceil(-3), ceil(7)])
IO.inspect([trunc(-9223372036854775808.0), floor(-9223372036854775808.0)])
IO.inspect([ceil(9223372036854774784.0), round(9223372036854774784.0)])
IO.inspect(Oracle.refused(fn -> abs("s") end))
IO.inspect(Oracle.refused(fn -> round("s") end))
IO.inspect(Oracle.refused(fn -> trunc([1]) end))
IO.inspect(Oracle.refused(fn -> floor("s") end))
IO.inspect(Oracle.refused(fn -> ceil("t") end))
