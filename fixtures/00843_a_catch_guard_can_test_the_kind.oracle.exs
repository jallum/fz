defmodule Oracle do
  def attempt(f) do
    try do
      f.()
    catch
      kind, value when kind == :throw and value > 100 -> {:big_throw, value}
      kind, value when kind == :throw -> {:throw, value}
      kind, value -> {:other, kind, value}
    end
  end
end

IO.inspect(Oracle.attempt(fn -> throw(500) end))
IO.inspect(Oracle.attempt(fn -> throw(5) end))
IO.inspect(Oracle.attempt(fn -> exit(:gone) end))
