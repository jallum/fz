defmodule Oracle do
  def pick(x) do
    v = if x > 0 do
      raise ArgumentError, "positive"
    else
      7
    end
    v + 1
  end
end

IO.inspect(Oracle.pick(0))
