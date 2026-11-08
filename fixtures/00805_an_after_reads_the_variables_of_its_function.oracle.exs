defmodule Oracle do
  def attempt(label, f) do
    try do
      f.()
    rescue
      _ -> :rescued
    after
      IO.inspect({:after, label})
    end
  end
end

IO.inspect(Oracle.attempt(:one, fn -> :fine end))
IO.inspect(Oracle.attempt(:two, fn -> raise "x" end))
