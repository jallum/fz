defmodule Oracle do
  def attempt(f) do
    try do
      f.()
    rescue
      e in ArgumentError -> {:rescued, e.message}
    after
      IO.inspect(:after)
    end
  end
end

IO.inspect(Oracle.attempt(fn -> raise ArgumentError, "bad" end))
IO.inspect(Oracle.attempt(fn -> :fine end))
