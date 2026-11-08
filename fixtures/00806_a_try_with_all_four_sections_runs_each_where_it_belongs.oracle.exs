defmodule Oracle do
  def attempt(f) do
    try do
      f.()
    rescue
      _ -> :rescued
    else
      {:ok, n} -> n
      other -> {:else, other}
    after
      IO.inspect(:after)
    end
  end
end

IO.inspect(Oracle.attempt(fn -> {:ok, 5} end))
IO.inspect(Oracle.attempt(fn -> :other end))
IO.inspect(Oracle.attempt(fn -> raise "x" end))
