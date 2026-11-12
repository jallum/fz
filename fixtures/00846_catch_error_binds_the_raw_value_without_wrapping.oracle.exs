defmodule Oracle do
  def attempt(f) do
    try do
      f.()
    catch
      :error, value -> value
    end
  end
end

IO.inspect(Oracle.attempt(fn -> :erlang.error(:bare_reason) end))
IO.inspect(Oracle.attempt(fn -> raise ArgumentError, "bad" end).message)
IO.inspect(Oracle.attempt(fn -> raise ArgumentError, "bad" end).__struct__)
