defmodule Oracle do
  def attempt(f) do
    try do
      f.()
    rescue
      [ArgumentError, RuntimeError] -> :listed
    end
  end
end

IO.inspect(Oracle.attempt(fn -> raise ArgumentError, "a" end))
IO.inspect(Oracle.attempt(fn -> raise "r" end))
IO.inspect(Oracle.attempt(fn -> :no_raise end))
