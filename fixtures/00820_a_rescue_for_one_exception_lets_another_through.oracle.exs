defmodule Oracle do
  def attempt(f) do
    try do
      try do
        f.()
      rescue
        ArgumentError -> :argument
      end
    rescue
      RuntimeError -> :runtime_from_outer
    end
  end
end

IO.inspect(Oracle.attempt(fn -> raise ArgumentError, "x" end))
IO.inspect(Oracle.attempt(fn -> raise "x" end))
