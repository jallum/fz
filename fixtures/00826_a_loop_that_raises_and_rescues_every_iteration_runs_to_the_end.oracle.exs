defmodule Oracle do
  def loop(0, acc), do: acc
  def loop(n, acc) do
    one = try do
      raise ArgumentError, "x"
    rescue
      ArgumentError -> 1
    end
    loop(n - 1, acc + one)
  end
end

IO.inspect(Oracle.loop(100_000, 0))
