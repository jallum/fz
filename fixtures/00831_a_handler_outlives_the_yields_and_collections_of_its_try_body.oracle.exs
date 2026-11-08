defmodule Oracle do
  def fill(0, _acc), do: raise ArgumentError, "full"
  def fill(n, acc), do: fill(n - 1, [n | acc])

  def round(0, acc), do: acc
  def round(n, acc) do
    got = try do
      fill(2_000, [])
    rescue
      e in ArgumentError -> e.message
    end
    round(n - 1, acc + byte_size(got))
  end
end

IO.inspect(Oracle.round(100, 0))
