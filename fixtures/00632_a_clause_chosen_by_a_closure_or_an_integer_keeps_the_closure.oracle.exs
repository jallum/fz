defmodule Oracle do
  def kind(n) when is_integer(n), do: {:int, n}
  def kind(f) when is_function(f, 1), do: {:fn, f.(10)}

  def pick(flag, a, b) do
    case flag do
      true -> a
      _ -> b
    end
  end

  def run() do
    flag = :erlang.phash2(1) == :erlang.phash2(1)
    one = pick(flag, fn x -> x + 1 end, 5)
    two = pick(flag, fn x -> x + 2 end, 6)
    other = pick(not flag, fn x -> x + 3 end, 7)
    IO.inspect([kind(one), kind(two), kind(other)])
  end
end

Oracle.run()
