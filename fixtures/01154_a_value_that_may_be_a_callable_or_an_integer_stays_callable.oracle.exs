defmodule Choose do
  def pick(flag, a, b) do
    case flag do
      true -> a
      _ -> b
    end
  end

  def pick_ok(flag, a, b) do
    case flag do
      true -> {:ok, a}
      _ -> {:ok, b}
    end
  end

  def kind(n) when is_integer(n), do: {:int, n}
  def kind(f), do: {:fn, f.(10)}

  def via(x), do: kind(x)

  def kind_ok({:ok, n}) when is_integer(n), do: {:int, n}
  def kind_ok({:ok, f}), do: {:fn, f.(10)}
end

defmodule Oracle do
  def run() do
    IO.inspect(Enum.map([true, false], fn flag -> Choose.kind(Choose.pick(flag, fn x -> x + 1 end, 5)) end))
    IO.inspect(Enum.map([true, false], fn flag -> Choose.via(Choose.pick(flag, fn x -> x + 2 end, 6)) end))
    IO.inspect(Enum.map([true, false], fn flag -> Choose.kind_ok(Choose.pick_ok(flag, fn x -> x + 3 end, 7)) end))
    IO.inspect(Enum.map([true, false], fn flag -> Choose.kind_ok(Choose.pick_ok(not flag, fn x -> x + 4 end, 8)) end))
  end
end

Oracle.run()
