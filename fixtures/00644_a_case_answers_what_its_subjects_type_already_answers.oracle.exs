defmodule Oracle do
  def flip(a) do
    case a == 1 do
      true -> :was_one
      false -> :was_other
    end
  end

  def word(v) do
    case v do
      :a -> "first"
      :b -> "second"
    end
  end

  def run() do
    IO.inspect(Enum.map([1, 2, 1], fn a -> flip(a) end))
    IO.inspect(Enum.map([1, 2], fn a -> not (a == 1) end))
    IO.inspect(Enum.map(Enum.take([:a, :b, :c], 2), fn v -> word(v) end))
  end
end

Oracle.run()
