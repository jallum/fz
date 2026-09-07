defmodule M do
  def go do
    send(self(), 5)
    send(self(), 50)
    send(self(), 500)
    IO.inspect(classify())
    IO.inspect(classify())
    IO.inspect(classify())

    send(self(), {:count, 0})
    send(self(), {:count, 7})
    IO.inspect(counted())
    IO.inspect(counted())

    send(self(), :skip)
    send(self(), {:take, 1})
    IO.inspect(only_tuples())
    IO.inspect(anything())
  end

  defp classify() do
    receive do
      n when n < 10 -> {:small, n}
      n when n < 100 -> {:medium, n}
      n -> {:large, n}
    end
  end

  defp counted() do
    receive do
      {:count, n} when n > 0 -> {:positive, n}
      {:count, n} -> {:zero_or_less, n}
    end
  end

  defp only_tuples() do
    receive do
      {:take, n} -> {:took, n}
    end
  end

  defp anything() do
    receive do
      other -> {:leftover, other}
    end
  end
end

M.go()
