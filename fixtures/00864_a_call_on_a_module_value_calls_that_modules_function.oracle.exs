defmodule Overdrawn do
  defstruct [:amount]

  def exception(attrs), do: {:overdrawn, attrs}
  def message(e), do: {:short_by, e.amount}
  def name(), do: :overdrawn
end

defmodule Bank.Frozen do
  def exception(attrs), do: {:frozen, attrs}
  def name(), do: :frozen
end

defmodule Oracle do
  def pick(m), do: m.exception([])

  def named(m, attrs), do: {m.name(), m.exception(attrs)}

  def note(v) do
    IO.inspect(v)
    v
  end

  def run() do
    IO.inspect(pick(Overdrawn))
    IO.inspect(pick(Bank.Frozen))
    IO.inspect(named(Bank.Frozen, [1, 2]))
    m = Overdrawn
    IO.inspect(m.name())
    e = %Overdrawn{amount: 7}
    IO.inspect(e.__struct__.message(e))
    IO.inspect(e.amount)
    held = %{first: Overdrawn, second: Bank.Frozen}
    IO.inspect(held.second.exception(:b))
    IO.inspect(note(Overdrawn).exception(note(:attrs)))
    callable = %{name: fn -> :a_field end}
    IO.inspect(callable.name.())
  end
end

Oracle.run()
