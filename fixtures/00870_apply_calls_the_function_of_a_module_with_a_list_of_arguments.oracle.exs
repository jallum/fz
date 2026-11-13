defmodule Overdrawn do
  def exception(attrs), do: {:overdrawn, attrs}
  def name(), do: :overdrawn
  def short_by(amount, fee), do: amount + fee
end

defmodule Frozen do
  def name(), do: :frozen
end

defmodule Oracle do
  def note(v) do
    IO.inspect(v)
    v
  end

  def name_of(m), do: apply(m, :name, [])

  def missed(m) do
    try do
      apply(m, :short_by, [1, 2])
    rescue
      e in UndefinedFunctionError -> {e.module, e.function, e.arity}
    end
  end

  def run() do
    IO.inspect(apply(Overdrawn, :exception, [[]]))
    IO.inspect(apply(Overdrawn, :short_by, [40, 2]))
    IO.inspect(name_of(Overdrawn))
    IO.inspect(name_of(Frozen))
    IO.inspect(name_of(String.to_atom("Elixir.Frozen")))
    IO.inspect(apply(note(Overdrawn), :short_by, [note(1), note(2)]))
    IO.inspect(apply(String, :upcase, ["abc"]))
    IO.inspect(missed(String.to_atom("Elixir.Frozen")))
    IO.inspect(missed(String.to_atom("nowhere")))
  end
end

Oracle.run()
