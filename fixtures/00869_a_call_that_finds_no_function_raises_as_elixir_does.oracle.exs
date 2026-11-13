defmodule Square do
  defstruct [:s]

  def area(s), do: s.s * s.s
end

defmodule Circle do
  def name(), do: "circle"
end

defmodule Oracle do
  def try_area(m) do
    try do
      m.area(%Square{s: 3})
    rescue
      e -> {e.__struct__, Exception.message(e)}
    end
  end

  def try_name(m) do
    try do
      m.name()
    rescue
      e -> {e.__struct__, Exception.message(e)}
    end
  end

  def missed(m) do
    try do
      m.area(1)
    rescue
      e in UndefinedFunctionError -> {e.module, e.function, e.arity, e.reason}
    end
  end

  # The name and the message go out on lines of their own, so no line is long
  # enough to be wrapped.
  def show({name, message}) do
    IO.inspect(name)
    IO.puts(message)
  end

  def show(value), do: IO.inspect(value)

  def opaque(x), do: Enum.at([x, String.to_atom("a")], 0)

  def run() do
    show(try_area(String.to_atom("Elixir.Square")))
    show(try_area(String.to_atom("nowhere")))
    show(try_area(String.to_atom("Elixir.Nowhere.Deep")))
    show(try_area(String.to_atom("Elixir.Circle")))
    show(try_area(opaque(nil)))
    show(try_area(opaque(true)))
    show(try_area(opaque(1)))
    show(try_area(opaque("str")))
    show(try_area(opaque({Square, 1})))
    show(try_area(opaque([Square])))
    show(try_name(String.to_atom("Elixir.Circle")))
    show(try_name(String.to_atom("Elixir.Square")))
    show(try_name(opaque(1)))
    IO.inspect(missed(String.to_atom("nowhere")))
    IO.inspect(missed(String.to_atom("Elixir.Circle")))
  end
end

Oracle.run()
