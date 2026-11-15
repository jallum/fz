defmodule Oracle do
  def show(f) do
    try do
      f.()
    rescue
      e -> [e.__struct__, Exception.message(e)]
    end
  end

  def all() do
    show(fn -> raise "plain text" end) ++
      show(fn -> raise ArgumentError end) ++
      show(fn -> raise ArgumentError, "with a text" end) ++
      show(fn -> raise KeyError, key: :a, term: [b: 1] end) ++
      show(fn -> raise(%KeyError{key: :c, term: 7}) end) ++
      show(fn -> raise RuntimeError, message: "by field" end) ++
      show(fn -> raise ArithmeticError end) ++
      show(fn -> raise(nominated(), "through a variable") end) ++
      show(fn -> raise(not_an_exception()) end) ++
      show(fn -> raise_missing(:d) end)
  end

  def not_an_exception(), do: 42

  def raise_missing(key), do: raise(KeyError, key: key)

  def nominated(), do: ArgumentError
  def run() do
    Enum.each(all(), fn r -> IO.inspect(r) end)
  end
end

Oracle.run()
