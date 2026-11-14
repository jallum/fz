defmodule Oracle do
  def run() do
    IO.inspect(Enum.map([4, :five], fn x ->
      case x do
        i when is_integer(i) -> :int
        f -> {:other, f}
      end
    end))
    IO.inspect(Enum.map([4, :five], fn x ->
      case x do
        i when is_integer(i) -> {:int, i}
        f when is_atom(f) -> {:atom, f}
      end
    end))
    IO.inspect(Enum.map([4, 2.5], fn x ->
      case x do
        i when is_integer(i) -> {:int, i}
        f -> {:float, f}
      end
    end))
    IO.inspect(Enum.map([4, :five], fn x ->
      case x do
        i when is_integer(i) -> {:int, i}
        _ -> {:other, x}
      end
    end))
    IO.inspect(Enum.map([4, :five], fn x ->
      y = case x do
        i when is_integer(i) -> i
        _ -> 0
      end
      {y, x}
    end))
  end
end

Oracle.run()
