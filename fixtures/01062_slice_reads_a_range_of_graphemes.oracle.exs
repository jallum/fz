defmodule Oracle do
  defp at(x), do: Enum.at([x], 0)

  def main() do
    s = at("héllo")
    IO.inspect(String.slice(s, 1..3))
    IO.inspect(String.slice(s, at(1)..at(-2)//1))
    IO.inspect(String.slice(s, -4..-2))
    IO.inspect(String.slice(s, at(-10)..2))
    IO.inspect(String.slice(s, 2..at(10)))
    IO.inspect(String.slice(s, 0..4//2))
    IO.inspect(String.slice(s, 0..at(-1)//2))
    IO.inspect(String.slice(s, 1..4//3))
    IO.inspect(String.slice(s, 3..1//1))
    IO.inspect(String.slice(s, at(10)..12))
    IO.inspect(String.slice(s, 0..at(-10)//1))
    IO.inspect(String.slice(at(""), 0..3))
    IO.inspect(String.slice(at(<<101, 204, 129, 120, 121>>), 0..1))
    try do
      String.slice(s, 0..2//at(-1))
    rescue
      e -> IO.inspect({e.__struct__, Exception.message(e)}, width: :infinity)
    end
    try do
      String.slice(s, 4..0//at(-2))
    rescue
      e -> IO.inspect({e.__struct__, Exception.message(e)}, width: :infinity)
    end
  end
end

Oracle.main()
