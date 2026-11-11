defmodule Oracle do
  def main() do
    s = Enum.at(["héllo"], 0)
    IO.inspect(String.slice(s, 1, 3))
    IO.inspect(String.slice(s, 0, 5))
    IO.inspect(String.slice(s, 3, 100))
    IO.inspect(String.slice(s, -3, 2))
    IO.inspect(String.slice(s, -10, 2))
    IO.inspect(String.slice(s, 10, 2))
    IO.inspect(String.slice(s, 5, 2))
    IO.inspect(String.slice(s, 2, 0))
    IO.inspect(String.slice(Enum.at([""], 0), 0, 3))
    IO.inspect(String.slice(Enum.at([""], 0), -1, 3))
    accent = Enum.at([<<101, 204, 129, 120, 121>>], 0)
    IO.inspect(String.slice(accent, 0, 1))
    IO.inspect(String.slice(accent, 1, 1))
    IO.inspect(String.slice(accent, -2, 2))
    try do
      String.slice(s, 0, Enum.at([-1], 0))
    rescue
      e -> IO.inspect({e.__struct__, Exception.message(e)})
    end
  end
end

Oracle.main()
