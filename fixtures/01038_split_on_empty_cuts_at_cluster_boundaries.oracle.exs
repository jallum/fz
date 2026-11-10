defmodule Oracle do
  def main() do
    strings = ["abc", "é", "\r\n", "éx", "👨‍👩‍👧x", "🇫🇷🇫", "각x", "क्षx", "x́̂y"]
    Enum.each(strings, fn s -> IO.inspect(String.split(s, "")) end)
  end
end

Oracle.main()
