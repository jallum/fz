defmodule Oracle do
  def main() do
    strings = ["abc", "é", "\r\n", "éx", "👨‍👩‍👧x", "🇫🇷🇫", "각x", "क्षx", "x́̂y"]
    Enum.each(strings, fn s -> IO.inspect(String.next_grapheme(s)) end)
    Enum.each(strings, fn s -> IO.inspect(String.next_grapheme_size(s)) end)
    IO.inspect(String.next_grapheme(""))
    IO.inspect(String.next_grapheme_size(""))
  end
end

Oracle.main()
