defmodule Oracle do
  def main() do
    bad = <<"a", 255, "e", 204, 129, 195>>
    IO.inspect(String.graphemes(bad))
    IO.inspect(String.length(bad))
    IO.inspect(String.next_grapheme_size(<<255, "a">>))
    IO.inspect(String.next_grapheme_size(<<"e", 204, 129, 195>>))
    IO.inspect(String.next_grapheme(<<195>>))
  end
end
Oracle.main()
