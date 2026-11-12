defmodule Oracle do
  def run() do
    mapped = Stream.map([1, 2, 3], fn x -> x * 2 end)
    IO.inspect(Enum.count(mapped))
    IO.inspect(Enum.member?(mapped, 4))
    IO.inspect(Enum.member?(mapped, 3))
    IO.inspect(Enum.reduce(mapped, 0, fn x, acc -> x + acc end))

    path = "00774_enum.tmp"
    File.write!(path, "a\nbb\nccc\n")
    file = File.stream!(path)
    IO.inspect(Enum.count(file))
    IO.inspect(Enum.member?(file, "bb\n"))
    IO.inspect(Enum.member?(file, "bb"))
    IO.inspect(Enum.reduce(file, 0, fn line, acc -> byte_size(line) + acc end))
    File.rm!(path)
  end
end

Oracle.run()
