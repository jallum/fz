defmodule Oracle do
  def run() do
    path = "00775_take.tmp"
    File.write!(path, "one\ntwo\nthree\n")
    IO.inspect(Enum.take(File.stream!(path), 1))
    IO.inspect(Enum.take(File.stream!(path), 2))
    IO.inspect(Enum.take(Stream.map(File.stream!(path), fn line -> IO.inspect(line) end), 1))
    File.rm!(path)
  end
end

Oracle.run()
