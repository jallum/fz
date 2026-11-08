defmodule Oracle do
  def lines_of(path, contents) do
    File.write!(path, contents)
    lines = Enum.to_list(File.stream!(path))
    File.rm!(path)
    lines
  end

  def run() do
    path = "00771_lines.tmp"
    IO.inspect(lines_of(path, "a\nb\n\nc"))
    IO.inspect(lines_of(path, "a\r\nb\n"))
    IO.inspect(lines_of(path, "a\r"))
    IO.inspect(lines_of(path, "a\r\r\n"))
    IO.inspect(lines_of(path, "a\rb\n"))
    IO.inspect(lines_of(path, ""))
    IO.inspect(lines_of(path, "x"))
  end
end

Oracle.run()
