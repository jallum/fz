defmodule Oracle do
  def run() do
    IO.inspect(Enum.to_list(Stream.map(Stream.map([1, 2, 3], fn x -> x + 1 end), fn x -> x * 10 end)))
    IO.inspect(Enum.to_list([1, 2, 3] |> Stream.map(fn x -> x - 1 end) |> Stream.map(fn x -> x * 7 end) |> Stream.map(fn x -> x + 1000 end)))

    path = "00773_compose.tmp"
    File.write!(path, "a\nb\n\nc")
    IO.inspect(path |> File.stream!() |> Stream.map(&String.trim/1) |> Stream.map(&String.upcase/1) |> Enum.to_list())
    File.rm!(path)
  end
end

Oracle.run()
