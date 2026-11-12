defmodule Oracle do
  def run() do
    path = "00777_trace.tmp"
    File.write!(path, "{\"a\":1}\n[1,2]\n\"x\"\n")
    records = path |> File.stream!() |> Stream.map(&JSON.decode!/1) |> Enum.to_list()
    File.rm!(path)
    IO.inspect(records)
  end
end

Oracle.run()
