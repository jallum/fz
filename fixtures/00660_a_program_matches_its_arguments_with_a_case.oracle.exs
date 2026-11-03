defmodule Oracle do
  def describe(argv) do
    case argv do
      [path] -> {:path, path}
      [] -> :none
      _ -> :too_many
    end
  end

  def run() do
    IO.inspect(describe(System.argv()))
    IO.inspect(describe([]))
    IO.inspect(describe(["a", "b"]))
  end
end

Oracle.run()
