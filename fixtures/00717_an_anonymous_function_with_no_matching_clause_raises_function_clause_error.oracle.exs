defmodule Words do
  def name(n) do
    to_word = fn 1 -> :one end
    to_word.(n)
  end
end

defmodule Oracle do
  def run() do
    IO.inspect(Words.name(1))
    IO.inspect(Words.name(2))
  end
end

try do
  Oracle.run()
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
