defprotocol Sizer do
  def size(value)
end

defimpl Sizer, for: Integer do
  def size(_value), do: 1
end

defmodule Oracle do
  def describe(value), do: Sizer.size(value)

  def run() do
    case [7, 1.0] do
      [a, b] ->
        IO.puts(describe(a))
        IO.puts(describe(b))
      _ -> 0
    end
  end
end

try do
  Oracle.run()
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
