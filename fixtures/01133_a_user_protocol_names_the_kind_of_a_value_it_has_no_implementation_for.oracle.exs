defprotocol Sizer do
  def size(value)
end

defimpl Sizer, for: Integer do
  def size(value), do: "an integer, #{value}"
end

defmodule Foo do
  defstruct [:a]
end

defmodule Oracle do
  def describe(value) do
    try do
      Sizer.size(value)
    rescue
      e -> Exception.message(e)
    end
  end

  def first_line(value) do
    [line | _] = String.split(describe(value), "\n")
    line
  end

  def main() do
    values = [7, 1.5, %Foo{a: 1}, :ok, [1, 2], {1, 2}, %{a: 1}, "text"]
    Enum.each(values, fn value -> IO.puts(describe(value)) end)
    Enum.each([7, fn -> 1 end, self(), make_ref()], fn value -> IO.puts(first_line(value)) end)
  end
end

Oracle.main()
