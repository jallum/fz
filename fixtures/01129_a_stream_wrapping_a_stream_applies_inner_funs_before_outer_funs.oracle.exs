defmodule Trace do
  def say(label, x) do
    IO.puts("#{label} #{x}")
    x
  end
end

defmodule Oracle do
  def wrap(inner, fun), do: Stream.map(inner, fun)

  def main() do
    src = [1, 2, 3, 4, 5, 6]
    two = wrap(Stream.map(src, fn x -> Trace.say("inner", x + 1) end), fn x -> Trace.say("outer", x * 10) end)
    IO.inspect(Enum.to_list(two))
    swapped = wrap(Stream.map(src, fn x -> Trace.say("inner", x * 10) end), fn x -> Trace.say("outer", x + 1) end)
    IO.inspect(Enum.to_list(swapped))
    three = wrap(wrap(Stream.map(src, fn x -> Trace.say("a", x + 1) end), fn x -> Trace.say("b", x * 10) end), fn x -> Trace.say("c", x - 3) end)
    IO.inspect(Enum.to_list(three))
    IO.inspect(Enum.reduce(three, 0, fn x, acc -> acc + x end))
    IO.inspect(Enum.take(two, 2))
    IO.inspect(Enum.take(three, 1))
    IO.inspect(Enum.reduce_while(swapped, 0, fn x, acc -> if acc + x > 30, do: {:halt, acc}, else: {:cont, acc + x} end))
  end
end

Oracle.main()
