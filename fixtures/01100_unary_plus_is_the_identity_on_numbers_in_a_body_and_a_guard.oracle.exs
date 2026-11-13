defmodule Oracle do
  def literal(), do: +3

  def body(n), do: +n

  def entry(n) when +n > 0, do: :a
  def entry(_), do: :b

  def receive_guard(m) do
    send(self(), m)

    receive do
      n when +n > 0 -> :a
      _ -> :b
    end
  end

  def raised(n) do
    try do
      +n
    rescue
      e in ArithmeticError -> e.message
    end
  end
end

IO.inspect([Oracle.literal(), Oracle.body(4), Oracle.body(-2.5), Oracle.body(0.0)])
IO.inspect([Oracle.entry(2), Oracle.entry(-2), Oracle.entry(1.5), Oracle.entry(:x)])
IO.inspect([Oracle.receive_guard(2), Oracle.receive_guard(-2), Oracle.receive_guard(1.5), Oracle.receive_guard(:x)])
IO.inspect(Oracle.raised("s"))
IO.inspect(Oracle.raised([1]))
