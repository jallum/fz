defmodule Oracle do
  def run() do
    IO.inspect(Integer.parse("5"))
    IO.inspect(Integer.parse("-5"))
    IO.inspect(Integer.parse("+5"))
    IO.inspect(Integer.parse("5x"))
    IO.inspect(Integer.parse("1_000"))
    IO.inspect(Integer.parse("007"))
    IO.inspect(Integer.parse("-0"))
    IO.inspect(Integer.parse("1.5"))
    IO.inspect(Integer.parse("0x1f"))
    IO.inspect(Integer.parse("12 34"))
    IO.inspect(Integer.parse(" 5"))
    IO.inspect(Integer.parse(""))
    IO.inspect(Integer.parse("-"))
    IO.inspect(Integer.parse("+"))
    IO.inspect(Integer.parse("+-5"))
    IO.inspect(Integer.parse("--5"))
    IO.inspect(Integer.parse("x5"))
    IO.inspect(Integer.parse("9223372036854775807"))
    IO.inspect(Integer.parse("-9223372036854775808"))
    IO.inspect(Integer.parse("9223372036854775807x"))
  end
end

Oracle.run()
