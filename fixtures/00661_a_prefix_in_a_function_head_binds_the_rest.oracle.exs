defmodule Oracle do
  def option("--" <> rest), do: {:long, rest}
  def option("-" <> rest), do: {:short, rest}
  def option(_), do: :operand

  def everything("" <> rest), do: rest

  def chained("a" <> "b" <> rest), do: rest
  def chained(_), do: :no

  def whole("a" <> "b"), do: :ab
  def whole(_), do: :no

  def nothing_after("--" <> ""), do: :exactly_dashes
  def nothing_after(_), do: :no

  def utf8("é✓" <> rest), do: rest
  def utf8(_), do: :no

  def continued("--" <> <<c, rest::binary>>), do: {c, rest}
  def continued(_), do: :no

  def run() do
    IO.inspect(option("--verbose"))
    IO.inspect(option("-v"))
    IO.inspect(option("file"))
    IO.inspect(option("--"))
    IO.inspect(option(""))
    IO.inspect(option(7))
    IO.inspect(option(:atom))
    IO.inspect(everything("anything"))
    IO.inspect(everything(""))
    IO.inspect(chained("abc"))
    IO.inspect(chained("ab"))
    IO.inspect(chained("ba"))
    IO.inspect(whole("ab"))
    IO.inspect(whole("abcd"))
    IO.inspect(whole("bc"))
    IO.inspect(nothing_after("--"))
    IO.inspect(nothing_after("--x"))
    IO.inspect(utf8("é✓ok"))
    IO.inspect(utf8("e✓ok"))
    IO.inspect(continued("--xyz"))
    IO.inspect(continued("--"))
  end
end

Oracle.run()
