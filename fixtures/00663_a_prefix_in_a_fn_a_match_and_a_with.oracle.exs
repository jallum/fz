defmodule Oracle do
  def strip(s) do
    f = fn
      "--" <> rest -> {:long, rest}
      "-" <> rest -> {:short, rest}
      _ -> :operand
    end

    f.(s)
  end

  def matched(s) do
    "--" <> rest = s
    rest
  end

  def matched_chain(s) do
    "a" <> "b" <> rest = s
    rest
  end

  def through_with(s) do
    with "--" <> name <- s do
      {:option, name}
    else
      _ -> :operand
    end
  end

  def run() do
    IO.inspect(strip("--verbose"))
    IO.inspect(strip("-v"))
    IO.inspect(strip("file"))
    IO.inspect(strip(7))
    IO.inspect(matched("--verbose"))
    IO.inspect(matched("--"))
    IO.inspect(matched_chain("abc"))
    IO.inspect(through_with("--name"))
    IO.inspect(through_with("name"))
    IO.inspect(through_with(:name))
  end
end

Oracle.run()
