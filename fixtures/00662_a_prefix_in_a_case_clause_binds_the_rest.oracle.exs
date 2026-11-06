defmodule Oracle do
  def option(s) do
    case s do
      "--" <> rest -> {:long, rest}
      "-" <> rest -> {:short, rest}
      _ -> :operand
    end
  end

  def guarded(s) do
    case s do
      "--" <> rest when rest != "" -> {:long, rest}
      "--" <> _ -> :bare_dashes
      _ -> :operand
    end
  end

  def nested(pair) do
    case pair do
      {:ok, "id:" <> id} -> {:id, id}
      {:ok, other} -> {:other, other}
      {:error, "e:" <> reason} -> {:error, reason}
      _ -> :unknown
    end
  end

  def whole_literals(s) do
    case s do
      "a" <> "b" -> :ab
      "a" <> "bc" -> :abc
      _ -> :no
    end
  end

  def chained(s) do
    case s do
      "a" <> "b" <> rest -> rest
      _ -> :no
    end
  end

  def utf8(s) do
    case s do
      "é✓" <> rest -> rest
      _ -> :no
    end
  end

  def empty_prefix(s) do
    case s do
      "" <> rest -> rest
    end
  end

  def run() do
    IO.inspect(option("--verbose"))
    IO.inspect(option("-v"))
    IO.inspect(option("file"))
    IO.inspect(option(7))
    IO.inspect(guarded("--x"))
    IO.inspect(guarded("--"))
    IO.inspect(guarded("x"))
    IO.inspect(nested({:ok, "id:42"}))
    IO.inspect(nested({:ok, "name"}))
    IO.inspect(nested({:error, "e:boom"}))
    IO.inspect(nested({:error, "boom"}))
    IO.inspect(nested(:nope))
    IO.inspect(whole_literals("ab"))
    IO.inspect(whole_literals("abc"))
    IO.inspect(whole_literals("abcd"))
    IO.inspect(whole_literals("a"))
    IO.inspect(whole_literals(:ab))
    IO.inspect(chained("abz"))
    IO.inspect(chained("a"))
    IO.inspect(utf8("é✓!"))
    IO.inspect(utf8("é"))
    IO.inspect(empty_prefix("anything"))
    IO.inspect(empty_prefix(""))
  end
end

Oracle.run()
