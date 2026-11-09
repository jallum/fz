defmodule Oracle do
  def after_prefix(prefix, s) do
    case s do
      ^prefix <> rest -> {:ok, rest}
      _ -> :no
    end
  end

  def as_segment(prefix, s) do
    case s do
      <<^prefix::binary, rest::binary>> -> {:ok, rest}
      _ -> :no
    end
  end

  def between(first, last, s) do
    case s do
      ^first <> "-" <> ^last <> rest -> {:ok, rest}
      _ -> :no
    end
  end

  def closing(prefix, s) do
    case s do
      "x" <> ^prefix -> :closed
      _ -> :open
    end
  end

  def captured(prefix, s) do
    f = fn
      ^prefix <> rest -> {:ok, rest}
      _ -> :no
    end

    f.(s)
  end

  def matched(prefix, s) do
    ^prefix <> rest = s
    rest
  end

  def through_with(prefix, s) do
    with {:ok, ^prefix <> rest} <- {:ok, s} do
      {:ok, rest}
    else
      _ -> :no
    end
  end

  def run() do
    IO.inspect(after_prefix("ab", "abc"))
    IO.inspect(after_prefix("ab", "ab"))
    IO.inspect(after_prefix("ab", "a"))
    IO.inspect(after_prefix("ab", "xbc"))
    IO.inspect(after_prefix("", "abc"))
    IO.inspect(after_prefix("ab", :abc))
    IO.inspect(after_prefix("é✓", "é✓z"))
    IO.inspect(as_segment("ab", "abc"))
    IO.inspect(as_segment("ab", "a"))
    IO.inspect(as_segment("ab", "xbc"))
    IO.inspect(between("a", "b", "a-bz"))
    IO.inspect(between("a", "b", "a-cz"))
    IO.inspect(closing("yz", "xyz"))
    IO.inspect(closing("yz", "xyw"))
    IO.inspect(captured("ab", "abc"))
    IO.inspect(captured("ab", "xbc"))
    IO.inspect(matched("ab", "abc"))
    IO.inspect(through_with("ab", "abc"))
    IO.inspect(through_with("ab", "xbc"))
  end
end

Oracle.run()
