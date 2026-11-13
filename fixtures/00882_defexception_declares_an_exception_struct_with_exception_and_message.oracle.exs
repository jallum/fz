defmodule Plain do
  defexception [:message]
end

defmodule Defaulted do
  defexception message: "defaulted", code: 7
end

defmodule NotFound do
  defexception [:path]

  def message(e), do: "no file " <> e.path
end

defmodule Odd do
  defexception [:message, :n]

  def exception(n) when is_integer(n), do: %Odd{message: "odd", n: n}
end

defmodule Pt do
  defstruct [:x]
end

defmodule Oracle do
  def kind(e) when is_exception(e), do: :exception
  def kind(_), do: :other

  def rescued(f) do
    try do
      f.()
    rescue
      e in Plain -> {:plain, e.message}
      e in Defaulted -> {:defaulted, Exception.message(e), e.code}
    end
  end

  def raised_is_exception(f) do
    try do
      f.()
    rescue
      e -> is_exception(e)
    end
  end

  def run() do
    IO.inspect(Plain.exception("x"))
    IO.inspect(Plain.exception(message: "y"))
    IO.inspect(Plain.exception([]))
    IO.inspect(Defaulted.exception([]))
    IO.inspect(Defaulted.exception(code: 9))
    IO.inspect(Exception.message(Defaulted.exception([])))
    IO.inspect(Exception.message(NotFound.exception(path: "/a")))
    IO.inspect(Odd.exception(3))
    IO.inspect(Exception.message(Odd.exception(3)))
    IO.inspect(rescued(fn -> raise Plain, "x" end))
    IO.inspect(is_exception(Plain.exception("x")))
    IO.inspect(is_exception(%Pt{x: 1}))
    IO.inspect(is_exception(%{__struct__: Pt}))
    IO.inspect(is_exception(%{__exception__: true}))
    IO.inspect(is_exception(:atom))
    IO.inspect(kind(NotFound.exception(path: "/a")))
    IO.inspect(kind(%Pt{x: 1}))
    IO.inspect(raised_is_exception(fn -> raise Plain, "x" end))
    IO.inspect(raised_is_exception(fn -> raise ArgumentError, "bad" end))
  end
end

Oracle.run()
