defmodule Oracle do
  def fail(:error), do: raise(ArgumentError, "not that")
  def fail(:throw), do: throw({:found, 7})
  def fail(:exit), do: exit(:stopped)

  def caught(how) do
    try do
      fail(how)
    catch
      :error, %ArgumentError{message: message} -> {:argument, message}
      kind, value -> {kind, value}
    end
  end

  def run() do
    IO.inspect(caught(:error))
    IO.inspect(caught(:throw))
    IO.inspect(caught(:exit))
  end
end

Oracle.run()
