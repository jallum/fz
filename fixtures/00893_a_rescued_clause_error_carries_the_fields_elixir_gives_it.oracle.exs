defmodule Shapes do
  def only_one(1), do: :one
end

defmodule Oracle do
  defp two(), do: 2
  defp word(), do: :maybe

  def run() do
    try do
      Shapes.only_one(two())
    rescue
      e in FunctionClauseError ->
        IO.inspect({e.module, e.function, e.arity})
        IO.inspect(Exception.message(e))
    end
    try do
      cond do
        two() == 1 -> :one
      end
    rescue
      e in CondClauseError -> IO.inspect(Exception.message(e))
    end
    try do
      word() and true
    rescue
      e in BadBooleanError ->
        IO.inspect({e.term, e.operator})
        IO.inspect(Exception.message(e))
    end
  end
end

Oracle.run()
