defmodule Shapes do
  def sides(:triangle), do: 3
  def sides(:square), do: 4
end

defmodule Oracle do
  defp two(), do: Enum.at([2], 0)
  defp pair(), do: Enum.at([{1, 2}], 0)
  defp bad(), do: Enum.at([{:bad, 1}], 0)

  def run() do
    try do
      case two() do
        1 -> :one
        3 -> :three
      end
    rescue
      e in [CaseClauseError, MatchError, FunctionClauseError, CondClauseError, WithClauseError] -> IO.inspect(e.__struct__)
    end
    IO.inspect(:after_case)
    try do
      {a} = pair()
      IO.inspect(a)
    rescue
      e in [CaseClauseError, MatchError, FunctionClauseError, CondClauseError, WithClauseError] -> IO.inspect(e.__struct__)
    end
    IO.inspect(:after_match)
    try do
      IO.inspect(Shapes.sides(String.to_atom("circle")))
    rescue
      e in [CaseClauseError, MatchError, FunctionClauseError, CondClauseError, WithClauseError] -> IO.inspect(e.__struct__)
    end
    IO.inspect(:after_function)
    try do
      x = two()
      cond do
        x == 1 -> :one
        x > 5 -> :many
      end
    rescue
      e in [CaseClauseError, MatchError, FunctionClauseError, CondClauseError, WithClauseError] -> IO.inspect(e.__struct__)
    end
    IO.inspect(:after_cond)
    try do
      with {:ok, v} <- bad() do
        v
      else
        :error -> :e
      end
    rescue
      e in [CaseClauseError, MatchError, FunctionClauseError, CondClauseError, WithClauseError] -> IO.inspect(e.__struct__)
    end
    IO.inspect(:after_with)
  end
end

Oracle.run()
