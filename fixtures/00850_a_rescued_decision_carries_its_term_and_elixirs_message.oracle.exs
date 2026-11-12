defmodule Oracle do
  defp three(), do: Enum.at([3], 0)
  defp pair(), do: Enum.at([{1, 2}], 0)
  defp bad(), do: Enum.at([{:bad, 1}], 0)
  defp unexpected(), do: Enum.at([:unexpected], 0)

  def run() do
    try do
      case three() do
        1 -> :one
      end
    rescue
      e in CaseClauseError ->
        IO.inspect(e.term)
        IO.inspect(Exception.message(e))
    end
    try do
      {a} = pair()
      IO.inspect(a)
    rescue
      e in MatchError ->
        IO.inspect(e.term)
        IO.inspect(Exception.message(e))
    end
    try do
      with {:ok, v} <- bad() do
        IO.inspect(v)
      else
        :nothing -> :none
      end
    rescue
      e in WithClauseError ->
        IO.inspect(e.term)
        IO.inspect(Exception.message(e))
    end
    try do
      try do
        unexpected()
      rescue
        _ -> :inner_rescue
      else
        :expected -> :ok
      end
    rescue
      e in TryClauseError ->
        IO.inspect(e.term)
        IO.inspect(Exception.message(e))
    end
  end
end

Oracle.run()
