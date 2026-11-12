defmodule Oracle do
  defp kind(:int), do: 1
  defp kind(:text), do: "one"
  defp kind(_other), do: raise(ArgumentError, "unknown kind")

  defp guarded(tag) do
    try do
      kind(tag)
    rescue
      e in ArgumentError -> {:rescued, e.message}
    end
  end

  defp same(a, b) do
    try do
      a === b
    rescue
      _ -> :never
    end
  end

  def run() do
    IO.inspect(guarded(Enum.at([:int], 0)))
    IO.inspect(guarded(Enum.at([:text], 0)))
    IO.inspect(guarded(Enum.at([:other], 0)))
    IO.inspect(same(Enum.at([:a], 0), :a))
    IO.inspect(same(Enum.at([:a], 0), :b))
  end
end

Oracle.run()
