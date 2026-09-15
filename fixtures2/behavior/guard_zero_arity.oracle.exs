defmodule M do
  def go do
    IO.inspect(pick())
    IO.inspect(fallback())
  end

  defp pick() when 1 > 0, do: :guarded
  defp pick(), do: :plain

  defp fallback() when 1 > 2, do: :guarded
  defp fallback(), do: :plain
end

M.go()
