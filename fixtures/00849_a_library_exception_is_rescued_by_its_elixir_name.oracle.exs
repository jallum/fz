defmodule Oracle do
  defp zero(), do: Enum.at([0], 0)
  defp empty(), do: Enum.take([1], 0)
  defp atom(), do: String.to_atom("x")

  def run() do
    try do
      Map.fetch!(%{}, :k)
    rescue
      e in KeyError -> IO.inspect(e.__struct__)
    end
    try do
      div(1, zero())
    rescue
      e in ArithmeticError ->
        IO.inspect(e.__struct__)
        IO.inspect(e.message)
    end
    try do
      tuple_size(atom())
    rescue
      e in ArgumentError -> IO.inspect(e.__struct__)
    end
    try do
      Enum.max(empty())
    rescue
      e in Enum.EmptyError ->
        IO.inspect(e.__struct__)
        IO.inspect(e.message)
    end
    IO.inspect(:done)
  end
end

Oracle.run()
