defmodule Oracle do
  defp at(x), do: Enum.at([x], 0)

  def main() do
    IO.inspect(Tuple.to_list(at({})))
    IO.inspect(Tuple.to_list(at({:a, 1, "b"})))
    IO.inspect(Tuple.to_list(at({{1, 2}, {}, [3]})))
    IO.inspect(Tuple.to_list(at({1})))
    try do
      Tuple.to_list(at([1]))
    rescue
      e -> IO.inspect({e.__struct__, Exception.message(e)}, width: :infinity)
    end
    try do
      Tuple.to_list(at(:atom))
    rescue
      e -> IO.inspect({e.__struct__, Exception.message(e)}, width: :infinity)
    end
  end
end

Oracle.main()
