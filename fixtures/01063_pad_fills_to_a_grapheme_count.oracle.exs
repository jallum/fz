defmodule Oracle do
  defp at(x), do: Enum.at([x], 0)

  def main() do
    IO.inspect(String.pad_leading(at("abc"), 6))
    IO.inspect(String.pad_trailing(at("abc"), 6))
    IO.inspect(String.pad_leading(at("abc"), 6, "12"))
    IO.inspect(String.pad_trailing(at("abc"), 6, "12"))
    IO.inspect(String.pad_trailing(at("abc"), 6, at(["x", "yz"])))
    IO.inspect(String.pad_leading(at("abc"), 6, at(["x", "yz"])))
    IO.inspect(String.pad_trailing(at("héllo"), 3))
    IO.inspect(String.pad_leading(at("abc"), 3))
    IO.inspect(String.pad_leading(at("a longer string than the count"), 4))
    IO.inspect(String.pad_trailing(at("a longer string than the count"), 4, at(["x"])))
    IO.inspect(String.pad_leading(at("abc"), 0))
    IO.inspect(String.pad_trailing(at(""), 2, "ab"))
    IO.inspect(String.pad_trailing(at("é"), 3, "ë"))
    IO.inspect(String.pad_leading(at(<<101, 204, 129>>), 3, "-"))
    IO.inspect(String.pad_leading(at("x"), 4, at(<<101, 204, 129>>)))
    try do
      String.pad_leading(at("abc"), at(-1))
    rescue
      e -> IO.inspect({e.__struct__, Exception.message(e)}, width: :infinity)
    end
    try do
      String.pad_trailing(at("abc"), at(-1), "x")
    rescue
      e -> IO.inspect({e.__struct__, Exception.message(e)}, width: :infinity)
    end
    try do
      String.pad_leading(at("abc"), 5, at(""))
    rescue
      e -> IO.inspect({e.__struct__, Exception.message(e)}, width: :infinity)
    end
    try do
      String.pad_trailing(at("abc"), 5, at([]))
    rescue
      e -> IO.inspect({e.__struct__, Exception.message(e)}, width: :infinity)
    end
    try do
      String.pad_leading(at("a"), 3, at(["x", 1]))
    rescue
      e -> IO.inspect({e.__struct__, Exception.message(e)}, width: :infinity)
    end
    IO.inspect(String.pad_leading(at("a"), 2, at(["x", 1])))
  end
end

Oracle.main()
