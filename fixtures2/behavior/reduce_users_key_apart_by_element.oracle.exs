IO.inspect(Enum.reduce([1, 2], [], fn x, acc -> [x + 200 | acc] end))
IO.inspect(Enum.reduce(["a", "b"], [], fn x, acc -> [x <> "!" | acc] end))
