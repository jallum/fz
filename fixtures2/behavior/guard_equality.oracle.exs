same? = fn
  a, b when a == b -> :equal
  _a, _b -> :different
end

differs? = fn
  a, b when a != b -> :differs
  _a, _b -> :same
end

pick = fn
  1 -> :matched_int
  1.0 -> :matched_float
  _x -> :no_match
end

pinned = fn
  a, b when a == b -> :pinned_equal
  _a, _b -> :pinned_different
end

IO.inspect(same?.(1, 1.0))
IO.inspect(same?.(1, 1))
IO.inspect(same?.(1.0, 1))
IO.inspect(same?.(2, 1.0))
IO.inspect(same?.(:a, :a))
IO.inspect(same?.("x", "x"))
IO.inspect(same?.([1], [1.0]))

IO.inspect(1 == 1.0)
IO.inspect(1 === 1.0)
IO.inspect(2 == 1.0)
IO.inspect([1] == [1.0])

IO.inspect(differs?.(1, 1.0))
IO.inspect(differs?.(1, 2))

IO.inspect(pick.(1))
IO.inspect(pick.(1.0))
IO.inspect(pick.(2))

IO.inspect(pinned.(1, 1.0))
