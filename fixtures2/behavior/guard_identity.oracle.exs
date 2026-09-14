identical? = fn
  a, b when a === b -> :identical
  _a, _b -> :distinct
end

IO.inspect(identical?.(1, 1.0))
IO.inspect(identical?.(1, :atom))
IO.inspect(identical?.(2, 2))
IO.inspect(1 === 1.0)
