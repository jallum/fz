result = try do
  try do
    raise ArgumentError, "original"
  rescue
    e in ArgumentError ->
      IO.inspect(:inner_saw)
      reraise e, []
  end
rescue
  e in ArgumentError -> {:outer_saw, e.message}
end
IO.inspect(result)
