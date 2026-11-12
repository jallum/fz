result = try do
  try do
    raise ArgumentError, "inner"
  rescue
    e in ArgumentError -> "inner caught " <> e.message
  end
rescue
  e in ArgumentError -> "outer caught " <> e.message
end
IO.inspect(result)
