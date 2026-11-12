result = try do
  try do
    raise ArgumentError, "first"
  rescue
    e in ArgumentError -> raise RuntimeError, "from rescue of " <> e.message
  end
rescue
  e in RuntimeError -> e.message
end
IO.inspect(result)
