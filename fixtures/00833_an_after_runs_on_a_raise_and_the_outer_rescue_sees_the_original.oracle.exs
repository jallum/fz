result = try do
  try do
    raise ArgumentError, "original"
  after
    IO.inspect(:after)
  end
rescue
  e in ArgumentError -> e.message
end
IO.inspect(result)
