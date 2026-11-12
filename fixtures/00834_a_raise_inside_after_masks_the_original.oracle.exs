result = try do
  try do
    raise ArgumentError, "original"
  after
    raise RuntimeError, "from after"
  end
rescue
  e in ArgumentError -> {:argument, e.message}
  e in RuntimeError -> {:runtime, e.message}
end
IO.inspect(result)
