result = try do
  try do
    :fine
  after
    raise RuntimeError, "from after"
  end
rescue
  e in RuntimeError -> e.message
end
IO.inspect(result)
