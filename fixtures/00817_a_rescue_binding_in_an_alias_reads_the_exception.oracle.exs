result = try do
  raise ArgumentError, "the message"
rescue
  e in ArgumentError -> e.message
end
IO.inspect(result)
