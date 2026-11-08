result = try do
  raise ArgumentError, "bare"
rescue
  e -> e.message
end
IO.inspect(result)
