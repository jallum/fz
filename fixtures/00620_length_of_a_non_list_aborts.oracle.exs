value = hd([:x])

try do
  length(value)
  raise "length accepted a value outside its domain"
rescue
  ArgumentError -> :ok
end
