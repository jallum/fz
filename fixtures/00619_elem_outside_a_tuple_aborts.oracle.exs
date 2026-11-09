value = hd([9])

try do
  elem({1}, value)
  raise "elem accepted a value outside its domain"
rescue
  ArgumentError -> :ok
end
