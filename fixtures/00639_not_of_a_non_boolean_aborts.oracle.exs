value = List.first([3])

try do
  not value
  raise "not accepted a non-boolean"
rescue
  ArgumentError -> :ok
end
