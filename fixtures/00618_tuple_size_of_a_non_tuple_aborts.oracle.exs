value = hd([:x])

try do
  tuple_size(value)
  raise "tuple_size accepted a value outside its domain"
rescue
  ArgumentError -> :ok
end
