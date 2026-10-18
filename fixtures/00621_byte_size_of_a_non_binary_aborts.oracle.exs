value = hd([:x])

try do
  byte_size(value)
  raise "byte_size accepted a value outside its domain"
rescue
  ArgumentError -> :ok
end
