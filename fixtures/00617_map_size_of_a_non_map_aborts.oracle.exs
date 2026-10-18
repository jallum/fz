value = hd([:x])

try do
  map_size(value)
  raise "map_size accepted a value outside its domain"
rescue
  BadMapError -> :ok
end
