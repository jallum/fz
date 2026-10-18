value = hd([2])

try do
  Map.fetch!(%{1 => :a}, value)
  raise "Map.fetch! accepted a missing key"
rescue
  KeyError -> :ok
end
