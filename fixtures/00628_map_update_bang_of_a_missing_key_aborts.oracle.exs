value = hd([2])

try do
  Map.update!(%{1 => :a}, value, fn v -> v end)
  raise "Map.update! accepted a missing key"
rescue
  KeyError -> :ok
end
