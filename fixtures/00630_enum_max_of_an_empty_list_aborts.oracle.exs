value = hd([[]])

try do
  Enum.max(value)
  raise "Enum.max accepted an empty list"
rescue
  Enum.EmptyError -> :ok
end
