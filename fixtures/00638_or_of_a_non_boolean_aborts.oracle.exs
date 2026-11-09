value = List.first([nil])

try do
  value or 5
  raise "or accepted a non-boolean"
rescue
  BadBooleanError -> :ok
end
