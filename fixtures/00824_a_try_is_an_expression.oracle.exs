IO.inspect(try do
  raise ArgumentError, "x"
rescue
  ArgumentError -> :rescued
end)
IO.inspect(try do
  :completed
rescue
  ArgumentError -> :rescued
end)
