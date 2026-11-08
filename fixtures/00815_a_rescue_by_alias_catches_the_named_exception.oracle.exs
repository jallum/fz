result = try do
  raise "boom"
rescue
  RuntimeError -> :rescued
end
IO.inspect(result)
