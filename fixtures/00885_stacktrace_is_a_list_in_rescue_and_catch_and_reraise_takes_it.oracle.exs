rescued = try do
  raise ArgumentError, "first"
rescue
  e in ArgumentError -> {e.message, is_list(__STACKTRACE__)}
end
IO.inspect(rescued)

caught = try do
  throw(:ball)
catch
  :throw, value -> {value, is_list(__STACKTRACE__)}
end
IO.inspect(caught)

in_a_closure = try do
  raise ArgumentError, "second"
rescue
  _ ->
    read = fn -> is_list(__STACKTRACE__) end
    read.()
end
IO.inspect(in_a_closure)

outer = try do
  try do
    raise ArgumentError, "third"
  rescue
    e in ArgumentError -> reraise e, __STACKTRACE__
  end
rescue
  e in ArgumentError -> {:outer_saw, e.message}
end
IO.inspect(outer)
