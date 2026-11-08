result = try do
  try do
    :value
  rescue
    _ -> :inner_rescue
  else
    :value -> raise ArgumentError, "from else"
  after
    IO.inspect(:after)
  end
rescue
  e in ArgumentError -> e.message
end
IO.inspect(result)
