result = try do
  raise ArgumentError, "x"
rescue
  _ -> :from_rescue
else
  :from_rescue -> :wrongly_matched
  other -> {:else, other}
end
IO.inspect(result)
