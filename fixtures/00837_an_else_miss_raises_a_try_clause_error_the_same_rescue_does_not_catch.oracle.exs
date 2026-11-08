result = try do
  try do
    :unexpected
  rescue
    _ -> :inner_rescue
  else
    :expected -> :ok
  end
rescue
  e in TryClauseError -> {:outer, e.term}
end
IO.inspect(result)
