result = try do
  throw({:found, 42})
catch
  {:found, n} -> n
end
IO.inspect(result)
