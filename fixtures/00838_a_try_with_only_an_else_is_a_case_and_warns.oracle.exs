result = try do
  {:ok, 1}
else
  {:ok, n} -> n
end
IO.inspect(result)
