a = try do
  {:ok, 1}
rescue
  _ -> :rescued
else
  {:ok, n} -> {:got, n}
  other -> other
end
b = try do
  :plain
rescue
  _ -> :rescued
else
  {:ok, n} -> {:got, n}
  other -> {:other, other}
end
IO.inspect(a)
IO.inspect(b)
