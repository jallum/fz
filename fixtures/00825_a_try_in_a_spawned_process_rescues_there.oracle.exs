parent = self()
spawn(fn ->
  result = try do
    raise ArgumentError, "in child"
  rescue
    e in ArgumentError -> e.message
  end
  send(parent, {:done, result})
end)
receive do
  {:done, result} -> IO.inspect(result)
end
IO.inspect(:main_carried_on)
