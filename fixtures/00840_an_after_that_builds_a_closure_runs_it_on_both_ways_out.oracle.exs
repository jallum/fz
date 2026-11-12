result = try do
  try do
    raise "x"
  after
    f = fn v -> IO.inspect({:raising, v}) end
    f.(1)
  end
rescue
  e -> e.message
end
IO.inspect(result)
try do
  :ok
after
  g = fn v -> IO.inspect({:completing, v}) end
  g.(2)
end
IO.inspect(:done)
