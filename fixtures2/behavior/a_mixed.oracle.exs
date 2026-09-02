double = fn x -> IO.inspect(x * 2) end
Enum.each([1, 2], double)

send(self(), double)
boxed = receive do f -> f end
Enum.each([3, 4], boxed)
IO.inspect(:done)
